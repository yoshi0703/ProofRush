import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CanonneQuantile

open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The ordinate is the square root of the overlap budget. At a positive
fixed point, dividing the profile by the ordinate gives the tail criterion. -/
def tail (q : ι → ℝ) (n y : ℝ) : ℝ :=
  ∑ i, n * q i * Real.sqrt (q i) / max 1 (n * y * Real.sqrt (q i))

theorem tail_continuous (q : ι → ℝ) (n : ℝ) : Continuous (tail q n) := by
  unfold tail
  apply continuous_finsetSum
  intro i _
  have hden : Continuous (fun y : ℝ => max (1 : ℝ) (n * y * Real.sqrt (q i))) :=
    continuous_const.max ((continuous_const.mul continuous_id).mul continuous_const)
  exact Continuous.div (f := fun _ : ℝ => n*q i*Real.sqrt (q i))
    (g := fun y : ℝ => max 1 (n*y*Real.sqrt (q i))) continuous_const hden
    (fun y => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem tail_antitone (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) {n : ℝ} (hn : 0 ≤ n) :
    Antitone (tail q n) := by
  intro y z hyz
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (by positivity [hq i])
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (max_le_max_left 1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyz hn)
      (Real.sqrt_nonneg _)))

theorem exists_unique_tail_root (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) {n : ℝ} (hn : 0 ≤ n) :
    ∃! y : ℝ, 0 ≤ y ∧ tail q n y = y := by
  let b := tail q n 0
  have hb : 0 ≤ b := by
    dsimp [b, tail]
    apply Finset.sum_nonneg
    intro i _
    positivity [hq i]
  have hdec := tail_antitone q hq hn
  let f := fun y : ℝ => tail q n y - y
  have hf : Continuous f := (tail_continuous q n).sub continuous_id
  have hzero : 0 ∈ Set.Icc (f b) (f 0) := by
    constructor
    · exact sub_nonpos.mpr (hdec hb)
    · simpa [f, b] using hb
  obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' hb hf.continuousOn hzero
  have heq : tail q n y = y := sub_eq_zero.mp hfy
  refine ⟨y, ⟨hy.1, heq⟩, ?_⟩
  intro z hz
  rcases le_total z y with h | h
  · have h' := hdec h
    linarith [hz.2, heq]
  · have h' := hdec h
    linarith [hz.2, heq]

noncomputable def root (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (n : ℝ) (hn : 0 ≤ n) : ℝ :=
  (exists_unique_tail_root q hq hn).exists.choose

theorem root_spec (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ root q hq n hn ∧ tail q n (root q hq n hn) = root q hq n hn :=
  (exists_unique_tail_root q hq hn).exists.choose_spec

theorem tail_eq_clipped (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) {n y : ℝ} (_hn : 0 ≤ n)
    (hy : 0 < y) :
    tail q n y = ∑ i, min (q i / y) (n * q i * Real.sqrt (q i)) := by
  apply Finset.sum_congr rfl
  intro i _
  have hs := Real.sqrt_nonneg (q i)
  by_cases h : n * y * Real.sqrt (q i) ≤ 1
  · rw [max_eq_left h, div_one, min_eq_right]
    apply (le_div_iff₀ hy).mpr
    calc
      _ = (n*y*Real.sqrt (q i)) * q i := by ring
      _ ≤ 1 * q i := mul_le_mul_of_nonneg_right h (hq i)
      _ = _ := one_mul _
  · have ht : 0 < n*y*Real.sqrt (q i) := lt_trans zero_lt_one (lt_of_not_ge h)
    rw [max_eq_right (le_of_not_ge h), min_eq_left]
    · apply (div_eq_div_iff ht.ne' hy.ne').mpr
      ring
    · apply (div_le_iff₀ hy).mpr
      calc
        _ = 1 * q i := (one_mul _).symm
        _ ≤ (n*y*Real.sqrt (q i)) * q i := mul_le_mul_of_nonneg_right (le_of_not_ge h) (hq i)
        _ = _ := by ring

theorem root_mono (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) {n m : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m) :
    root q hq n hn ≤ root q hq m (hn.trans hnm) := by
  let x := root q hq n hn
  let y := root q hq m (hn.trans hnm)
  obtain ⟨hx, hfx⟩ := root_spec q hq hn
  obtain ⟨hy, hfy⟩ := root_spec q hq (hn.trans hnm)
  by_contra! h
  have hxpos : 0 < x := lt_of_le_of_lt hy h
  have hxy : tail q n x ≤ tail q m x := by
    rw [tail_eq_clipped q hq hn hxpos, tail_eq_clipped q hq (hn.trans hnm) hxpos]
    apply Finset.sum_le_sum
    intro i _
    exact min_le_min_left _ (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnm (hq i)) (Real.sqrt_nonneg _))
  have hyx := tail_antitone q hq (hn.trans hnm) h.le
  change tail q m x ≤ tail q m y at hyx
  change tail q n x = x at hfx
  change tail q m y = y at hfy
  linarith

theorem root_unsaturated_dilation (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n M : ℝ} (hn : 0 ≤ n) (hM : 1 ≤ M)
    (hlight : ∀ i, M^2 * n * root q hq n hn * Real.sqrt (q i) ≤ 1) :
    root q hq (M*n) (mul_nonneg (by linarith) hn) = M * root q hq n hn := by
  let y := root q hq n hn
  obtain ⟨hy, hfy⟩ := root_spec q hq hn
  have hM0 : 0 ≤ M := by linarith
  have htr (i : ι) : n*y*Real.sqrt (q i) ≤ 1 := by
    have hv : 0 ≤ n*y*Real.sqrt (q i) := mul_nonneg (mul_nonneg hn hy) (Real.sqrt_nonneg _)
    have hsq : 1 ≤ M^2 := by nlinarith [sq_nonneg (M-1)]
    calc
      _ ≤ M^2 * (n*y*Real.sqrt (q i)) := le_mul_of_one_le_left hv hsq
      _ = _ := by ring
      _ ≤ 1 := hlight i
  have eq : tail q (M*n) (M*y) = M * tail q n y := by
    unfold tail
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hat : M*n*(M*y)*Real.sqrt (q i) ≤ 1 := by
      calc
        _ = M^2*n*y*Real.sqrt (q i) := by ring
        _ ≤ _ := hlight i
    rw [max_eq_left hat, max_eq_left (htr i), div_one, div_one]
    ring
  have hfix : tail q (M*n) (M*y) = M*y := by simpa only [y, hfy] using eq
  exact (exists_unique_tail_root q hq (mul_nonneg hM0 hn)).unique
    (root_spec q hq (mul_nonneg hM0 hn)) ⟨mul_nonneg hM0 hy, hfix⟩

end
end CanonneQuantile
