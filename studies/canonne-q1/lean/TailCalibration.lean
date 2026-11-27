import TailCrossing
import SplitLabels

namespace CanonneQuantile

open CanonneRefinement
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A]

def criterion (q : A → ℝ) (n x : ℝ) : ℝ := tail q n (Real.sqrt x)/Real.sqrt x

def cutoff (n x : ℝ) : ℝ := 1/(n^2*x)

theorem sqrt_cutoff {n x : ℝ} (hn : 0 < n) (_hx : 0 < x) :
    Real.sqrt (cutoff n x) = 1/(n * Real.sqrt x) := by
  rw [cutoff,Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hn.le]

theorem criterion_from_clipped (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    {n x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    criterion q n x * Real.sqrt x = n * clippedMoment q (cutoff n x) := by
  have hy := Real.sqrt_pos.mpr hx
  rw [criterion, div_mul_cancel₀ _ hy.ne', tail_eq_clipped q hq hn.le hy]
  unfold clippedMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sqrt_cutoff hn hx, ← mul_assoc, mul_min_of_nonneg _ _ (mul_nonneg hn.le (hq a)), min_comm]
  congr 1
  field_simp

theorem calibrated_split_height (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    {n x : ℝ} (hn : 0 < n) (hx : 0 < x) (hlarge : 16 ≤ criterion q n x) :
    let m := fun a => multiplicity (cutoff n x) (q a)
    8*Real.sqrt x / n ≤ height (clone m q) := by
  let m := fun a => multiplicity (cutoff n x) (q a)
  let H := height (clone m q)
  have hcap : 0 < cutoff n x := by unfold cutoff; positivity
  have hH : 0 ≤ H := Finset.sum_nonneg fun a _ =>
    mul_nonneg (div_nonneg (hq _) (by positivity)) (Real.sqrt_nonneg _)
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_nonneg (Real.sqrt 2-2)]
  have h2' := (actual_split_height q hq hcap).2
  change clippedMoment q (cutoff n x) ≤ Real.sqrt 2*H at h2'
  have hbound := mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_right h2 hH)) hn.le
  have hrate := mul_le_mul_of_nonneg_right hlarge (Real.sqrt_nonneg x)
  rw [criterion_from_clipped q hq hn hx] at hrate
  exact (div_le_iff₀ hn).mpr (by change 8*Real.sqrt x ≤ H*n; linarith)

theorem heavy_light_budgets (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    {n x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    (∑ i ∈ Finset.univ.filter (fun i => cutoff n x ≤ q i), q i) ≤ x*criterion q n x ∧
    n*Real.sqrt x*(∑ i ∈ Finset.univ.filter (fun i => q i < cutoff n x),
      q i*Real.sqrt (q i)) ≤ x*criterion q n x := by
  let y := Real.sqrt x
  have hy : 0 < y := Real.sqrt_pos.mpr hx
  have hysq : y^2 = x := Real.sq_sqrt hx.le
  have hcap : 0 < cutoff n x := by unfold cutoff; positivity
  have heq : x*criterion q n x = n*y*clippedMoment q (cutoff n x) := by
    have he1 := criterion_from_clipped q hq hn hx
    change criterion q n x * y = _ at he1
    calc
      _ = y^2*criterion q n x := by rw [hysq]
      _ = y*(criterion q n x*y) := by ring
      _ = _ := by rw [he1]; ring
  rw [heq]
  let f (i : A) := q i * min (Real.sqrt (q i)) (Real.sqrt (cutoff n x))
  have hf (i) : 0 ≤ f i := mul_nonneg (hq i) (le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have sub (s : Finset A) : ∑ i ∈ s, f i ≤ clippedMoment q (cutoff n x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => hf i)
  have hny : 0 ≤ n*y := mul_nonneg hn.le hy.le
  constructor
  · let s := Finset.univ.filter (fun i => cutoff n x ≤ q i)
    have hsum : (∑ i ∈ s, q i) = n*y*(∑ i ∈ s, f i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hb : cutoff n x ≤ q i := (Finset.mem_filter.mp hi).2
      unfold f
      rw [min_eq_right (Real.sqrt_le_sqrt hb), sqrt_cutoff hn hx]
      change q i = n*y*(q i*(1/(n*y)))
      field_simp
    exact hsum.le.trans (mul_le_mul_of_nonneg_left (sub s) hny)
  · apply mul_le_mul_of_nonneg_left _ hny
    let s := Finset.univ.filter (fun i => q i < cutoff n x)
    refine le_trans ?_ (sub s)
    apply Finset.sum_le_sum
    intro i hi
    have hb : q i < cutoff n x := (Finset.mem_filter.mp hi).2
    unfold f
    rw [min_eq_left (Real.sqrt_le_sqrt hb.le)]

theorem criterion_at_reverse_scale (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    {n x : ℝ} (hn : 0 < n) (hx : 0 < x) (hfloor : 8 ≤ n*x)
    (hroot : 64 * root q hq n hn.le ≤ Real.sqrt x) :
    criterion q n x ≤ 1/64 ∧ 2*cutoff n x ≤ x/32 := by
  have hr := root_spec q hq hn.le
  have hy := Real.sqrt_pos.mpr hx
  have h := tail_antitone q hq hn.le (show root q hq n hn.le ≤ Real.sqrt x by linarith [hr.1])
  rw [hr.2] at h
  constructor
  · exact (div_le_iff₀ hy).mpr (by linarith)
  · unfold cutoff
    have hp : 0 < n^2*x := by positivity
    have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) hfloor 2
    field_simp
    nlinarith

theorem criterion_at_forward_scale (q : A → ℝ) (hq : ∀ a, 0 ≤ q a)
    {n x : ℝ} (hn : 0 < n) (hx : 0 < x)
    (hroot : 16 * Real.sqrt x ≤ root q hq n hn.le) :
    16 ≤ criterion q n x := by
  have hy := Real.sqrt_pos.mpr hx
  have h := tail_antitone q hq hn.le (show Real.sqrt x ≤ root q hq n hn.le by linarith)
  rw [(root_spec q hq hn.le).2] at h
  exact (le_div_iff₀ hy).mpr (hroot.trans h)

end
end CanonneQuantile
