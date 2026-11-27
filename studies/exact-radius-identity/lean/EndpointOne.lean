import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CanonneEndpoint

open scoped BigOperators
noncomputable section

structure IsLaw {α : Type*} [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  total : ∑ i, p i = 1

def mass {α : Type*} (p : α → ℝ) (S : Finset α) : ℝ :=
  ∑ i ∈ S, p i

def tv {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ i, |p i - q i|) / 2

theorem tv_overlap {α : Type*} [Fintype α] {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    tv p q = 1 - ∑ i, min (p i) (q i) := by
  unfold tv
  have point (i : α) : |p i - q i| = p i + q i - 2 * min (p i) (q i) := by
    rcases le_total (p i) (q i) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), min_eq_right h]
      ring
  simp only [point, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hp.total, hq.total]
  ring

/-- The positive difference event is an explicit maximizer in the finite TV formula. -/
theorem tv_eq_mass_difference {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) :
    let A := Finset.univ.filter (fun i => q i < p i)
    tv p q = mass p A - mass q A := by
  classical
  dsimp only
  rw [tv_overlap hp hq]
  have point (i : α) :
      p i - min (p i) (q i) = if q i < p i then p i - q i else 0 := by
    by_cases h : q i < p i
    · rw [ite_eq_left h, min_eq_right h.le]
    · rw [ite_eq_right h, min_eq_left (le_of_not_gt h), sub_self]
  calc
    1 - ∑ i, min (p i) (q i) = ∑ i, (p i - min (p i) (q i)) := by
      rw [Finset.sum_sub_distrib, hp.total]
    _ = ∑ i, (if q i < p i then p i - q i else 0) := Finset.sum_congr rfl fun i _ => point i
    _ = mass p (Finset.univ.filter (fun i => q i < p i)) -
        mass q (Finset.univ.filter (fun i => q i < p i)) := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib]
      rfl

/-- At one sample, the test rejects exactly on this set of known low-mass labels. -/
def rejectionSet {α : Type*} [Fintype α] (q : α → ℝ) (ρ : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter fun i => q i ≤ ρ

theorem rejectionSet_null_mass {α : Type*} [Fintype α] (q : α → ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : mass q (rejectionSet q ρ) ≤ (Fintype.card α : ℝ) * ρ := by
  classical
  unfold mass rejectionSet
  calc
    (∑ i ∈ Finset.univ.filter (fun i => q i ≤ ρ), q i) ≤
        ∑ _i ∈ Finset.univ.filter (fun i => q i ≤ ρ), ρ :=
      Finset.sum_le_sum fun _ hi => (Finset.mem_filter.mp hi).2
    _ ≤ (Fintype.card α : ℝ) * ρ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hρ
      exact_mod_cast Finset.card_filter_le _ _

theorem rejectionSet_alternative_mass {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) {ρ : ℝ} (hfar : 1 - ρ ≤ tv p q) :
    1 - ρ ≤ mass p (rejectionSet q ρ) := by
  classical
  let A := Finset.univ.filter (fun i => q i < p i)
  have htv : tv p q = mass p A - mass q A := tv_eq_mass_difference hp hq
  have hpA : mass p A ≤ 1 := by
    rw [← hp.total]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun i _ _ => hp.nonneg i)
  have hqA_nonneg : 0 ≤ mass q A := Finset.sum_nonneg fun i _ => hq.nonneg i
  have hqA : mass q A ≤ ρ := by linarith
  have hs : A ⊆ rejectionSet q ρ := by
    intro i hi
    unfold rejectionSet
    have hsub : ({i} : Finset α) ⊆ A := Finset.singleton_subset_iff.mpr hi
    have hqi : q i ≤ mass q A := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hq.nonneg j)
      simpa [mass] using h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hqi.trans hqA⟩
  have hmon : mass p A ≤ mass p (rejectionSet q ρ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => hp.nonneg i)
  linarith

/-- For every null law, a single deterministic sample has both error probabilities ≤ 1/3
    at the inclusive distance cutoff \(1-1/(4n)\), with \(n\) the alphabet size. -/
theorem one_sample_endpoint {α : Type*} [Fintype α] (hn : 2 ≤ Fintype.card α)
    {q : α → ℝ} (hq : IsLaw q) :
    let ρ : ℝ := 1 / (4 * (Fintype.card α : ℝ))
    let R := rejectionSet q ρ
    mass q R ≤ 1 / 3 ∧
      ∀ p : α → ℝ, IsLaw p → 1 - ρ ≤ tv p q → 1 - mass p R ≤ 1 / 3 := by
  let n : ℝ := Fintype.card α
  let ρ : ℝ := 1 / (4 * n)
  have hnR : (2 : ℝ) ≤ n := by
    change (2 : ℝ) ≤ (Fintype.card α : ℝ)
    exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hden : 0 < 4 * n := by positivity
  have hρ : 0 ≤ ρ := by exact div_nonneg (by norm_num) hden.le
  have hρthird : ρ ≤ 1 / 3 := by
    change 1 / (4 * n) ≤ 1 / 3
    apply (div_le_div_iff_of_pos_left (show (0 : ℝ) < 1 by norm_num) hden
      (show (0 : ℝ) < 3 by norm_num)).mpr
    linarith
  have hcard : n * ρ = 1 / 4 := by
    dsimp only [ρ]
    field_simp [ne_of_gt hn0]
  change mass q (rejectionSet q ρ) ≤ 1 / 3 ∧
    ∀ p : α → ℝ, IsLaw p → 1 - ρ ≤ tv p q → 1 - mass p (rejectionSet q ρ) ≤ 1 / 3
  constructor
  · have h := rejectionSet_null_mass q hρ
    change mass q (rejectionSet q ρ) ≤ n * ρ at h
    rw [hcard] at h
    linarith
  · intro p hp hfar
    have h := rejectionSet_alternative_mass hp hq hfar
    linarith

/-- At this exact cutoff there are full-support null laws with a nonempty alternative. -/
theorem positive_null_with_boundary_alternative (n : ℕ) (hn : 2 ≤ n) :
    ∃ q p : Fin n → ℝ, IsLaw q ∧ IsLaw p ∧ (∀ i, 0 < q i) ∧
      tv p q = 1 - 1 / (4 * (n : ℝ)) := by
  classical
  let lo : Fin n := ⟨0, by omega⟩
  let hi : Fin n := ⟨1, by omega⟩
  have hne : hi ≠ lo := by
    intro h
    have hval := congrArg Fin.val h
    norm_num [hi, lo] at hval
  let ρ : ℝ := 1 / (4 * (n : ℝ))
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcard : (n : ℝ) * ρ = 1 / 4 := by
    dsimp only [ρ]
    field_simp [ne_of_gt hn0]
  let q : Fin n → ℝ := fun i => ρ + if i = lo then 3 / 4 else 0
  let p : Fin n → ℝ := fun i => if i = hi then 1 else 0
  have hq_pos (i : Fin n) : 0 < q i := by
    by_cases h : i = lo <;> simp [q, h] <;> linarith
  have hq : IsLaw q := by
    refine ⟨fun i => (hq_pos i).le, ?_⟩
    unfold q
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hcard]
    norm_num
  have hp : IsLaw p := by
    refine ⟨?_, ?_⟩
    · intro i
      by_cases h : i = hi <;> simp [p, h]
    · simp [p]
  refine ⟨q, p, hq, hp, hq_pos, ?_⟩
  have hρ1 : ρ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hnR hρ.le
    linarith
  have point (i : Fin n) : min (p i) (q i) = if i = hi then ρ else 0 := by
    by_cases h : i = hi
    · subst i
      simpa [p, q, hne] using min_eq_right hρ1
    · simp [p, h, min_eq_left (hq_pos i).le]
  rw [tv_overlap hp hq]
  simp [point, ρ]

end
end CanonneEndpoint
