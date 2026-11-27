import HeadTransfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

variable {I T : Type*} [Fintype I] [Fintype T] [DecidableEq T]

/-- These are the labels appearing in the pilot tuple, one time each. -/
def pilotSupport (x : I → T) : Finset T := Finset.univ.image x

/-- Pathwise proof of the union bound, allowing repeated pilot labels. -/
theorem pilotSupport_mass_le {r : T → ℝ} (hr : IsLaw r) (x : I → T) :
    mass r (pilotSupport x) ≤ ∑ i, r (x i) := by
  classical
  have support_filter : Finset.univ.filter (fun a : T => a ∈ pilotSupport x) = pilotSupport x := by
    ext a
    simp
  calc
    _ = ∑ a, (if a ∈ pilotSupport x then r a else 0) := by
      rw [← Finset.sum_filter, support_filter]
      rfl
    _ ≤ ∑ a : T, ∑ i : I, (if x i = a then r a else 0) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a ∈ pilotSupport x
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
        rw [ite_eq_left ha]
        calc
          r a = (if x i = a then r a else 0) := (ite_eq_left hi).symm
          _ ≤ ∑ j : I, (if x j = a then r a else 0) :=
            Finset.single_le_sum (f := fun j : I => if x j = a then r a else 0)
              (fun _ _ => by split <;> simp [hr.nonneg a]) (Finset.mem_univ i)
      · rw [ite_eq_right ha]
        exact Finset.sum_nonneg (fun i _ => by split <;> simp [hr.nonneg a])
    _ = _ := by
      rw [Finset.sum_comm]
      simp

/-- Product probability of an actual ordered tuple of iid tail pilots. -/
def pilotLaw (r : T → ℝ) (x : I → T) : ℝ := ∏ i, r (x i)

variable [DecidableEq I]

omit [DecidableEq T] in
theorem pilotLaw_isLaw {r : T → ℝ} (hr : IsLaw r) :
    IsLaw (pilotLaw (I := I) r) := by
  classical
  refine ⟨fun _ => Finset.prod_nonneg (fun _ _ => hr.nonneg _), ?_⟩
  unfold pilotLaw
  rw [← Fintype.prod_sum]
  simp [hr.total]

omit [DecidableEq T] in
theorem pilot_weighted_marginal {r : T → ℝ} (hr : IsLaw r) (f : T → ℝ) (i : I) :
    (∑ x : I → T, pilotLaw r x * f (x i)) = ∑ a, r a * f a := by
  classical
  let q (j : I) (a : T) := r a * if j = i then f a else 1
  calc
    _ = ∑ x : I → T, ∏ j, q j (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      unfold q
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq']
      rfl
    _ = ∏ j : I, ∑ a : T, q j a := (Fintype.prod_sum q).symm
    _ = _ := by
      have hpoint (j : I) :
          (∑ a : T, q j a) = if j = i then (∑ a, r a * f a) else 1 := by
        by_cases h : j = i <;> simp [q, h, hr.total]
      simp only [hpoint, Fintype.prod_ite_eq']

/-- Expected reference mass of the random pilot support. -/
theorem pilot_support_expected_mass {r : T → ℝ} (hr : IsLaw r) :
    (∑ x : I → T, pilotLaw r x * mass r (pilotSupport x)) ≤
      (Fintype.card I : ℝ) * ∑ a : T, (r a)^2 := by
  classical
  calc
    _ ≤ ∑ x : I → T, pilotLaw r x * (∑ i, r (x i)) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (pilotSupport_mass_le hr x) ((pilotLaw_isLaw hr).nonneg x)
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [pilot_weighted_marginal hr r, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_two]
      rw [Finset.mul_sum]

/-- The strict bad-support event has at most the stated reference product mass. -/
theorem pilot_bad_support_mass {r : T → ℝ} (hr : IsLaw r) {y : ℝ} (hy : 0 < y) :
    mass (pilotLaw (I := I) r)
      (Finset.univ.filter (fun x : I → T => y < mass r (pilotSupport x))) ≤
      ((Fintype.card I : ℝ) * ∑ a : T, (r a)^2) / y := by
  classical
  let bad := Finset.univ.filter (fun x : I → T => y < mass r (pilotSupport x))
  have h₁ : mass (pilotLaw r) bad * y ≤
      ∑ x ∈ bad, pilotLaw r x * mass r (pilotSupport x) := by
    unfold mass
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun x hx =>
      mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2.le ((pilotLaw_isLaw hr).nonneg x)
  have h₂ : (∑ x ∈ bad, pilotLaw r x * mass r (pilotSupport x)) ≤
      ∑ x : I → T, pilotLaw r x * mass r (pilotSupport x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg ((pilotLaw_isLaw hr).nonneg x)
        (Finset.sum_nonneg fun a _ => hr.nonneg a))
  exact (le_div_iff₀ hy).mpr (h₁.trans (h₂.trans (pilot_support_expected_mass hr)))

/-- The support truncation event in the transfer discards at most one percent
when the chosen pilot count meets the second-moment budget. -/
theorem pilot_bad_support_one_percent {r : T → ℝ} (hr : IsLaw r) {y : ℝ} (hy : 0 < y)
    (hbudget : (Fintype.card I : ℝ) * ∑ a : T, (r a)^2 ≤ y / 100) :
    mass (pilotLaw (I := I) r)
      (Finset.univ.filter (fun x : I → T => y < mass r (pilotSupport x))) ≤ 1 / 100 := by
  refine (pilot_bad_support_mass hr hy).trans ((div_le_iff₀ hy).mpr ?_)
  linarith

end
end CanonneHeadTransfer
