import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic

/-! A linear target on a finite population can be estimated without bias under
all designs in a family if and only if label-specific sample weights solve
their simultaneous inclusion equations. The observed data are the sample
identifier and its masked population. No design identifier is observed. -/
namespace LinearEstimator
open scoped BigOperators
noncomputable section

variable {I S R : Type*} [Fintype I] [DecidableEq I] [Fintype S]

def mask (seen : S → I → Bool) (s : S) (y : I → ℕ) (i : I) : ℕ :=
  if seen s i then y i else 0

def point (i j : I) : ℕ := if j=i then 1 else 0

omit [Fintype I] [Fintype S] in
private theorem mask_off (seen : S → I → Bool) (s : S) (i : I) (h : seen s i=false) :
    mask seen s (point i) = mask seen s (fun _ => 0) := by
  funext j
  by_cases e : j=i
  · subst j
    simp [mask,h]
  · simp [mask,point,e]

/-- The weights may depend on both a sampled label and the full observed
sample. Each design is a row of probabilities on the finite sample space.
The identity in fact requires no signs or normalization of those rows. -/
theorem simultaneous_calibration (seen : S → I → Bool) (p : R → S → ℝ) (a : I → ℝ) :
    (∃ T : S → (I → ℕ) → ℝ, ∀ r y,
        ∑ s, p r s * T s (mask seen s y) = ∑ i, a i * (y i : ℝ)) ↔
    (∃ w : I → S → ℝ, ∀ r i,
        ∑ s, (if seen s i then p r s * w i s else 0) = a i) := by
  constructor
  · rintro ⟨T,h⟩
    refine ⟨fun i s => T s (mask seen s (point i)) - T s (mask seen s (fun _ => 0)), ?_⟩
    intro r i
    have delta := h r (point i)
    have zero := h r (fun _ => 0)
    calc
      _ = ∑ s, (p r s * T s (mask seen s (point i)) -
          p r s * T s (mask seen s (fun _ => 0))) := by
        apply Finset.sum_congr rfl
        intro s _
        cases b : seen s i with
        | false => simp [mask_off seen s i b]
        | true => simp [mul_sub]
      _ = a i := by
        rw [Finset.sum_sub_distrib,delta,zero]
        simp [point,apply_ite,Finset.sum_ite_eq']
  · rintro ⟨w,h⟩
    refine ⟨fun s data => ∑ i, w i s * (data i : ℝ), ?_⟩
    intro r y
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← h r i,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    cases b : seen s i <;> simp [mask,b,mul_assoc]

#print axioms simultaneous_calibration
end
end LinearEstimator
