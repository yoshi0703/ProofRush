import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Topology.Instances.Real.Lemmas

/-! Shared degree-bounded monomial features and an explicit homogeneous
readout, as used in Hsu–Xu Lemma 13. -/
noncomputable section

namespace AttentionUpper

open scoped BigOperators

variable {I : Type*} {K : Type*} [CommSemiring K]

/-- A degree basis, with the constant feature (exponent zero) available
for padding each representation to exactly D summands. -/
def ExactBasis (exponent : I → Nat) (H D : Nat) : Prop :=
  (∀ i, exponent i ≤ H) ∧
    ∀ e : Fin (H*D+1), ∃ pick : Fin D → I, ∑ j, exponent (pick j) = e.val

def features (exponent : I → Nat) (i : I) : Polynomial K :=
  Polynomial.X ^ exponent i

theorem features_degree [Nontrivial K] {exponent : I → Nat} {H : Nat}
    (bound : ∀ i, exponent i ≤ H) (i : I) :
    (features exponent i : Polynomial K).natDegree ≤ H := by
  simpa [features] using bound i

/-- The supplied selector is the table of exactly-D additive
representations. Formula uses actual products of feature variables. -/
noncomputable def readout {H D : Nat} (pick : Fin (H*D+1) → Fin D → I)
    (F : Polynomial K) : MvPolynomial I K :=
  ∑ e, MvPolynomial.C (F.coeff e.val) * ∏ j, MvPolynomial.X (pick e j)

theorem readout_homogeneous {H D : Nat} (pick : Fin (H*D+1) → Fin D → I)
    (F : Polynomial K) : (readout pick F).IsHomogeneous D := by
  unfold readout
  apply MvPolynomial.IsHomogeneous.sum
  intro e _
  have product : (∏ j : Fin D, MvPolynomial.X (pick e j) : MvPolynomial I K).IsHomogeneous D := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun j : Fin D => (MvPolynomial.X (pick e j) : MvPolynomial I K))
      (fun _ => 1) (fun j _ => MvPolynomial.isHomogeneous_X K (pick e j))
  simpa using (MvPolynomial.isHomogeneous_C I (F.coeff e.val)).mul product

theorem readout_realizes {H D : Nat} (exponent : I → Nat)
    (pick : Fin (H*D+1) → Fin D → I) (spec : ∀ e, ∑ j, exponent (pick e j) = e.val)
    (F : Polynomial K) (bound : F.natDegree ≤ H*D) :
    MvPolynomial.aeval (features exponent) (readout pick F) = F := by
  have product (e : Fin (H*D+1)) :
      (∏ j : Fin D, (features exponent (pick e j) : Polynomial K)) = Polynomial.X ^ e.val := by
    unfold features
    rw [Finset.prod_pow_eq_pow_sum, spec]
  unfold readout
  simp only [map_sum, map_mul, map_prod, MvPolynomial.aeval_C, Polynomial.algebraMap_apply,
    MvPolynomial.aeval_X, product]
  change (∑ e : Fin (H*D+1),
    (fun n : Nat => Polynomial.C (F.coeff n) * Polynomial.X ^ n) e.val) = F
  rw [Fin.sum_univ_eq_sum_range (fun n : Nat => Polynomial.C (F.coeff n) * Polynomial.X ^ n) (H*D+1)]
  exact (F.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le bound)).symm

/-- The same degree-H feature list works for every degree-at-most-HD
univariate target. The homogeneous readout coefficients may vary. -/
theorem shared_features [Nontrivial K] {H D : Nat} {exponent : I → Nat}
    (basis : ExactBasis exponent H D) :
    (∀ i, (features exponent i : Polynomial K).natDegree ≤ H) ∧
      ∀ F : Polynomial K, F.natDegree ≤ H*D →
        ∃ g : MvPolynomial I K, g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
          MvPolynomial.aeval (features exponent) g = F := by
  classical
  choose pick spec using basis.2
  refine ⟨features_degree basis.1, fun F bound => ?_⟩
  have hom := readout_homogeneous pick F
  exact ⟨readout pick F, hom, hom.totalDegree_le, readout_realizes exponent pick spec F bound⟩

/-- For any common positive denominator, homogeneous readout has exactly
the corresponding positive scale factor at a scalar input. -/
theorem readout_scaled {D : Nat} (exponent : I → Nat) {g : MvPolynomial I ℝ}
    (hom : g.IsHomogeneous D) {F : Polynomial ℝ}
    (realizes : MvPolynomial.aeval (features exponent) g = F)
    {t q : ℝ} :
    MvPolynomial.eval (fun i => (features exponent i : Polynomial ℝ).eval t / q) g =
      (q⁻¹)^D * F.eval t := by
  let e : Polynomial ℝ →ₐ[ℝ] ℝ := Polynomial.aeval t
  have value := congrArg e realizes
  rw [MvPolynomial.comp_aeval_apply] at value
  have base : MvPolynomial.eval (fun i => (features exponent i : Polynomial ℝ).eval t) g = F.eval t := by
    simpa only [e, MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval] using value
  have scale : (fun i => (features exponent i : Polynomial ℝ).eval t / q) =
      q⁻¹ • (fun i => (features exponent i : Polynomial ℝ).eval t) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [scale, hom.eval_smul, base]

theorem readout_strict_sign {D : Nat} (exponent : I → Nat) {g : MvPolynomial I ℝ}
    (hom : g.IsHomogeneous D) {F : Polynomial ℝ}
    (realizes : MvPolynomial.aeval (features exponent) g = F) {t q : ℝ} (pos : 0 < q) :
    (0 < MvPolynomial.eval (fun i => (features exponent i : Polynomial ℝ).eval t / q) g) ↔
      0 < F.eval t := by
  rw [readout_scaled exponent hom realizes]
  exact mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr pos) D)

#print axioms shared_features
#print axioms readout_strict_sign

end AttentionUpper

end
