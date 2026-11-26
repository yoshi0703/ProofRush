import Softmax
import Chart
import Enumeration
import Mathlib.Tactic.FieldSimp

namespace AttentionBridge
open scoped BigOperators
open Polynomial AttentionModel AttentionChart
noncomputable section
set_option maxHeartbeats 1000000

variable {H D d M : Nat}

def readout (weights : Fin M → ℝ) (exponent : Fin M → Fin d → Nat)
    (z : Fin d → ℝ) : ℝ :=
  ∑ k, weights k * ∏ i, z i ^ exponent k i

def cleared (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ)
    (exponent : Fin M → Fin d → Nat) : Polynomial ℝ :=
  ∑ k, Polynomial.C (weights k) * ps 0 ^ (D - mass d M exponent k) *
    ∏ i, ps i.succ ^ exponent k i

theorem eval_cleared (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ)
    (exponent : Fin M → Fin d → Nat) (t : ℝ) :
    (cleared (D:=D) ps weights exponent).eval t =
      ∑ k, weights k * (ps 0).eval t ^ (D - mass d M exponent k) *
        ∏ i, (ps i.succ).eval t ^ exponent k i := by
  change (Polynomial.evalRingHom t) (cleared (D:=D) ps weights exponent) = _
  simp [cleared, map_sum, Polynomial.eval_prod]

theorem cleared_eq (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ)
    (exponent : Fin M → Fin d → Nat) (bounded : ∀ k, mass d M exponent k ≤ D)
    (t : ℝ) (hq : (ps 0).eval t ≠ 0) :
    (cleared (D:=D) ps weights exponent).eval t =
      (ps 0).eval t ^ D * readout weights exponent (fun i => (ps i.succ).eval t / (ps 0).eval t) := by
  rw [eval_cleared]
  unfold readout
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hk := bounded k
  have hp : (ps 0).eval t ^ D = (ps 0).eval t ^ (D - mass d M exponent k) *
      (ps 0).eval t ^ mass d M exponent k := by rw [← pow_add]; congr 1; omega
  rw [hp]
  field_simp
  simp [mass]

/-- The finite slack-variable enumeration covers every nonhomogeneous
multivariate polynomial of degree at most D, not only selected monomials. -/
theorem readout_complete (g : MvPolynomial (Fin d) ℝ) (hg : g.totalDegree ≤ D)
    (z : Fin d → ℝ) :
    readout (fun k => g.coeff (AttentionEnumeration.expFinsupp d D k))
      (AttentionEnumeration.exponent d D) z = MvPolynomial.eval z g := by
  conv_rhs => rw [AttentionEnumeration.polynomial_expansion d D g hg]
  simp [readout, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype, AttentionEnumeration.expFinsupp]

/-- Every original normalized softmax layer determines this common polynomial tuple. -/
def modelPolys (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) : Fin (d+1) → Polynomial ℝ :=
  Fin.cases (qPoly r) (pPoly r v0 v1)

theorem modelPolys_degree (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) :
    ∀ row, (modelPolys r v0 v1 row).natDegree ≤ H := by
  intro row
  refine Fin.cases ?_ ?_ row
  · exact qPoly_degree r
  · intro i
    exact pPoly_degree r v0 v1 i

theorem model_cleared (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (weights : Fin M → ℝ) (exponent : Fin M → Fin d → Nat)
    (bounded : ∀ k, mass d M exponent k ≤ D) (t : ℝ)
    (hr : ∀ h, 0 < r h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (cleared (D:=D) (modelPolys r v0 v1) weights exponent).eval t =
      commonDen r t ^ D * readout weights exponent (fun i => heads r v0 v1 i t) := by
  have hq : ((modelPolys r v0 v1) 0).eval t ≠ 0 := by
    change (qPoly r).eval t ≠ 0
    rw [eval_qPoly]
    exact ne_of_gt (commonDen_pos r t hr ht0 ht1)
  rw [cleared_eq _ weights exponent bounded t hq]
  change (qPoly r).eval t ^ D * readout weights exponent
    (fun i => (pPoly r v0 v1 i).eval t / (qPoly r).eval t) = _
  rw [eval_qPoly]
  congr 2
  funext i
  rw [eval_pPoly]
  symm
  exact heads_common r v0 v1 i t (fun h => ne_of_gt (headDen_pos (r h) t (hr h) ht0 ht1))

/-- All coefficients of the cleared original layer are values of fixed
multivariate polynomials in (d+1)(H+1)+M real parameters. -/
theorem model_coefficient_chart (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (weights : Fin M → ℝ) (exponent : Fin M → Fin d → Nat) (j : Nat) :
    MvPolynomial.eval (assignment H d M (coefficients H d M (modelPolys r v0 v1) weights))
      (coefficient H D d M exponent j) =
      (cleared (D:=D) (modelPolys r v0 v1) weights exponent).coeff j := by
  exact chart_covers H D d M (modelPolys r v0 v1) weights (modelPolys_degree r v0 v1) exponent j

/-- General degree-D readout and the exact binomial-sized chart. -/
theorem all_readouts (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (g : MvPolynomial (Fin d) ℝ) (hg : g.totalDegree ≤ D)
    (hr : ∀ h, 0 < r h) :
    ∃ (R : Polynomial ℝ)
      (θ : Fin (Count H d (AttentionEnumeration.count d D)) → ℝ),
      (∀ j, MvPolynomial.eval θ
        (coefficient H D d (AttentionEnumeration.count d D) (AttentionEnumeration.exponent d D) j) = R.coeff j) ∧
      (∀ t, 0 ≤ t → t ≤ 1 →
        R.eval t = commonDen r t ^ D * MvPolynomial.eval (fun i => heads r v0 v1 i t) g) := by
  let weights := fun k : Fin (AttentionEnumeration.count d D) =>
    g.coeff (AttentionEnumeration.expFinsupp d D k)
  let exponent := AttentionEnumeration.exponent d D
  let R := cleared (D:=D) (modelPolys r v0 v1) weights exponent
  let θ := assignment H d (AttentionEnumeration.count d D)
    (coefficients H d (AttentionEnumeration.count d D) (modelPolys r v0 v1) weights)
  refine ⟨R, θ, ?_, ?_⟩
  · intro j
    exact model_coefficient_chart r v0 v1 weights exponent j
  · intro t ht0 ht1
    rw [model_cleared r v0 v1 weights exponent ?_ t hr ht0 ht1]
    · rw [readout_complete g hg]
    · intro k
      exact AttentionEnumeration.exponent_bounded d D k

end
end AttentionBridge
