import Dimension
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith

/-! A family of univariate polynomials of degree at most T which can realize
arbitrary separated sign changes on rational grids must have Zariski-dense
monic coefficients. The proof does not assume a bound on the head parameters. -/
namespace AttentionWindows
open Finset Polynomial
open scoped BigOperators
noncomputable section

variable {T : ℕ}

def rootPoly (z : Fin T → ℝ) : Polynomial ℝ :=
  ∏ i, (X + C (z i))

def coordinates (p : Polynomial ℝ) (i : Fin T) : ℝ := p.coeff (T - (i.val+1))

def pullback (f : MvPolynomial (Fin T) ℝ) : MvPolynomial (Fin T) ℝ :=
  (MvPolynomial.esymmAlgEquiv (Fin T) ℝ (Fintype.card_fin T) f).val

theorem pullback_ne {f : MvPolynomial (Fin T) ℝ} (h : f ≠ 0) : pullback f ≠ 0 := by
  intro hz
  apply h
  apply (MvPolynomial.esymmAlgEquiv (Fin T) ℝ (Fintype.card_fin T)).injective
  rw [map_zero]
  exact Subtype.ext hz

theorem pullback_eval (f : MvPolynomial (Fin T) ℝ) (z : Fin T → ℝ) :
    MvPolynomial.eval z (pullback f) = MvPolynomial.eval (coordinates (rootPoly z)) f := by
  rw [pullback, MvPolynomial.esymmAlgEquiv_apply, MvPolynomial.esymmAlgHom_apply]
  change MvPolynomial.eval z (MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin T => MvPolynomial.esymm (Fin T) ℝ (i.val+1)) f) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun v : Fin T → ℝ => MvPolynomial.eval v f)
  funext i
  change MvPolynomial.aeval z (MvPolynomial.esymm (Fin T) ℝ (i.val+1)) = _
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  unfold coordinates rootPoly
  rw [Finset.prod, Multiset.prod_X_add_C_coeff']
  · have hc : Multiset.card (Finset.univ : Finset (Fin T)).val = T := by simp
    rw [hc]
    congr 1
    omega
  · simp

theorem rootPoly_monic (z : Fin T → ℝ) : (rootPoly z).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_add_C (z i)

theorem rootPoly_natDegree (z : Fin T → ℝ) : (rootPoly z).natDegree = T := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (z i))]
  simp

theorem rootPoly_zero (z : Fin T → ℝ) (i : Fin T) : (rootPoly z).eval (-(z i)) = 0 := by
  simp only [rootPoly, eval_prod, eval_add, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (neg_add_cancel _)

theorem identifies {p : Polynomial ℝ} (bound : p.natDegree ≤ T) (pos : 0 < T)
    (z : Fin T → ℝ) (inj : Function.Injective z)
    (roots : ∀ i, p.eval (-(z i)) = 0) :
    p = C (p.coeff T) * rootPoly z := by
  let r := rootPoly z
  have degR : r.natDegree = T := rootPoly_natDegree z
  have mon : r.Monic := rootPoly_monic z
  have leadR : r.coeff T = 1 := by rw [← degR]; exact mon.coeff_natDegree
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun i => -(z i))
  · intro i j h
    exact inj (neg_inj.mp h)
  · intro i
    simp [eval_sub, eval_mul, roots i, rootPoly_zero z i]
  · rw [Fintype.card_fin]
    by_cases hz : p - C (p.coeff T) * rootPoly z = 0
    · simp [hz, pos]
    apply (natDegree_lt_iff_degree_lt hz).2
    apply (degree_lt_iff_coeff_zero _ _).2
    intro j hj
    rw [coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hj with he|hl
    · subst j
      change p.coeff T - p.coeff T * r.coeff T = 0
      rw [leadR, mul_one, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt bound hl),
        coeff_eq_zero_of_natDegree_lt (p := rootPoly z) (n := j) (by rw [rootPoly_natDegree]; exact hl)]
      simp

theorem root_in_interval (p : Polynomial ℝ) {a b : ℝ} (hab : a ≤ b)
    (jump : p.eval a * p.eval b < 0) : ∃ x ∈ Set.Icc a b, p.eval x = 0 := by
  rcases (mul_neg_iff.mp jump) with h|h
  · exact intermediate_value_Icc' hab p.continuous.continuousOn ⟨h.2.le,h.1.le⟩
  · exact intermediate_value_Icc hab p.continuous.continuousOn ⟨h.1.le,h.2.le⟩

end
end AttentionWindows
