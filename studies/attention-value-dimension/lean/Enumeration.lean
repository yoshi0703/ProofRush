import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FinCases

/-! The homogeneous slack-variable indexing has the exact binomial size. -/
namespace AttentionEnumeration
open scoped BigOperators
noncomputable section

variable (d D : Nat)

def monomials := (Finset.univ : Finset (Fin (d+1))).finsuppAntidiag D

def count := Nat.choose (d+D) D

theorem card_monomials : (monomials d D).card = count d D := by
  rw [monomials, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp [count, Nat.add_comm]

def enumerate : Fin (count d D) ≃ {a // a ∈ monomials d D} := by
  have h : Fintype.card {a // a ∈ monomials d D} = count d D := by
    rw [Fintype.card_coe, card_monomials]
  exact (finCongr h.symm).trans (Fintype.equivFin _).symm

def exponent (k : Fin (count d D)) (i : Fin d) : Nat := (enumerate d D k).val i.succ

theorem exponent_bounded (k : Fin (count d D)) : ∑ i, exponent d D k i ≤ D := by
  have h := (Finset.mem_finsuppAntidiag.mp (enumerate d D k).property).1
  rw [Fin.sum_univ_succ] at h
  change (enumerate d D k).val 0 + ∑ i : Fin d, exponent d D k i = D at h
  omega

def pad (a : Fin d →₀ Nat) : Fin (d+1) →₀ Nat :=
  Finsupp.equivFunOnFinite.symm (Fin.cases (D - ∑ i, a i) (fun i => a i))

theorem pad_mem (a : Fin d →₀ Nat) (h : ∑ i, a i ≤ D) : pad d D a ∈ monomials d D := by
  apply Finset.mem_finsuppAntidiag.mpr
  constructor
  · rw [Fin.sum_univ_succ]
    simp [pad]
    omega
  · exact Finset.subset_univ _

theorem exponent_complete (a : Fin d →₀ Nat) (h : ∑ i, a i ≤ D) :
    ∃ k : Fin (count d D), ∀ i, exponent d D k i = a i := by
  let k := (enumerate d D).symm ⟨pad d D a, pad_mem d D a h⟩
  refine ⟨k, ?_⟩
  intro i
  simp [exponent, k, pad]

theorem exponent_injective : Function.Injective (exponent d D) := by
  intro k l h
  apply (enumerate d D).injective
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  refine Fin.cases ?_ ?_ j
  · have hk := (Finset.mem_finsuppAntidiag.mp (enumerate d D k).property).1
    have hl := (Finset.mem_finsuppAntidiag.mp (enumerate d D l).property).1
    rw [Fin.sum_univ_succ] at hk hl
    have hs : (∑ i : Fin d, (enumerate d D k).val i.succ) =
        ∑ i : Fin d, (enumerate d D l).val i.succ := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun h i
    omega
  · intro i
    exact congrFun h i

def expFinsupp (k : Fin (count d D)) : Fin d →₀ Nat :=
  Finsupp.equivFunOnFinite.symm (exponent d D k)

theorem expFinsupp_injective : Function.Injective (expFinsupp d D) := by
  intro k l h
  apply exponent_injective d D
  funext i
  have h' := congrArg (fun a : Fin d →₀ Nat => a i) h
  simpa [expFinsupp] using h'

theorem polynomial_expansion (g : MvPolynomial (Fin d) ℝ) (hg : g.totalDegree ≤ D) :
    g = ∑ k : Fin (count d D), MvPolynomial.monomial (expFinsupp d D k) (g.coeff (expFinsupp d D k)) := by
  classical
  apply MvPolynomial.ext
  intro a
  by_cases ha : a ∈ g.support
  · have hsum : ∑ i, a i ≤ D := by
      have h := (MvPolynomial.le_totalDegree ha).trans hg
      simpa [Finsupp.sum_fintype] using h
    obtain ⟨k, hk⟩ := exponent_complete d D a hsum
    have he : expFinsupp d D k = a := by
      ext i
      simpa [expFinsupp] using hk i
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single k]
    · simp [MvPolynomial.coeff_monomial, he]
    · intro j _ hj
      rw [MvPolynomial.coeff_monomial]
      have hne : expFinsupp d D j ≠ a := by
        intro heq
        have := expFinsupp_injective d D (heq.trans he.symm)
        exact hj this
      simp [hne]
    · simp
  · have hzero : g.coeff a = 0 := MvPolynomial.notMem_support_iff.mp ha
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_zero]
    · exact hzero
    · intro k _
      rw [MvPolynomial.coeff_monomial]
      by_cases he : expFinsupp d D k = a <;> simp [he, hzero]

end
end AttentionEnumeration
