import GridSigns
import Mathlib.Data.Finset.Powerset
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite-cube symmetrization, preserving total degree and strict signs.
The univariate polynomial interpolates the means on Hamming-weight levels. -/

namespace AttentionSymmetry

open AttentionGrid Polynomial
open scoped BigOperators

noncomputable section

def subsetBits {n : ℕ} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ s)

@[simp] theorem weight_subsetBits {n : ℕ} (s : Finset (Fin n)) :
    hammingWeight (subsetBits s) = s.card := by
  have eq : (Finset.univ.filter fun i => subsetBits s i) = s := by
    ext i
    simp [subsetBits]
  simp only [hammingWeight, eq]

/-- This degree-`r` polynomial evaluates to `k.choose r` at the `k`th grid point. -/
def binomialPolynomial (n r : ℕ) : Polynomial ℝ :=
  C ((r.factorial : ℝ)⁻¹) * (descPochhammer ℝ r).comp (C (n : ℝ) * X)

theorem binomialPolynomial_degree (n r : ℕ) : (binomialPolynomial n r).natDegree ≤ r := by
  unfold binomialPolynomial
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  rw [descPochhammer_natDegree]
  simpa only [mul_one] using
    Nat.mul_le_mul_left r ((natDegree_C_mul_le (n : ℝ) X).trans natDegree_X_le)

theorem binomialPolynomial_eval {n : ℕ} (hn : 0 < n) (k r : ℕ) :
    (binomialPolynomial n r).eval (grid n k) = (k.choose r : ℝ) := by
  have hscale : (n : ℝ) * grid n k = k := by
    unfold grid
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')
  rw [binomialPolynomial, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, hscale,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hnz : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
  field_simp

private theorem monomial_bits {n : ℕ} (a : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    (∏ i ∈ a.support, booleanReals (subsetBits s) i ^ a i) =
      if a.support ⊆ s then 1 else 0 := by
  classical
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i hi
    simp [booleanReals, subsetBits, h hi]
  · obtain ⟨i, hi, hs⟩ : ∃ i ∈ a.support, i ∉ s := by
      have witness : ∃ i, ∃ _ : i ∈ a.support, i ∉ s := by
        simpa only [Finset.subset_iff, not_forall, not_imp] using h
      obtain ⟨i, hi, hs⟩ := witness
      exact ⟨i, hi, hs⟩
    refine Finset.prod_eq_zero hi ?_
    simp [booleanReals, subsetBits, hs, zero_pow (Finsupp.mem_support_iff.mp hi)]

private theorem count_containing {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :
    n.choose s.card *
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter (s ⊆ ·)).card =
      n.choose k * k.choose s.card := by
  classical
  by_cases h : s.card ≤ k
  · rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _) h]
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Nat.choose_mul h).symm
  · have empty : (((Finset.univ : Finset (Fin n)).powersetCard k).filter (s ⊆ ·)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha, hs⟩ := Finset.mem_filter.mp ha
      exact h ((Finset.card_le_card hs).trans_eq (Finset.mem_powersetCard.mp ha).2)
    simp [empty, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

private theorem avg_monomial {n : ℕ} (a : Fin n →₀ ℕ) (k : ℕ) :
    ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∏ i ∈ a.support, booleanReals (subsetBits s) i ^ a i =
      (n.choose k : ℝ) * (k.choose a.support.card : ℝ) / (n.choose a.support.card : ℝ) := by
  classical
  simp_rw [monomial_bits]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have bound : a.support.card ≤ n := by
    simpa using Finset.card_le_univ a.support
  have nz : (n.choose a.support.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos bound).ne'
  apply (eq_div_iff nz).2
  rw [mul_comm]
  exact_mod_cast count_containing a.support k

/-- The coefficient from a Boolean monomial depends on the size of its support. -/
def averagePolynomial {n : ℕ} (b : MvPolynomial (Fin n) ℝ) : Polynomial ℝ :=
  ∑ a ∈ b.support, C (b.coeff a / (n.choose a.support.card : ℝ)) *
    binomialPolynomial n a.support.card

theorem averagePolynomial_degree {n : ℕ} (b : MvPolynomial (Fin n) ℝ) :
    (averagePolynomial b).natDegree ≤ b.totalDegree := by
  unfold averagePolynomial
  refine natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
  refine (natDegree_C_mul_le _ _).trans ((binomialPolynomial_degree _ _).trans ?_)
  have h : a.support.card ≤ a.sum (fun _ d => d) := by
    unfold Finsupp.sum
    calc
      _ = ∑ _i ∈ a.support, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  exact h.trans (MvPolynomial.le_totalDegree ha)

/-- On a fixed weight level, the polynomial gives the exact arithmetic mean. -/
theorem averagePolynomial_mul_eval {n : ℕ} (hn : 0 < n) (b : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    (n.choose k : ℝ) * (averagePolynomial b).eval (grid n k) =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        MvPolynomial.eval (booleanReals (subsetBits s)) b := by
  classical
  simp only [averagePolynomial, eval_finsetSum, eval_mul, eval_C, binomialPolynomial_eval hn,
    Finset.mul_sum, MvPolynomial.eval_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, avg_monomial]
  ring

/-- If a real polynomial represents a strict symmetric sign pattern on the
Boolean cube, a univariate polynomial of no greater degree represents the
same strict signs on the normalized Hamming-weight grid. -/
theorem exists_grid_sign {n T : ℕ} (hn : 0 < n) (b : MvPolynomial (Fin n) ℝ)
    (degree : b.totalDegree ≤ T)
    (strict : ∀ x : Fin n → Bool, MvPolynomial.eval (booleanReals x) b ≠ 0)
    (symmetric : ∀ x y : Fin n → Bool, hammingWeight x = hammingWeight y →
      (0 < MvPolynomial.eval (booleanReals x) b ↔ 0 < MvPolynomial.eval (booleanReals y) b)) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ T ∧ ∀ x : Fin n → Bool,
      0 < p.eval (grid n (hammingWeight x)) * MvPolynomial.eval (booleanReals x) b := by
  classical
  refine ⟨averagePolynomial b, (averagePolynomial_degree b).trans degree, ?_⟩
  intro x
  let k := hammingWeight x
  let level := (Finset.univ : Finset (Fin n)).powersetCard k
  have chosen : 0 < n.choose k := Nat.choose_pos (hammingWeight_le x)
  have nonempty : level.Nonempty := by
    apply Finset.card_pos.mp
    simpa [level] using chosen
  have realChosen : (0 : ℝ) < n.choose k := by exact_mod_cast chosen
  have average := averagePolynomial_mul_eval hn b k
  change (n.choose k : ℝ) * (averagePolynomial b).eval (grid n k) =
    ∑ s ∈ level, MvPolynomial.eval (booleanReals (subsetBits s)) b at average
  have same : ∀ s ∈ level,
      (0 < MvPolynomial.eval (booleanReals x) b ↔
        0 < MvPolynomial.eval (booleanReals (subsetBits s)) b) := by
    intro s hs
    exact symmetric x (subsetBits s) (by
      rw [weight_subsetBits]
      exact (Finset.mem_powersetCard.mp hs).2.symm)
  rcases lt_or_gt_of_ne (strict x) with neg | pos
  · have sumNeg : ∑ s ∈ level, MvPolynomial.eval (booleanReals (subsetBits s)) b < 0 :=
      Finset.sum_neg (fun s hs => lt_of_le_of_ne
        (le_of_not_gt fun z => (not_lt_of_gt neg) ((same s hs).mpr z)) (strict (subsetBits s))) nonempty
    have evalNeg : (averagePolynomial b).eval (grid n k) < 0 := by
      rcases mul_neg_iff.mp (average ▸ sumNeg) with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim ((not_lt_of_gt realChosen) h)
    exact mul_pos_of_neg_of_neg evalNeg neg
  · have sumPos : 0 < ∑ s ∈ level, MvPolynomial.eval (booleanReals (subsetBits s)) b :=
      Finset.sum_pos (fun s hs => (same s hs).mp pos) nonempty
    have evalPos : 0 < (averagePolynomial b).eval (grid n k) := by
      rcases mul_pos_iff.mp (average ▸ sumPos) with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact False.elim ((not_lt_of_gt realChosen) h)
    exact mul_pos evalPos pos

end
end AttentionSymmetry

#print axioms AttentionSymmetry.averagePolynomial_mul_eval
#print axioms AttentionSymmetry.exists_grid_sign
