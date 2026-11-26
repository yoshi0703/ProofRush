import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Rational windows on a common Hamming-weight grid and a strict
polynomial threshold realizing one sign change per window. -/
namespace AttentionGrid

open Polynomial
open scoped BigOperators

noncomputable def grid (n k : Nat) : ℝ := (k : ℝ) / n

def commonDenominator {T : Nat} (left right : Fin T → ℚ) : Nat :=
  (∏ i, (left i).den) * ∏ i, (right i).den

def gridIndex (n : Nat) (q : ℚ) : Nat :=
  q.num.toNat * (n / q.den)

theorem commonDenominator_pos {T : Nat} (left right : Fin T → ℚ) :
    0 < commonDenominator left right := by
  unfold commonDenominator
  exact Nat.mul_pos (Finset.prod_pos (fun i _ => (left i).den_pos))
    (Finset.prod_pos (fun i _ => (right i).den_pos))

theorem left_den_dvd {T : Nat} (left right : Fin T → ℚ) (i : Fin T) :
    (left i).den ∣ commonDenominator left right := by
  unfold commonDenominator
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun j => (left j).den) (Finset.mem_univ i)) _

theorem right_den_dvd {T : Nat} (left right : Fin T → ℚ) (i : Fin T) :
    (right i).den ∣ commonDenominator left right := by
  unfold commonDenominator
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => (right j).den) (Finset.mem_univ i)) _

theorem gridIndex_spec {n : Nat} (hn : 0 < n) {q : ℚ}
    (q0 : 0 ≤ q) (divides : q.den ∣ n) :
    grid n (gridIndex n q) = (q : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have denR : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have numerator : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr q0)
  have factor : ((n / q.den : Nat) : ℝ) * (q.den : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel divides
  unfold grid gridIndex
  rw [Nat.cast_mul, numerator, Rat.cast_def, div_eq_div_iff hnR denR, mul_assoc, factor]

theorem gridIndex_le {n : Nat} (hn : 0 < n) {q : ℚ}
    (q0 : 0 ≤ q) (q1 : q ≤ 1) (divides : q.den ∣ n) : gridIndex n q ≤ n := by
  have below : grid n (gridIndex n q) ≤ 1 := by
    rw [gridIndex_spec hn q0 divides]
    exact_mod_cast q1
  have nPos : (0 : ℝ) < n := by exact_mod_cast hn
  have result := (div_le_iff₀ nPos).mp below
  exact_mod_cast (by simpa using result : (gridIndex n q : ℝ) ≤ n)

/-- The midpoint between two consecutive grid positions. The expression
is rational when the two inputs are natural numbers. -/
noncomputable def halfGrid (n k : Nat) : ℝ := ((k : ℝ) + 1 / 2) / n

theorem halfGrid_rational (n k : Nat) : ∃ q : ℚ, (q : ℝ) = halfGrid n k := by
  exact ⟨((k : ℚ) + 1 / 2) / n, by norm_num [halfGrid, Rat.cast_div]⟩

theorem halfGrid_not_grid {n : Nat} (hn : 0 < n) (j k : Nat) :
    grid n k ≠ halfGrid n j := by
  intro eq
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have doubled : (k : ℝ) = (j : ℝ) + 1 / 2 := (div_left_inj₀ hnR).mp eq
  have impossible : ((2*k : Nat) : ℝ) = ((2*j+1 : Nat) : ℝ) := by
    push_cast
    linarith
  have same : 2*k = 2*j+1 := by exact_mod_cast impossible
  omega

theorem grid_lt_halfGrid {n : Nat} (hn : 0 < n) (j : Nat) :
    grid n j < halfGrid n j := by
  have nPos : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_lt_div_iff_of_pos_right nPos).mpr (by linarith)

theorem halfGrid_lt_grid {n j k : Nat} (hn : 0 < n) (between : grid n j < grid n k) :
    halfGrid n j < grid n k := by
  have nPos : (0 : ℝ) < n := by exact_mod_cast hn
  have ji : (j : ℝ) < k := (div_lt_div_iff_of_pos_right nPos).mp between
  have integer : j < k := by exact_mod_cast ji
  have distance : (j : ℝ) + 1 ≤ k := by
    exact_mod_cast (Nat.succ_le_of_lt integer)
  apply (div_lt_div_iff_of_pos_right nPos).mpr
  linarith

noncomputable def target {T : Nat} (roots : Fin T → ℝ) : ℝ[X] :=
  ∏ j, (X - C (roots j))

theorem target_monic {T : Nat} (roots : Fin T → ℝ) : (target roots).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (roots i))

theorem target_degree {T : Nat} (roots : Fin T → ℝ) : (target roots).natDegree = T := by
  unfold target
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (roots i))]
  simp

theorem target_eval {T : Nat} (roots : Fin T → ℝ) (x : ℝ) :
    (target roots).eval x = ∏ i, (x - roots i) := by
  simp [target, eval_prod]

theorem target_eval_ne_zero {T : Nat} {roots : Fin T → ℝ} {x : ℝ}
    (avoid : ∀ i, x ≠ roots i) : (target roots).eval x ≠ 0 := by
  rw [target_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (avoid i))

/-- Multiply the two evaluations. The factor corresponding to the root
inside the window is negative, and every factor for another root is positive. -/
theorem target_opposite {T : Nat} (left right roots : Fin T → ℝ)
    (inside : ∀ i, left i < roots i ∧ roots i < right i)
    (separation : ∀ i j, i < j → right i < left j) (i : Fin T) :
    (target roots).eval (left i) * (target roots).eval (right i) < 0 := by
  classical
  rw [target_eval, target_eval, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (sub_neg.mpr (inside i).1) (sub_pos.mpr (inside i).2)
  · apply Finset.prod_pos
    intro j mem
    have different : j ≠ i := (Finset.mem_erase.mp mem).1
    rcases lt_or_gt_of_ne different with before | after
    · have rLeft := ((inside j).2.trans (separation j i before))
      exact mul_pos (sub_pos.mpr rLeft) (sub_pos.mpr (rLeft.trans ((inside i).1.trans (inside i).2)))
    · have rRight := (separation i j after).trans (inside j).1
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (((inside i).1.trans (inside i).2).trans rRight))
        (sub_neg.mpr rRight)

/-- Explicit realization of any ordered, strictly separated rational
windows in (0,1) by a degree-T polynomial on one Hamming-weight grid. -/
theorem exists_product_grid_with_sign_changes {T : Nat} (left right : Fin T → ℚ)
    (positive : ∀ i, 0 < left i) (window : ∀ i, left i < right i)
    (belowOne : ∀ i, right i < 1)
    (separated : ∀ i j, i < j → right i < left j) :
    ∃ n : Nat, 0 < n ∧ ∃ L R : Fin T → Fin (n+1),
      (∀ i, grid n (L i) = (left i : ℝ) ∧ grid n (R i) = (right i : ℝ)) ∧
      ∃ roots : Fin T → ℝ,
        (∀ k : Fin (n+1), (target roots).eval (grid n k) ≠ 0) ∧
        ∀ i, (target roots).eval (grid n (L i)) * (target roots).eval (grid n (R i)) < 0 := by
  let n := commonDenominator left right
  have hn := commonDenominator_pos left right
  let L : Fin T → Fin (n+1) := fun i => ⟨gridIndex n (left i),
    Nat.lt_succ_of_le (gridIndex_le hn (positive i).le
      ((window i).trans (belowOne i)).le (left_den_dvd left right i))⟩
  let R : Fin T → Fin (n+1) := fun i => ⟨gridIndex n (right i),
    Nat.lt_succ_of_le (gridIndex_le hn ((positive i).trans (window i)).le
      (belowOne i).le (right_den_dvd left right i))⟩
  have leftEq (i : Fin T) : grid n (L i) = (left i : ℝ) :=
    gridIndex_spec hn (positive i).le (left_den_dvd left right i)
  have rightEq (i : Fin T) : grid n (R i) = (right i : ℝ) :=
    gridIndex_spec hn ((positive i).trans (window i)).le (right_den_dvd left right i)
  let root : Fin T → ℝ := fun i => halfGrid n (L i)
  refine ⟨n, hn, L, R, fun i => ⟨leftEq i, rightEq i⟩, root, ?_, ?_⟩
  · intro k
    exact target_eval_ne_zero (fun i => halfGrid_not_grid hn (L i) k)
  · intro i
    apply target_opposite (fun j => grid n (L j)) (fun j => grid n (R j)) root
    · intro j
      exact ⟨grid_lt_halfGrid hn (L j), halfGrid_lt_grid hn (by
        rw [leftEq, rightEq]
        exact_mod_cast window j)⟩
    · intro a b hab
      rw [rightEq, leftEq]
      exact_mod_cast separated a b hab

theorem exists_grid_with_sign_changes {T : Nat} (left right : Fin T → ℚ)
    (positive : ∀ i, 0 < left i) (window : ∀ i, left i < right i)
    (belowOne : ∀ i, right i < 1)
    (separated : ∀ i j, i < j → right i < left j) :
    ∃ n : Nat, 0 < n ∧ ∃ L R : Fin T → Fin (n+1),
      (∀ i, grid n (L i) = (left i : ℝ) ∧ grid n (R i) = (right i : ℝ)) ∧
      ∃ p : ℝ[X], p.Monic ∧ p.natDegree = T ∧
        (∀ k : Fin (n+1), p.eval (grid n k) ≠ 0) ∧
        ∀ i, p.eval (grid n (L i)) * p.eval (grid n (R i)) < 0 := by
  obtain ⟨n, hn, L, R, points, roots, strict, changes⟩ :=
    exists_product_grid_with_sign_changes left right positive window belowOne separated
  exact ⟨n, hn, L, R, points, target roots, target_monic roots, target_degree roots, strict, changes⟩

/-- Strict positive products express sign agreement without a convention at zero. -/
def agreesOnGrid (n : Nat) (target model : ℝ[X]) : Prop :=
  ∀ k : Fin (n+1), 0 < target.eval (grid n k) * model.eval (grid n k)

theorem opposite_of_agreesOnGrid {n : Nat} {target model : ℝ[X]} (left right : Fin (n+1))
    (opposite : target.eval (grid n left) * target.eval (grid n right) < 0)
    (agrees : agreesOnGrid n target model) :
    model.eval (grid n left) * model.eval (grid n right) < 0 := by
  have both := mul_pos (agrees left) (agrees right)
  rw [← mul_mul_mul_comm] at both
  rcases mul_pos_iff.mp both with positive | negative
  · exact False.elim ((not_lt_of_ge opposite.le) positive.1)
  · exact negative.2

private theorem finitePositive_margin {I : Type*} [Fintype I] (f : I → ℝ) (positive : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ < f i := by
  classical
  have onFinset (indices : Finset I) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ indices, δ < f i := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | insert i rest fresh ih =>
      obtain ⟨δ, pos, small⟩ := ih
      have half : 0 < f i / 2 := by linarith [positive i]
      refine ⟨min δ (f i / 2), lt_min pos half, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | later
      · exact (min_le_right ..).trans_lt (by linarith [positive j])
      · exact (min_le_left ..).trans_lt (small j later)
  obtain ⟨δ, hp, small⟩ := onFinset Finset.univ
  exact ⟨δ, hp, fun j => small j (Finset.mem_univ j)⟩

/-- Turns a convention assigning zero to the positive class into strict
grid agreement. A model with an adjustable bias and a positive common
denominator can supply that denominator as the adjustment direction. -/
theorem exists_positive_shift {n : Nat} {target model direction : ℝ[X]}
    (strict : ∀ k : Fin (n+1), target.eval (grid n k) ≠ 0)
    (weak : ∀ k : Fin (n+1), 0 < target.eval (grid n k) ↔ 0 ≤ model.eval (grid n k))
    (directionPos : ∀ k : Fin (n+1), 0 < direction.eval (grid n k)) :
    ∃ δ : ℝ, 0 < δ ∧ agreesOnGrid n target (model + C δ * direction) ∧
      (model + C δ * direction).natDegree ≤ max model.natDegree direction.natDegree := by
  let margin : Fin (n+1) → ℝ := fun k =>
    if model.eval (grid n k) < 0 then -model.eval (grid n k) / direction.eval (grid n k) else 1
  have positive (k : Fin (n+1)) : 0 < margin k := by
    unfold margin
    split
    · rename_i negative
      exact div_pos (neg_pos.mpr negative) (directionPos k)
    · exact zero_lt_one
  obtain ⟨δ, δPos, small⟩ := finitePositive_margin margin positive
  refine ⟨δ, δPos, ?_, ?_⟩
  · intro k
    rw [eval_add, eval_mul, eval_C]
    rcases lt_or_gt_of_ne (strict k) with negative | positive
    · have modelNegative : model.eval (grid n k) < 0 :=
        lt_of_not_ge (fun nonneg => (not_lt_of_ge negative.le) ((weak k).mpr nonneg))
      have marginBound : δ < -model.eval (grid n k) / direction.eval (grid n k) := by
        simpa [margin, modelNegative] using small k
      have product := (lt_div_iff₀ (directionPos k)).mp marginBound
      exact mul_pos_of_neg_of_neg negative (by linarith)
    · have modelNonneg := (weak k).mp positive
      exact mul_pos positive (add_pos_of_nonneg_of_pos modelNonneg (mul_pos δPos (directionPos k)))
  · apply (natDegree_add_le _ _).trans
    apply max_le_max le_rfl
    exact (natDegree_mul_le).trans_eq (by simp)

def hammingWeight {n : Nat} (bits : Fin n → Bool) : Nat :=
  (Finset.univ.filter (fun i => bits i)).card

theorem hammingWeight_le {n : Nat} (bits : Fin n → Bool) : hammingWeight bits ≤ n := by
  simpa [hammingWeight] using Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => bits i)

def bitsAtWeight {n : Nat} (k : Fin (n+1)) : Fin n → Bool :=
  fun i => decide (i.val < k.val)

theorem hammingWeight_bitsAtWeight {n : Nat} (k : Fin (n+1)) :
    hammingWeight (bitsAtWeight k) = k.val := by
  have le : k.val ≤ n := Nat.le_of_lt_succ k.isLt
  simp [hammingWeight, bitsAtWeight, Fin.card_filter_val_lt, Nat.min_eq_right le]

def booleanReals {n : Nat} (bits : Fin n → Bool) : Fin n → ℝ :=
  fun i => if bits i then 1 else 0

noncomputable def averageVariables (n : Nat) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (n : ℝ)⁻¹ * ∑ i : Fin n, MvPolynomial.X i

noncomputable def booleanTarget {T : Nat} (n : Nat) (roots : Fin T → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i, (averageVariables n - MvPolynomial.C (roots i))

theorem averageVariables_degree (n : Nat) : (averageVariables n).totalDegree ≤ 1 := by
  unfold averageVariables
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  exact MvPolynomial.totalDegree_finsetSum_le (fun _ _ => by simp)

theorem booleanTarget_degree {T n : Nat} (roots : Fin T → ℝ) :
    (booleanTarget n roots).totalDegree ≤ T := by
  classical
  unfold booleanTarget
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin T, (1 : Nat) := Finset.sum_le_sum (fun i _ => by
      exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (averageVariables_degree n))
    _ = T := by simp

theorem averageVariables_eval {n : Nat} (bits : Fin n → Bool) :
    MvPolynomial.eval (booleanReals bits) (averageVariables n) = grid n (hammingWeight bits) := by
  unfold averageVariables booleanReals hammingWeight grid
  simp only [map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, Finset.sum_boole,
    div_eq_mul_inv, mul_comm]

theorem booleanTarget_eval {T n : Nat} (roots : Fin T → ℝ) (bits : Fin n → Bool) :
    MvPolynomial.eval (booleanReals bits) (booleanTarget n roots) =
      (target roots).eval (grid n (hammingWeight bits)) := by
  simp [booleanTarget, target_eval, map_prod, averageVariables_eval]

theorem booleanTarget_symmetric {T n : Nat} (roots : Fin T → ℝ) {bits other : Fin n → Bool}
    (weight : hammingWeight bits = hammingWeight other) :
    MvPolynomial.eval (booleanReals bits) (booleanTarget n roots) =
      MvPolynomial.eval (booleanReals other) (booleanTarget n roots) := by
  rw [booleanTarget_eval, booleanTarget_eval, weight]

theorem booleanTarget_strict {T n : Nat} (roots : Fin T → ℝ)
    (gridStrict : ∀ k : Fin (n+1), (target roots).eval (grid n k) ≠ 0) (bits : Fin n → Bool) :
    MvPolynomial.eval (booleanReals bits) (booleanTarget n roots) ≠ 0 := by
  rw [booleanTarget_eval]
  exact gridStrict ⟨hammingWeight bits, Nat.lt_succ_of_le (hammingWeight_le bits)⟩

/-- Packages the same grid target with an actual degree-bounded polynomial
in the Boolean coordinates. Evaluation depends only on Hamming weight. -/
theorem exists_boolean_grid_with_sign_changes {T : Nat} (left right : Fin T → ℚ)
    (positive : ∀ i, 0 < left i) (window : ∀ i, left i < right i)
    (belowOne : ∀ i, right i < 1) (separated : ∀ i j, i < j → right i < left j) :
    ∃ n : Nat, 0 < n ∧ ∃ L R : Fin T → Fin (n+1),
      (∀ i, grid n (L i) = (left i : ℝ) ∧ grid n (R i) = (right i : ℝ)) ∧
      ∃ (p : ℝ[X]) (b : MvPolynomial (Fin n) ℝ), p.Monic ∧ p.natDegree = T ∧
        b.totalDegree ≤ T ∧ (∀ bits : Fin n → Bool,
          MvPolynomial.eval (booleanReals bits) b = p.eval (grid n (hammingWeight bits))) ∧
        (∀ k : Fin (n+1), p.eval (grid n k) ≠ 0) ∧
        ∀ i, p.eval (grid n (L i)) * p.eval (grid n (R i)) < 0 := by
  obtain ⟨n, hn, L, R, points, roots, strict, changes⟩ :=
    exists_product_grid_with_sign_changes left right positive window belowOne separated
  exact ⟨n, hn, L, R, points, target roots, booleanTarget n roots, target_monic roots,
    target_degree roots, booleanTarget_degree roots, booleanTarget_eval roots, strict, changes⟩

theorem agreesOnGrid_of_boolean {n : Nat} {target model : ℝ[X]}
    {b : MvPolynomial (Fin n) ℝ}
    (evals : ∀ bits : Fin n → Bool,
      MvPolynomial.eval (booleanReals bits) b = target.eval (grid n (hammingWeight bits)))
    (matchesBits : ∀ bits : Fin n → Bool, 0 < MvPolynomial.eval (booleanReals bits) b *
      model.eval (grid n (hammingWeight bits))) : agreesOnGrid n target model := by
  intro k
  simpa only [evals, hammingWeight_bitsAtWeight] using matchesBits (bitsAtWeight k)

#print axioms exists_grid_with_sign_changes
#print axioms opposite_of_agreesOnGrid
#print axioms exists_positive_shift
#print axioms booleanTarget_degree
#print axioms booleanTarget_symmetric
#print axioms booleanTarget_strict
#print axioms exists_boolean_grid_with_sign_changes
#print axioms agreesOnGrid_of_boolean

end AttentionGrid
