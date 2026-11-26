import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-! Finite parameter counting for monic rational charts. A localization at
the common denominator permits exactly the evaluations where that
denominator is nonzero. -/
namespace AttentionDimension

open MvPolynomial Algebra
open scoped BigOperators

universe u
variable {K : Type u} [Field K]

/-- Rational coordinate functions with a common denominator satisfy a
nonzero common polynomial relation once output dimension exceeds the
number of parameters. The relation vanishes at every defined value. -/
theorem exists_relation_ratio {m T : Nat} (dimension : m < T)
    (numerator : Fin T → MvPolynomial (Fin m) K)
    (denominator : MvPolynomial (Fin m) K) (nonzero : denominator ≠ 0) :
    ∃ relation : MvPolynomial (Fin T) K, relation ≠ 0 ∧
      ∀ x : Fin m → K, eval x denominator ≠ 0 →
        eval (fun i => eval x (numerator i) / eval x denominator) relation = 0 := by
  classical
  let P := MvPolynomial (Fin m) K
  let L := Localization.Away denominator
  let _ : IsDomain L := Localization.Away.isDomain nonzero
  let _ : FaithfulSMul P L := (faithfulSMul_iff_algebraMap_injective P L).mpr <|
    IsLocalization.injective L (powers_le_nonZeroDivisors_of_noZeroDivisors nonzero)
  let _ : Algebra.IsAlgebraic P L := IsLocalization.isAlgebraic L (Submonoid.powers denominator)
  have locDegree : Algebra.trdeg P L = 0 := trdeg_eq_zero
  have trdeg : Algebra.trdeg K L = (m : Cardinal) := by
    rw [← trdeg_add_eq K P, locDegree, add_zero]
    simp [P]
  let values : Fin T → L := fun i =>
    algebraMap P L (numerator i) * IsLocalization.Away.invSelf denominator
  have dep : ¬ Function.Injective (aeval values : MvPolynomial (Fin T) K →ₐ[K] L) := by
    intro injective
    have indep := algebraicIndependent_iff_injective_aeval.mpr injective
    have bound := indep.lift_cardinalMk_le_trdeg
    rw [trdeg] at bound
    have size : T ≤ m := by simpa using bound
    exact Nat.not_le_of_gt dimension size
  obtain ⟨r, s, eq, distinct⟩ := Function.not_injective_iff.mp dep
  have vanish : aeval values (r-s) = 0 := by rw [map_sub, eq, sub_self]
  refine ⟨r-s, sub_ne_zero.mpr distinct, ?_⟩
  intro x hx
  let e : P →ₐ[K] K := aeval x
  have hu : IsUnit (e denominator) := isUnit_iff_ne_zero.mpr hx
  let g : L →ₐ[K] K := IsLocalization.Away.liftAlgHom denominator hu
  have evalOriginal (p : P) : g (algebraMap P L p) = eval x p :=
    IsLocalization.Away.lift_eq denominator hu p
  have evalInverse : g (IsLocalization.Away.invSelf denominator) = (eval x denominator)⁻¹ := by
    have product : eval x denominator * g (IsLocalization.Away.invSelf denominator) = 1 := by
      rw [← evalOriginal, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    rw [← one_div]
    exact (eq_div_iff hx).mpr (by simpa [mul_comm] using product)
  have evalRatio (i : Fin T) : g (values i) = eval x (numerator i) / eval x denominator := by
    simp only [values, map_mul, evalOriginal, evalInverse, div_eq_mul_inv]
  have gZero := congrArg g vanish
  rw [comp_aeval_apply, map_zero] at gZero
  simpa only [evalRatio, aeval_eq_eval] using gZero

/-- The polynomial-coordinate special case. -/
theorem exists_relation_polynomial {m T : Nat} (dimension : m < T)
    (coordinate : Fin T → MvPolynomial (Fin m) K) :
    ∃ relation : MvPolynomial (Fin T) K, relation ≠ 0 ∧
      ∀ x : Fin m → K, eval (fun i => eval x (coordinate i)) relation = 0 := by
  obtain ⟨r, hr, result⟩ := exists_relation_ratio dimension coordinate 1 one_ne_zero
  exact ⟨r, hr, fun x => by simpa using result x (by simp)⟩

/-- A finite union of charts, with different parameter counts allowed, still
lies in a single proper polynomial zero set. A zero denominator polynomial
contributes no defined values. -/
theorem exists_relation_finite_charts {I : Type*} [Fintype I] {T : Nat}
    (m : I → Nat) (dimension : ∀ chart, m chart < T)
    (numerator : (chart : I) → Fin T → MvPolynomial (Fin (m chart)) K)
    (denominator : (chart : I) → MvPolynomial (Fin (m chart)) K) :
    ∃ relation : MvPolynomial (Fin T) K, relation ≠ 0 ∧
      ∀ (chart : I) (x : Fin (m chart) → K), eval x (denominator chart) ≠ 0 →
        eval (fun i => eval x (numerator chart i) / eval x (denominator chart)) relation = 0 := by
  classical
  have perChart (chart : I) : ∃ relation : MvPolynomial (Fin T) K, relation ≠ 0 ∧
      ∀ x : Fin (m chart) → K, eval x (denominator chart) ≠ 0 →
        eval (fun i => eval x (numerator chart i) / eval x (denominator chart)) relation = 0 := by
    by_cases empty : denominator chart = 0
    · exact ⟨1, one_ne_zero, fun _ h => by simp [empty] at h⟩
    · exact exists_relation_ratio (dimension chart) (numerator chart) (denominator chart) empty
  choose factors ne zero using perChart
  refine ⟨∏ chart, factors chart, Finset.prod_ne_zero_iff.mpr (fun chart _ => ne chart), ?_⟩
  intro chart x valid
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ chart) (zero chart x valid)

/-- A nonzero polynomial cannot vanish throughout a nonempty open subset
of a finite-dimensional real coefficient space. -/
theorem exists_nonzero_in_open {T : Nat} {p : MvPolynomial (Fin T) ℝ} (ne : p ≠ 0)
    (U : Set (Fin T → ℝ)) (op : IsOpen U) (nonempty : U.Nonempty) :
    ∃ x ∈ U, eval x p ≠ 0 := by
  classical
  by_contra! vanishes
  obtain ⟨center, belongs⟩ := nonempty
  obtain ⟨radius, pos, small⟩ := Metric.isOpen_iff.mp op center belongs
  let sides : Fin T → Set ℝ := fun i => Set.Ioo (center i - radius) (center i + radius)
  have infinite : ∀ i, (sides i).Infinite := by
    intro i
    apply Set.Ioo_infinite
    exact (sub_lt_self _ pos).trans (lt_add_of_pos_right _ pos)
  apply ne
  apply MvPolynomial.funext_set sides infinite
  intro point pointBox
  have inBall : point ∈ Metric.ball center radius := by
    rw [ball_pi center pos]
    intro i _
    have side := pointBox i (Set.mem_univ i)
    simpa only [Real.ball_eq_Ioo, sides] using side
  simpa using vanishes point (small inBall)

/-- Every nonempty open real coefficient set contains a point outside all
defined values of finitely many underparameterized rational charts. -/
theorem open_contains_unrealizable {I : Type*} [Fintype I] {T : Nat}
    (m : I → Nat) (dimension : ∀ chart, m chart < T)
    (numerator : (chart : I) → Fin T → MvPolynomial (Fin (m chart)) ℝ)
    (denominator : (chart : I) → MvPolynomial (Fin (m chart)) ℝ)
    (U : Set (Fin T → ℝ)) (op : IsOpen U) (nonempty : U.Nonempty) :
    ∃ point ∈ U, ∀ (chart : I) (x : Fin (m chart) → ℝ), eval x (denominator chart) ≠ 0 →
      (fun i => eval x (numerator chart i) / eval x (denominator chart)) ≠ point := by
  obtain ⟨relation, ne, vanishes⟩ := exists_relation_finite_charts m dimension numerator denominator
  obtain ⟨point, member, nonzero⟩ := exists_nonzero_in_open ne U op nonempty
  refine ⟨point, member, fun chart x valid eq => nonzero ?_⟩
  rw [← eq]
  exact vanishes chart x valid

#print axioms exists_relation_ratio
#print axioms exists_relation_polynomial
#print axioms exists_relation_finite_charts
#print axioms exists_nonzero_in_open
#print axioms open_contains_unrealizable

end AttentionDimension
