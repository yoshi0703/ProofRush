import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Funext

/-! A polynomial coefficient chart for a degree-D readout over d rational
coordinates with a common degree-H denominator. The monomial enumeration is
an explicit input, so no completeness or cardinality assumption is hidden. -/
namespace AttentionChart
open scoped BigOperators
open Polynomial MvPolynomial
noncomputable section

variable (H D d M : Nat)

abbrev Parameter := ((Fin (d+1) × Fin (H+1)) ⊕ Fin M)
abbrev Count := (d+1)*(H+1)+M

def index : Parameter H d M ≃ Fin (Count H d M) := by
  have h : Fintype.card (Parameter H d M) = Count H d M := by simp [Parameter, Count]
  exact (Fintype.equivFin (Parameter H d M)).trans (finCongr h)

abbrev A := MvPolynomial (Fin (Count H d M)) ℝ

def coordinate (row : Fin (d+1)) : Polynomial (A H d M) :=
  ∑ j : Fin (H+1), Polynomial.C (MvPolynomial.X (index H d M (.inl (row,j)))) * Polynomial.X ^ j.val

def q : Polynomial (A H d M) := coordinate H d M 0

def p (i : Fin d) : Polynomial (A H d M) := coordinate H d M i.succ

def weight (k : Fin M) : A H d M := MvPolynomial.X (index H d M (.inr k))

def mass (exponent : Fin M → Fin d → Nat) (k : Fin M) : Nat := ∑ i, exponent k i

def numerator (exponent : Fin M → Fin d → Nat) : Polynomial (A H d M) :=
  ∑ k, Polynomial.C (weight H d M k) * q H d M ^ (D - mass d M exponent k) *
    ∏ i, p H d M i ^ exponent k i

def coefficient (exponent : Fin M → Fin d → Nat) (j : Nat) : A H d M :=
  (numerator H D d M exponent).coeff j

/-- Parameters can be supplied directly by a finite coefficient array and
readout weights; the equivalence merely flattens them into Fin m. -/
def assignment (values : Parameter H d M → ℝ) : Fin (Count H d M) → ℝ :=
  fun i => values ((index H d M).symm i)

def evaluatedCoordinate (values : Parameter H d M → ℝ) (row : Fin (d+1)) : Polynomial ℝ :=
  ∑ j : Fin (H+1), Polynomial.C (values (.inl (row,j))) * Polynomial.X ^ j.val

def evaluatedNumerator (values : Parameter H d M → ℝ) (exponent : Fin M → Fin d → Nat) : Polynomial ℝ :=
  ∑ k, Polynomial.C (values (.inr k)) * evaluatedCoordinate H d M values 0 ^ (D - mass d M exponent k) *
    ∏ i, evaluatedCoordinate H d M values i.succ ^ exponent k i

theorem map_coordinate (values : Parameter H d M → ℝ) (row : Fin (d+1)) :
    Polynomial.map (MvPolynomial.eval (assignment H d M values)) (coordinate H d M row) =
      evaluatedCoordinate H d M values row := by
  simp [coordinate, evaluatedCoordinate, Polynomial.map_sum, assignment]

theorem map_numerator (values : Parameter H d M → ℝ) (exponent : Fin M → Fin d → Nat) :
    Polynomial.map (MvPolynomial.eval (assignment H d M values)) (numerator H D d M exponent) =
      evaluatedNumerator H D d M values exponent := by
  simp [numerator, evaluatedNumerator, Polynomial.map_sum, Polynomial.map_prod, q, p, weight, assignment, map_coordinate]

theorem coefficient_evaluation (values : Parameter H d M → ℝ)
    (exponent : Fin M → Fin d → Nat) (j : Nat) :
    MvPolynomial.eval (assignment H d M values) (coefficient H D d M exponent j) =
      (evaluatedNumerator H D d M values exponent).coeff j := by
  rw [coefficient, ← Polynomial.coeff_map, map_numerator]

def coefficients (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ) : Parameter H d M → ℝ
  | .inl (row,j) => (ps row).coeff j.val
  | .inr k => weights k

theorem reconstructed (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ)
    (bounded : ∀ row, (ps row).natDegree ≤ H) (row : Fin (d+1)) :
    evaluatedCoordinate H d M (coefficients H d M ps weights) row = ps row := by
  simp only [evaluatedCoordinate, coefficients]
  change (∑ j : Fin (H+1), (fun n : Nat => Polynomial.C ((ps row).coeff n) * Polynomial.X ^ n) j.val) = ps row
  rw [Fin.sum_univ_eq_sum_range (fun n : Nat => Polynomial.C ((ps row).coeff n) * Polynomial.X ^ n) (H+1)]
  exact ((ps row).as_sum_range_C_mul_X_pow' (by have := bounded row; omega)).symm

theorem chart_covers (ps : Fin (d+1) → Polynomial ℝ) (weights : Fin M → ℝ)
    (bounded : ∀ row, (ps row).natDegree ≤ H) (exponent : Fin M → Fin d → Nat) (j : Nat) :
    MvPolynomial.eval (assignment H d M (coefficients H d M ps weights))
      (coefficient H D d M exponent j) =
      (∑ k, Polynomial.C (weights k) * ps 0 ^ (D - mass d M exponent k) *
        ∏ i, ps i.succ ^ exponent k i).coeff j := by
  rw [coefficient_evaluation]
  simp [evaluatedNumerator, coefficients, reconstructed H d M ps weights bounded]

end
end AttentionChart
