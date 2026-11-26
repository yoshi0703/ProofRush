import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Canonne

open scoped BigOperators
noncomputable section

/-- A sorted probability mass function on a countable alphabet. -/
structure Law (p : ℕ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sorted : Antitone p
  total : HasSum p 1

/-- Index of the last retained coordinate. Index zero is the largest atom. -/
def Cut (p : ℕ → ℝ) (u : ℝ) (k : ℕ) : Prop :=
  1 - u ≤ ∑ i ∈ Finset.range (k + 1), p i ∧
    (k = 0 ∨ (∑ i ∈ Finset.range k, p i) < 1 - u)

def powerSum (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (p (i + 1)) ^ (2 / 3 : ℝ)

def phiAt (p : ℕ → ℝ) (k : ℕ) : ℝ := (powerSum p k) ^ (3 / 2 : ℝ)

def ell2 (z : ℕ → ℝ) : ℝ := Real.sqrt (∑' i, z i ^ 2)

/-- A bounded vector that captures the required mass in the dual problem. -/
structure Feasible (p : ℕ → ℝ) (u : ℝ) (z : ℕ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ z i
  le_one : ∀ i, z i ≤ 1
  energy : Summable (fun i => z i ^ 2)
  capture : 1 - u ≤ ∑' i, p i * z i

def costs (p : ℕ → ℝ) (t : ℝ) : Set ℝ :=
  {v | ∃ a b : ℕ → ℝ, (∀ i, a i + b i = p i) ∧
    Summable (fun i => |a i|) ∧ Summable (fun i => b i ^ 2) ∧
    v = (∑' i, |a i|) + t * ell2 b}

def peetre (p : ℕ → ℝ) (t : ℝ) : ℝ := sInf (costs p t)

/-- Left endpoint of the level set of the original Peetre K functional. -/
def inverseK (p : ℕ → ℝ) (u : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ 1 - u ≤ peetre p t}

end
end Canonne
