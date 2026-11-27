import Mathlib.Tactic

namespace SmokeTest

/-- Minimal smoke-test proposition to verify the ProofRush Lean 4 + Mathlib harness. -/
def SmokeStatement : Prop :=
  ∀ n : ℕ, n + 0 = n ∧ (n + 1) ^ 2 = n ^ 2 + 2 * n + 1

end SmokeTest
