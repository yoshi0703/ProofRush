import ForestLabels
import Mathlib.Tactic.Linarith

/-! Arithmetic consequence of the forest and original-adjacency estimates.
    Hypotheses are stated explicitly; this module does not assert that a
    comparator execution has already supplied the path estimates. -/
namespace BPEForest

theorem sqrt_budget_arithmetic (s k C U E N G : Nat)
    (hs : 0 < s) (hk : k ≤ s*s)
    (hn : N ≤ 2*C+U)
    (hc : C ≤ 5*G)
    (he : E ≤ (3+4*s)*G)
    (hu : s*U ≤ s*E+4*s*C+4*k*C) :
    N ≤ 57*s*G := by
  have h1 := Nat.mul_le_mul_left s hn
  have h2 := Nat.mul_le_mul_left s he
  have h3 := Nat.mul_le_mul_left (6*s+4*k) hc
  have h4 := Nat.mul_le_mul_right (20*G) hk
  nlinarith

end BPEForest
