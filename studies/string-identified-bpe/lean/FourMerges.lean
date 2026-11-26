import SpellingBPE

namespace SpellingWitness
open SpellingBPE

/-- a^n over an alphabet consisting of only one letter. -/
def unary (n : ℕ) : Token Unit := List.replicate n ()

def input : Word Unit := [8,4,2,1,1,8,2,2,4,4,4,8,8,8].map unary

def pairOf (p : ℕ × ℕ) : Pair Unit := (unary p.1,unary p.2)

def slow : List (Pair Unit) := [(8,4),(12,2),(14,1),(15,1)].map pairOf
def fast : List (Pair Unit) := [(1,1),(2,2),(4,4),(8,8)].map pairOf

def gains (w : Word Unit) : List (Pair Unit) → List ℕ
  | [] => []
  | p::ps => gain p w :: gains (full p w) ps

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem actual_greedy : Greedy 4 input (play input slow) :=
  greedy_checked input slow (by decide +kernel)

theorem actual_comparator : Feasible 4 input (play input fast) := plays_feasible input fast

theorem slow_saves : input.length - (play input slow).length = 4 := by decide +kernel
theorem fast_saves : input.length - (play input fast).length = 10 := by decide +kernel

theorem histories : gains input slow = [1,1,1,1] ∧
    gains input fast = [1,2,3,4] ∧ play input fast = [16,16,16,16].map unary := by
  decide +kernel

theorem initial_atoms_present : ∀ s ∈ input, s ≠ [] := by decide +kernel

/-- The factors (a,a) and (aa) have identical literal spelling and different
factorisations. Both must occur in the actual input under the source definition. -/
theorem ambiguous : ¬UniqueDecoding input := by
  intro h
  have aa : Factor [unary 1,unary 1] input :=
    ⟨[8,4,2].map unary, [8,2,2,4,4,4,8,8,8].map unary, by decide +kernel⟩
  have two : Factor [unary 2] input :=
    ⟨[8,4].map unary, [1,1,8,2,2,4,4,4,8,8,8].map unary, by decide +kernel⟩
  have eq := h _ _ aa two (by decide +kernel)
  have len := congrArg List.length eq
  contradiction

theorem optimum_at_least_ten : 10 ≤ optimum input 4 := by
  rw [← fast_saves]
  exact feasible_le_optimum le_rfl actual_comparator

/-- Direct negation of the approximation guarantee, with the original
non-overlap count, all tie choices, and unrestricted partial-rule optimum. -/
theorem refutes_extension : ¬Extension Unit := by
  intro proposed
  have h := proposed input 4 (play input slow) (by decide) initial_atoms_present actual_greedy
  rw [slow_saves] at h
  have violation : 2 * 4^4 * 4 < (4^4-(4-2)^4)*10 := by decide
  have hopt := optimum_at_least_ten
  omega

end SpellingWitness
