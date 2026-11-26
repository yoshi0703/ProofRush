import CFGClock

/-! A source-matched two-dimensional implication of the published ordering.
The two classes and the two comparison words are quantified. Full support
overlap and one-coordinate overlaps are calculated from the input tables. -/
namespace CFGOrdering
open CFGFinite
open scoped BigOperators

def mixture {d : ℕ} (p q : Word d → ℚ) (x : Word d) : ℚ := (p x + q x) / 2

def jump {d : ℕ} (p q : Word d → ℚ) (s : State d) (j : Fin d) (b : Bool) : ℚ :=
  if s j = none then (conditional p s j b)^2 / conditional (mixture p q) s j b else 0

def atWord {d : ℕ} (s : State d) (x : Word d) : ℚ :=
  if ∀ j, s j = some (x j) then 1 else 0

/-- Full path recursion using the rates of every available coordinate and token. -/
def terminal {d : ℕ} (rates : State d → Fin d → Bool → ℚ) (x : Word d) :
    ℕ → State d → ℚ
  | 0, s => atWord s x
  | n + 1, s =>
    if 0 < exitRate rates s then
      ∑ j : Fin d, ∑ b : Bool, (rates s j b / exitRate rates s) * terminal rates x n (reveal s j b)
    else atWord s x

noncomputable def integrated {d : ℕ} (rates : State d → Fin d → Bool → ℚ) (x : Word d) :
    ℕ → State d → ℝ
  | 0, s => (atWord s x : ℝ)
  | n + 1, s =>
    if 0 < exitRate rates s then
      ∑ j : Fin d, ∑ b : Bool, CFGClock.raceMass (exitRate rates s : ℝ) (rates s j b : ℝ) *
        integrated rates x n (reveal s j b)
    else (atWord s x : ℝ)

theorem integrated_terminal {d : ℕ} (rates : State d → Fin d → Bool → ℚ) (x : Word d)
    (n : ℕ) (s : State d) : integrated rates x n s = (terminal rates x n s : ℝ) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases h : 0 < exitRate rates s
    · have h' : 0 < (exitRate rates s : ℝ) := by exact_mod_cast h
      simp [integrated, terminal, h, CFGClock.raceMass_eq h', ih]
    · simp [integrated, terminal, h]

def Class2 (p : Word 2 → ℚ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ marginal p (masked 2) = 1 ∧ ∃ x, p x = 0

def projectionsShared (q : Word 2 → ℚ) (x : Word 2) : Prop :=
  ∀ j, 0 < marginal q (reveal (masked 2) j (x j))

/-- The R3/R4 consequence of Conjecture E.1 at dimension 2 and w = 1.
Class-1-only and shared comparison words have overlapping projections in
both coordinates. Allowing equality makes the universal claim weaker. -/
def PrivateWeightOrdering : Prop :=
  ∀ p q : Word 2 → ℚ, Class2 p → Class2 q →
    ∀ x y, 0 < p x → q x = 0 → projectionsShared q x →
      0 < p y → 0 < q y → projectionsShared q y →
      terminal (jump p q) x 2 (masked 2) / p x ≥
      terminal (jump p q) y 2 (masked 2) / p y

set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem diagonal_masses :
    terminal (jump targetWeight otherWeight) (constant 2 false) 2 (masked 2) = 17/80 ∧
    terminal (jump targetWeight otherWeight) (constant 2 true) 2 (masked 2) = 63/80 := by
  decide +kernel

theorem refutes_private_weight_ordering : ¬ PrivateWeightOrdering := by
  intro h
  have claim := h targetWeight otherWeight
    (by unfold Class2; decide +kernel) (by unfold Class2; decide +kernel)
    (constant 2 false) (constant 2 true)
    (by decide +kernel) (by decide +kernel) (by unfold projectionsShared; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold projectionsShared; decide +kernel)
  rw [diagonal_masses.1, diagonal_masses.2, witness2_support.1, witness2_support.2.2.1] at claim
  norm_num at claim

end CFGOrdering
