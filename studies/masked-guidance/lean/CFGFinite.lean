import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs

/-! The rational jump generator at guidance strength one in the binary
counterexample to overlap suppression in masked discrete diffusion. -/

namespace CFGFinite

open scoped BigOperators

abbrev State (d : ℕ) := Fin d → Option Bool
abbrev Word (d : ℕ) := Fin d → Bool

def masked (d : ℕ) : State d := fun _ => none

def complete {d : ℕ} (x : Word d) : State d := fun j => some (x j)

def constant (d : ℕ) (b : Bool) : Word d := fun _ => b

def reveal {d : ℕ} (s : State d) (j : Fin d) (b : Bool) : State d :=
  fun i => if i = j then some b else s i

def compatible {d : ℕ} (s : State d) (x : Word d) : Bool :=
  decide (∀ j, s j = none ∨ s j = some (x j))

def Reachable {d : ℕ} (s : State d) : Prop :=
  compatible s (constant d false) = true ∨ compatible s (constant d true) = true

instance {d : ℕ} (s : State d) : Decidable (Reachable s) := by
  unfold Reachable
  infer_instance

def Incomplete {d : ℕ} (s : State d) : Prop := ∃ j, s j = none

instance {d : ℕ} (s : State d) : Decidable (Incomplete s) := by
  unfold Incomplete
  infer_instance

def targetWeight {d : ℕ} (x : Word d) : ℚ :=
  (if ∀ j, x j = false then 1 / 4 else 0) +
  (if ∀ j, x j = true then 3 / 4 else 0)

def otherWeight {d : ℕ} (x : Word d) : ℚ :=
  if ∀ j, x j = false then 0 else 1 / ((2 : ℚ) ^ d - 1)

def mixtureWeight {d : ℕ} (x : Word d) : ℚ := (targetWeight x + otherWeight x) / 2

def marginal {d : ℕ} (weight : Word d → ℚ) (s : State d) : ℚ :=
  ∑ x : Word d, if compatible s x then weight x else 0

def conditional {d : ℕ} (weight : Word d → ℚ) (s : State d) (j : Fin d) (b : Bool) : ℚ :=
  marginal weight (reveal s j b) / marginal weight s

/-- The time-independent multiplier of the guided reveal rate at guidance one.
Already visible coordinates have no reveal transition. A source state outside the
target support has zero target marginal and is assigned zero rates. On reachable
states every candidate target successor with positive mass also has positive
mixture mass. A zero-mass target successor has rate zero. -/
def rate {d : ℕ} (s : State d) (j : Fin d) (b : Bool) : ℚ :=
  if s j = none then
    (conditional targetWeight s j b) ^ 2 / conditional mixtureWeight s j b
  else 0

abbrev rate2 := @rate 2
abbrev rate3 := @rate 3

def exitRate {d : ℕ} (jump : State d → Fin d → Bool → ℚ) (s : State d) : ℚ :=
  ∑ j : Fin d, ∑ b : Bool, jump s j b

def generator {d : ℕ} (jump : State d → Fin d → Bool → ℚ)
    (h : State d → ℚ) (s : State d) : ℚ :=
  ∑ j : Fin d, ∑ b : Bool, jump s j b * (h (reveal s j b) - h s)

def posterior {d : ℕ} (s : State d) : ℚ :=
  marginal targetWeight s / (2 * marginal mixtureWeight s)

def masksRemaining {d : ℕ} (s : State d) : ℕ :=
  ∑ j : Fin d, if s j = none then 1 else 0

def harmonic {d : ℕ} (initial : ℚ) (s : State d) : ℚ :=
  if ∀ j, s j = none then initial
  else if compatible s (constant d true) then 1 else 0

def harmonic2 : State 2 → ℚ := harmonic (63 / 80)
def harmonic3 : State 3 → ℚ := harmonic (171 / 208)

set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem harmonic2_generator : ∀ s : State 2, Reachable s →
    generator rate2 harmonic2 s = 0 := by
  decide +kernel

theorem harmonic3_generator : ∀ s : State 3, Reachable s →
    generator rate3 harmonic3 s = 0 := by
  decide +kernel

theorem harmonic2_masked : harmonic2 (masked 2) = 63 / 80 := by
  decide +kernel

theorem harmonic3_masked : harmonic3 (masked 3) = 171 / 208 := by
  decide +kernel

theorem first2_rates : ∀ j : Fin 2,
    rate2 (masked 2) j false = 3 / 14 ∧ rate2 (masked 2) j true = 27 / 34 := by
  decide +kernel

theorem first3_rates : ∀ j : Fin 3,
    rate3 (masked 3) j false = 7 / 38 ∧ rate3 (masked 3) j true = 63 / 74 := by
  decide +kernel

theorem harmonic2_complete : ∀ b : Bool,
    harmonic2 (complete (constant 2 b)) = if b then 1 else 0 := by
  decide +kernel

theorem harmonic3_complete : ∀ b : Bool,
    harmonic3 (complete (constant 3 b)) = if b then 1 else 0 := by
  decide +kernel

theorem witness2_support :
    targetWeight (constant 2 false) = 1 / 4 ∧ otherWeight (constant 2 false) = 0 ∧
    targetWeight (constant 2 true) = 3 / 4 ∧ otherWeight (constant 2 true) = 1 / 3 := by
  decide +kernel

theorem witness3_support :
    targetWeight (constant 3 false) = 1 / 4 ∧ otherWeight (constant 3 false) = 0 ∧
    targetWeight (constant 3 true) = 3 / 4 ∧ otherWeight (constant 3 true) = 1 / 7 := by
  decide +kernel

theorem weights2_normalized :
    marginal (@targetWeight 2) (masked 2) = 1 ∧ marginal (@otherWeight 2) (masked 2) = 1 := by
  decide +kernel

theorem weights3_normalized :
    marginal (@targetWeight 3) (masked 3) = 1 ∧ marginal (@otherWeight 3) (masked 3) = 1 := by
  decide +kernel

theorem mask2_reachable : Reachable (masked 2) := by decide +kernel

theorem mask3_reachable : Reachable (masked 3) := by decide +kernel

theorem rate2_nonneg : ∀ (s : State 2) (j : Fin 2) (b : Bool), 0 ≤ rate2 s j b := by
  decide +kernel

theorem rate3_nonneg : ∀ (s : State 3) (j : Fin 3) (b : Bool), 0 ≤ rate3 s j b := by
  decide +kernel

theorem rate2_reachable : ∀ (s : State 2) (j : Fin 2) (b : Bool),
    Reachable s → 0 < rate2 s j b → Reachable (reveal s j b) := by
  decide +kernel

theorem rate3_reachable : ∀ (s : State 3) (j : Fin 3) (b : Bool),
    Reachable s → 0 < rate3 s j b → Reachable (reveal s j b) := by
  decide +kernel

theorem rate2_exit_pos : ∀ s : State 2, Reachable s → Incomplete s → 0 < exitRate rate2 s := by
  decide +kernel

theorem rate3_exit_pos : ∀ s : State 3, Reachable s → Incomplete s → 0 < exitRate rate3 s := by
  decide +kernel

theorem mixture2_marginal_pos : ∀ s : State 2, 0 < marginal mixtureWeight s := by
  decide +kernel

theorem mixture3_marginal_pos : ∀ s : State 3, 0 < marginal mixtureWeight s := by
  decide +kernel

theorem target2_marginal_pos_iff : ∀ s : State 2, 0 < marginal targetWeight s ↔ Reachable s := by
  decide +kernel

theorem target3_marginal_pos_iff : ∀ s : State 3, 0 < marginal targetWeight s ↔ Reachable s := by
  decide +kernel

theorem rate2_posterior_form : ∀ (s : State 2) (j : Fin 2) (b : Bool),
    Reachable s → s j = none →
    rate2 s j b = conditional targetWeight s j b * (posterior (reveal s j b) / posterior s) := by
  decide +kernel

theorem rate3_posterior_form : ∀ (s : State 3) (j : Fin 3) (b : Bool),
    Reachable s → s j = none →
    rate3 s j b = conditional targetWeight s j b * (posterior (reveal s j b) / posterior s) := by
  decide +kernel

theorem rate2_progress : ∀ (s : State 2) (j : Fin 2) (b : Bool), 0 < rate2 s j b →
    masksRemaining (reveal s j b) + 1 = masksRemaining s := by
  decide +kernel

theorem rate3_progress : ∀ (s : State 3) (j : Fin 3) (b : Bool), 0 < rate3 s j b →
    masksRemaining (reveal s j b) + 1 = masksRemaining s := by
  decide +kernel

theorem masks2_incomplete_iff : ∀ s : State 2, Incomplete s ↔ 0 < masksRemaining s := by
  decide +kernel

theorem masks3_incomplete_iff : ∀ s : State 3, Incomplete s ↔ 0 < masksRemaining s := by
  decide +kernel

def terminalShared {d : ℕ} (s : State d) : Prop := ∀ j, s j = some true

instance {d : ℕ} (s : State d) : Decidable (terminalShared s) := by
  unfold terminalShared
  infer_instance

theorem harmonic2_terminal : ∀ s : State 2, Reachable s → ¬ Incomplete s →
    harmonic2 s = if terminalShared s then 1 else 0 := by
  decide +kernel

theorem harmonic3_terminal : ∀ s : State 3, Reachable s → ¬ Incomplete s →
    harmonic3 s = if terminalShared s then 1 else 0 := by
  decide +kernel

/-- The probability of ending at the shared word in at most the given number
of jumps, with transition probabilities obtained by normalizing the rates. -/
def sharedWithin {d : ℕ} (jump : State d → Fin d → Bool → ℚ) : ℕ → State d → ℚ
  | 0, s => if terminalShared s then 1 else 0
  | n + 1, s =>
    if Incomplete s then
      (∑ j : Fin d, ∑ b : Bool,
        if jump s j b = 0 then 0 else jump s j b * sharedWithin jump n (reveal s j b)) /
          exitRate jump s
    else if terminalShared s then 1 else 0

theorem sharedWithin2_masked : sharedWithin rate2 2 (masked 2) = 63 / 80 := by
  decide +kernel

theorem sharedWithin3_masked : sharedWithin rate3 3 (masked 3) = 171 / 208 := by
  decide +kernel

theorem witness2_proper_projections_shared : ∀ (s : State 2) (b : Bool),
    Incomplete s → compatible s (constant 2 b) = true → 0 < marginal otherWeight s := by
  decide +kernel

theorem witness3_proper_projections_shared : ∀ (s : State 3) (b : Bool),
    Incomplete s → compatible s (constant 3 b) = true → 0 < marginal otherWeight s := by
  decide +kernel

/-- The relative weight on the class-private point is strictly smaller than
that on the shared point. In dimension two these are the paper's regions R3
and R4, respectively. The ratios use the harmonic value at the all-mask state,
with the private mass its complement. -/
theorem witness2_relative_weight_reversed :
    (1 - harmonic2 (masked 2)) / targetWeight (constant 2 false) <
    harmonic2 (masked 2) / targetWeight (constant 2 true) := by
  decide +kernel

theorem witness3_relative_weight_reversed :
    (1 - harmonic3 (masked 3)) / targetWeight (constant 3 false) <
    harmonic3 (masked 3) / targetWeight (constant 3 true) := by
  decide +kernel

end CFGFinite
