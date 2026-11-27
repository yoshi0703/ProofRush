import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #30 — Sidon Sets

Formal problem statement faithfully matching `erdosproblems.com/30` and
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/30.lean`).

Let $h(N)$ denote the maximum cardinality of a Sidon set contained in $\{1, \dots, N\}$.
The open \$1,000 Erdős–Turán conjecture asks whether for every $\varepsilon > 0$,
$$h(N) = \sqrt{N} + O_\varepsilon(N^\varepsilon).$$
-/

namespace Erdos030

open Filter
open scoped Asymptotics

/-- A set of natural numbers is a Sidon set ($B_2$-set) if every sum $a + b$ has at most one
unordered representation with $a, b \in A$. Formulated purely with addition to avoid `ℕ`
truncated-subtraction artifacts. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ a₂ ∈ A, ∀ b₂ ∈ A,
    a₁ + b₁ = a₂ + b₂ → (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂)

/-- Maximum cardinality of a Sidon subset of a finite set `S : Finset ℕ`. -/
noncomputable def maxSidonSubsetCard (S : Finset ℕ) : ℕ :=
  letI := Classical.decPred (fun A : Finset ℕ => IsSidon (A : Set ℕ))
  (S.powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))).sup Finset.card

/-- `h N` is the maximum size of a Sidon set in `{1, ..., N}`. -/
noncomputable def h (N : ℕ) : ℕ :=
  maxSidonSubsetCard (Finset.Icc 1 N)

/-- Open Erdős Problem #30 (\$1,000): for every $\varepsilon > 0$,
$h(N) = \sqrt{N} + O_\varepsilon(N^\varepsilon)$. -/
def Erdos30Conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ => (h N : ℝ) - Real.sqrt (N : ℝ)) =O[atTop]
      fun N : ℕ => (N : ℝ) ^ ε

/-- Milestone (Lindström 1969 / Erdős–Turán 1941):
for all $N \in \mathbb{N}$, $h(N) \le \sqrt{N} + N^{1/4} + 1$. -/
def LindstromStatement : Prop :=
  ∀ N : ℕ, (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ (4⁻¹ : ℝ) + 1

/-- Milestone (Erdős–Turán 1941):
$h(N) \le \sqrt{N} + O(N^{1/4})$. -/
def ErdosTuranStatement : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    (h N : ℝ) ≤ Real.sqrt (N : ℝ) + C * (N : ℝ) ^ (4⁻¹ : ℝ)

/-- Milestone (Balogh–Füredi–Roy 2023):
$h(N) \le \sqrt{N} + 0.998 N^{1/4}$ for all sufficiently large $N$. -/
def BaloghFurediRoyStatement : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (0.998 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ)

/-- Milestone (O'Bryant 2022):
$h(N) \le \sqrt{N} + 0.99703 N^{1/4}$ for all sufficiently large $N$. -/
def OBryantStatement : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (0.99703 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ)

/-- Milestone (Carter–Hunter–O'Bryant 2025):
$h(N) \le \sqrt{N} + 0.98183 N^{1/4} + O(1)$. -/
def CarterHunterOBryantStatement : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (0.98183 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) + C

/-- Milestone (Bose 1942 lower bound):
for every prime $p$, $p \le h(p^2 - 1)$. -/
def BoseLowerBoundStatement : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ≤ h (p ^ 2 - 1)

end Erdos030
