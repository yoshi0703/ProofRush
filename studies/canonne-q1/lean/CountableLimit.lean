import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases

namespace CanonneCountable

open Filter
open scoped Topology
noncomputable section

/-- Rejection expectation on a countable set of ordered records. -/
def expectation {X : Type*} (w f : X → ℝ) : ℝ := ∑' x, w x * f x

abbrev TestBox (X : Type*) := X → Set.Icc (0:ℝ) 1

/-- Bounded convergence of rejection expectations in the product topology.
The summable dominating family is the probability mass of each record. -/
theorem continuous_rejection {X : Type*} {w : X → ℝ}
    (hw : Summable w) (hnonneg : ∀ x, 0 ≤ w x) :
    Continuous (fun f : TestBox X => expectation w (fun x => (f x : ℝ))) := by
  unfold expectation
  refine continuous_tsum (fun x => ?_) hw (fun x f => ?_)
  · have hx : Continuous (fun f : TestBox X => f x) := continuous_apply x
    exact continuous_const.mul ((continuous_subtype_val : Continuous
      (fun v : Set.Icc (0:ℝ) 1 => (v : ℝ))).comp hx)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnonneg x) (f x).2.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (f x).2.2 (hnonneg x)

/-- A single convergent subsequence works for every alternative. An alternative
only needs to be detected at all sufficiently fine indices, and no uniform
index across alternatives is needed. -/
theorem compact_test_limit {X P : Type*} [Countable X]
    {w₀ : X → ℝ} (h₀ : Summable w₀) (hn₀ : ∀ x, 0 ≤ w₀ x)
    {w₁ : P → X → ℝ} (h₁ : ∀ p, Summable (w₁ p)) (hn₁ : ∀ p x, 0 ≤ w₁ p x)
    {α β : ℝ} (f : ℕ → TestBox X)
    (hn : ∀ m, expectation w₀ (fun x => (f m x : ℝ)) ≤ α)
    (ha : ∀ p, ∀ᶠ m in atTop, β ≤ expectation (w₁ p) (fun x => (f m x : ℝ))) :
    ∃ g : TestBox X,
      expectation w₀ (fun x => (g x : ℝ)) ≤ α ∧
        ∀ p, β ≤ expectation (w₁ p) (fun x => (g x : ℝ)) := by
  obtain ⟨g, φ, hmono, hconv⟩ := CompactSpace.tendsto_subseq f
  refine ⟨g, ?_, ?_⟩
  · have hlim := (continuous_rejection h₀ hn₀).continuousAt.tendsto.comp hconv
    exact le_of_tendsto hlim (Eventually.of_forall (fun m => hn (φ m)))
  · intro p
    have hlim := (continuous_rejection (h₁ p) (hn₁ p)).continuousAt.tendsto.comp hconv
    exact ge_of_tendsto hlim (hmono.tendsto_atTop.eventually (ha p))

end
end CanonneCountable
