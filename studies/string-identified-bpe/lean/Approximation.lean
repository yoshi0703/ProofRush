import UniversalRate
import SourceGreedy

/-! The worst unbounded-vocabulary ratio and the uniform fixed-vocabulary
bound use the same greedy rules and the same partial-merge optimum. -/
namespace SpellingApproximation
open SpellingBPE DiamondLimit

theorem sharp_rates {k : Nat} (hk : 8 ≤ k) :
    ((1:ℝ)/114 ≤ worst Greedy k * Real.sqrt k ∧ worst Greedy k * Real.sqrt k ≤ 24) ∧
    ((1:ℝ)/114 ≤ worst RawDiamond.RawGreedy k * Real.sqrt k ∧
      worst RawDiamond.RawGreedy k * Real.sqrt k ≤ 24) :=
  ⟨SpellingUniversalRate.replacement_worst_rate hk,SpellingUniversalRate.overlapping_worst_rate hk⟩

#print axioms sharp_rates
#print axioms BoundedInitial.uniform_source_approximation
end SpellingApproximation
