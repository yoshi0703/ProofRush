import CountableResolution
import SuccinctBound

/-! Main entry point for Canonne's COLT 2024 Open Question 1. Both error probabilities
are one third, alternatives are strictly greater than the given TV distance, and
all hidden comparison constants are independent of the reference law and alphabet. -/
namespace CanonneQuestionOne

open CanonneQuantile

theorem uniform_characterization :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      (∀ {A : Type} [Fintype A] [DecidableEq A] (q : A → ℝ) (hq : CanonneDiffuse.IsLaw q)
          (e : ℝ) (he : 0 < e),
        (finiteRate q hq e he : ℝ) ≤ L*sampleComplexity q e ∧
          (sampleComplexity q e : ℝ) ≤ U*finiteRate q hq e he) ∧
      (∀ (q : ℕ → ℝ) (hq : CanonneCountable.Law q) (e : ℝ) (he : 0 < e),
        (CanonneCountable.countableRate hq e he : ℝ) ≤ L*CanonneCountable.countableSampleComplexity q e ∧
          (CanonneCountable.countableSampleComplexity q e : ℝ) ≤ U*CanonneCountable.countableRate hq e he) := by
  refine ⟨max 65 lowerFactor,49152,(by norm_num : (0:ℝ)<65).trans_le (le_max_left _ _),by norm_num,?_,?_⟩
  · intro A hA dA q hq e he
    obtain ⟨hl,hu⟩ := finite_sample_complexity q hq e he
    exact ⟨hl,by exact_mod_cast hu⟩
  · intro q hq e he
    obtain ⟨hl,hu⟩ := CanonneCountable.countable_sample_complexity hq e he
    exact ⟨hl,by exact_mod_cast hu⟩

end CanonneQuestionOne
