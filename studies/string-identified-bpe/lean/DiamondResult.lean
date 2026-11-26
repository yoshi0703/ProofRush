import LimitRatio
import DiamondConclusion
import RawDiamond

namespace DiamondResult
open SpellingBPE SpellingDecoy DiamondGuarantee DiamondFamily DiamondLimit
open scoped Topology

theorem input_allowed (m k : ℕ) (hm : 2 ≤ m) : allowed (input m k) :=
  ⟨DiamondConclusion.input_nonempty m k,DiamondConclusion.input_not_unique m k hm⟩

/-- The limit as the merge budget tends to infinity of the infimum, over
nonempty genuinely ambiguous inputs, of the best greedy-tie ratio. -/
theorem replacement_limit_zero : Filter.Tendsto (worst Greedy) Filter.atTop (𝓝 0) := by
  apply limit_of_construction
  intro ε he
  obtain ⟨K,bad⟩ := arbitrarily_small ε he
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨m,hm,pos,existsRun,all⟩ := bad k hk
  exact ⟨input m k,input_allowed m k hm,pos,existsRun,all⟩

/-- All adjacent observations, including overlapping self-pairs, determine
the next maximizing pair. Full replacements still scan from left to right. -/
theorem overlapping_limit_zero : Filter.Tendsto (worst RawDiamond.RawGreedy) Filter.atTop (𝓝 0) := by
  apply limit_of_construction
  intro ε he
  obtain ⟨K,bad⟩ := arbitrarily_small ε he
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨m,hm,pos,_,all⟩ := bad k hk
  have mp : 1 ≤ m := by omega
  exact ⟨input m k,input_allowed m k hm,pos,RawDiamond.rawGreedy_exists m k mp,
    fun v run => all v ((RawDiamond.rawGreedy_iff_greedy_input m k mp v).mp run)⟩

theorem below_one_sixth : ∃ w : Word Letters, allowed w ∧ 0 < optimum w 338 ∧
    (∃ v, Greedy 338 w v) ∧ ∀ v, Greedy 338 w v →
      6*(w.length-v.length) < optimum w 338 := by
  let w := input 13 338
  have bound : 30758 ≤ optimum w 338 := comparator_lower 13 338 (by decide)
  refine ⟨w,input_allowed 13 338 (by decide),by omega,has_greedy 13 338 (by decide),?_⟩
  intro v run
  have exactGain : w.length-v.length = 4732 := all_ties 13 338 (by decide) v run
  omega

end DiamondResult
