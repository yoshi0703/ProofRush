import SameRadius
import Sharp
import Uniform

namespace Canonne
open scoped BigOperators
noncomputable section

/-- Every admissible cutoff equals the least index in the source definition. -/
theorem cutIndex_eq_of_cut {p : ℕ → ℝ} {u : ℝ} {k : ℕ}
    (hp : Law p) (hu : 0 < u) (hk : Cut p u k) : cutIndex hp hu = k := by
  refine le_antisymm (cutIndex_le_of_capture hp hu hk.1) ?_
  by_contra! hlt
  rcases hk.2 with rfl | hbelow
  · omega
  · have hincl : Finset.range (cutIndex hp hu + 1) ⊆ Finset.range k :=
      Finset.range_mono (by omega)
    have hsum : (∑ i ∈ Finset.range (cutIndex hp hu + 1), p i) ≤
        ∑ i ∈ Finset.range k, p i :=
      Finset.sum_le_sum_of_subset_of_nonneg hincl (fun i _ _ => hp.nonneg i)
    linarith [cutIndex_capture hp hu]

/-- On the canonical truncated quasinorm, the lower multiplier cannot exceed one. -/
theorem canonical_lower_optimal (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ (p : ℕ → ℝ) (hp : Law p) (u : ℝ) (hu : 0 < u),
      u < 1 → c * phi p u hp hu ≤ inverseK p u) : c ≤ 1 := by
  apply universal_lower_coefficient_optimal c hc
  intro p u k hp hk hu hu'
  simpa only [phi, cutIndex_eq_of_cut hp hu hk] using bound p hp u hu hu'

/-- For the canonical truncated quasinorm, the upper radius-gap multiplier
    cannot be smaller than one quarter. -/
theorem canonical_upper_optimal (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ (p : ℕ → ℝ) (hp : Law p) (s e : ℝ) (hs : 0 < s),
      s < e → e < 1 →
      inverseK p e ≤ Real.sqrt (1 + (c * phi p s hp hs / (e - s)) ^ 2)) :
    1 / 4 ≤ c := by
  apply universal_coefficient_lower c hc
  intro p u s k hp hk hs hsu hu
  simpa only [phi, cutIndex_eq_of_cut hp hs hk] using bound p hp s u hs hsu hu

end
end Canonne
