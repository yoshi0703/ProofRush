import WeakCrossingComplete
import HeadProfileBridge
import Horizontal

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- The weak statistical lower comparison in the exact cost and slack
coordinates of the horizontal comparison theorem. The off-largest head
weights are the cube roots of the original, unconditional probabilities. -/
theorem weak_quantile_crossing_at_fixed_amplification
    {d : ℕ} (order : Fin (d+1) ≃ H) {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i => q (Sum.inl (order i))))
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hwe : (∑ t : T, q (Sum.inr t)) ≤ e)
    (hreg : CanonneNearOne.nearOneMoment q (1-e) ≤ 32*(1-e))
    (hnonempty : ∃ p : H ⊕ T → ℝ, IsLaw p ∧ e < totalVariation p q)
    {m : ℕ} (htest : ∃ f, GoodTest q e m f) :
    let n := amplifiedBudget m
    let w := ∑ t : T, q (Sum.inr t)
    let s := fun i : Fin d => (q (Sum.inl (order i.succ)))^((1:ℝ)/3)
    CanonneQuantile.cost s (CanonneHeadEnvelope.cutoffCandidates d)
        (CanonneHeadEnvelope.cutoffCandidates_nonempty d) (w*(1-w)) (n:ℝ) ≤
      163881 * CanonneQuantile.slack (fun t : T => q (Sum.inr t))
        (fun t => hq.nonneg (Sum.inr t)) (e-w) (n:ℝ) (Nat.cast_nonneg n) := by
  open CanonneHeadEnvelope in
  let n := amplifiedBudget m
  let w := ∑ t : T, q (Sum.inr t)
  let A := headMass q
  let s := fun i : Fin d => (q (Sum.inl (order i.succ)))^((1:ℝ)/3)
  have hweak := weak_crossing_for_sorted_head order hq hpos horder he he1 hwe hreg hnonempty htest
  have hm : 0 < m := (testing_baseline_budgets hq he he1 hreg hnonempty htest).1
  have hnN : 0 < n := Nat.mul_pos (by decide) hm
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr hnN
  have hA : 0 < A := by
    refine (hpos 0).trans_le ?_
    exact Finset.single_le_sum (fun h _ => hq.nonneg (Sum.inl h)) (Finset.mem_univ (order 0))
  let h := orderedConditional order q
  have hhnonneg (i : Fin (d+1)) : 0 ≤ h i := div_nonneg (hq.nonneg _) hA.le
  have hraw (i : Fin (d+1)) : A * h i = q (Sum.inl (order i)) :=
    mul_div_cancel₀ _ hA.ne'
  have hprofile : A * headProfile ((n:ℝ)*A) h =
      CanonneQuantile.headProfile s (cutoffCandidates d) (cutoffCandidates_nonempty d) (n:ℝ) := by
    rw [← headProfile_scale hn hA hhnonneg]
    simp only [hraw]
    exact headProfile_eq_quantile hn (fun i => hq.nonneg (Sum.inl (order i)))
  have hw0 : 0 ≤ w := Finset.sum_nonneg (fun t _ => hq.nonneg (Sum.inr t))
  have hwA : 0 ≤ w*(1-w) := mul_nonneg hw0 (by linarith [show w≤e from hwe])
  change Real.sqrt (w*(1-w)/(n:ℝ)) + 1/(n:ℝ) + A*headProfile ((n:ℝ)*A) h ≤
    163881 * (e-w+tailOverlapSquare q hq n) at hweak
  rw [Real.sqrt_div hwA, hprofile] at hweak
  exact hweak

end
end CanonneRegularTransfer
