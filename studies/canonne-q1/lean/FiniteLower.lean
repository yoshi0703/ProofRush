import BoundaryRate
import DyadicRate
import CanonicalRegular
import WeakCrossingQuantile

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting CanonneRefinement CanonneRegularTransfer
open CanonneHeadEnvelope (CanonicalSplit cutoffCandidates cutoffCandidates_nonempty cutoffCandidates_full)
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] {q : A → ℝ} {e : ℝ}

def strongFactor : ℝ := 1/4000000

def crossingPredicate (S : CanonicalSplit q e) (hq : IsLaw q) : ℕ → Prop :=
  crosses (fun i : Fin S.headPred => (q (S.head i.succ))^((1:ℝ)/3))
    (cutoffCandidates S.headPred) (cutoffCandidates_nonempty _)
    (fun i => q (S.tail i)) (fun i => hq.nonneg (S.tail i))
    (S.tailMass*(1-S.tailMass)) (e-S.tailMass) strongFactor

def regularRate (S : CanonicalSplit q e) (hq : IsLaw q) : ℕ :=
  firstDyadic (crossingPredicate S hq)

omit [DecidableEq A] in
theorem regular_crossing_exists (S : CanonicalSplit q e) (hq : IsLaw q) (he : 0 < e) :
    ∃ j, crossingPredicate S hq j :=
  dyadic_crossing_exists _ _ (cutoffCandidates_full _) _ _ _ _ (by norm_num [strongFactor])
    (positive_initial_slack _ _ he (S.tailMass_le hq.total))

def lowerFactor : ℝ := 2*dilation 163881 strongFactor*8796093022208

omit [DecidableEq A] in
theorem regularRate_le_of_test (S : CanonicalSplit q e) (hq : IsLaw q) (he : 0 < e) (he1 : e < 1)
    (hreg : nearMoment q (1-e) ≤ 32*(1-e)) (halt : ∃ a, e < 1-q a)
    {m : ℕ} (htest : ∃ f, GoodTest q e m f) : (regularRate S hq : ℝ) ≤ lowerFactor*m := by
  classical
  let Q := S.pulledLaw
  have hQ := S.pulledLaw_isLaw hq
  have ht := (S.goodTest_iff m).mpr htest
  have hnear : CanonneNearOne.nearOneMoment Q (1-e) = nearMoment q (1-e) :=
    S.label.sum_comp (fun a => q a*min 1 (Real.sqrt (q a/(1-e))))
  have haltQ : ∃ p, IsLaw p ∧ e < totalVariation p Q := by
    obtain ⟨a,ha⟩ := halt
    obtain ⟨i,hi⟩ := S.label.surjective a
    apply (strict_alternative_iff_atom Q hQ e).mpr
    exact ⟨i,by simpa [Q,CanonicalSplit.pulledLaw,hi] using ha⟩
  have hregQ : CanonneNearOne.nearOneMoment Q (1-e) ≤ 32*(1-e) := hnear.trans_le hreg
  have hnpos : 0 < m := (testing_baseline_budgets hQ he.le he1 hregQ haltQ ht).1
  let n := amplifiedBudget m
  have hn : (1:ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n from Nat.mul_pos (by decide) hnpos)
  have hweak := weak_quantile_crossing_at_fixed_amplification (Equiv.refl (Fin (S.headPred+1))) hQ
    (fun i => S.head_pos i) S.head_sorted he.le he1 (S.tailMass_le hq.total) hregQ haltQ ht
  let b := S.thresholdAtom^((1:ℝ)/3)
  have hb : 0 < b := Real.rpow_pos_of_pos S.threshold_pos _
  have hb3 : b^3 = S.thresholdAtom := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast S.threshold_pos.le]
    norm_num
  have hhead (i : Fin S.headPred) : b ≤ (q (S.head i.succ))^((1:ℝ)/3) :=
    Real.rpow_le_rpow S.threshold_pos.le (S.threshold_le_head _) (by norm_num)
  have hda : e-S.tailMass ≤ b^3 := hb3 ▸ (S.gap_lt_threshold hq.total).le
  have htail (i : Fin S.tailSize) : q (S.tail i) ≤ b^3 := hb3 ▸ S.tail_le_threshold i
  have result := firstDyadic_le_of_weak _ _ (cutoffCandidates_full _) _ (fun i => hq.nonneg (S.tail i))
    (S.tailMass*(1-S.tailMass)) hb hhead hda (sub_nonneg.mpr (S.tailMass_le hq.total)) htail hn
    (by norm_num : (0:ℝ)<163881) (by norm_num [strongFactor] : 0<strongFactor) hweak
  change (regularRate S hq:ℝ) ≤ 2*dilation 163881 strongFactor*(n:ℝ) at result
  simpa only [n,amplifiedBudget,lowerFactor,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using result

end
end CanonneQuantile
