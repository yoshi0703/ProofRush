import FiniteLower
import SumQuantileUpper

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting CanonneRefinement
open CanonneHeadEnvelope (CanonicalSplit exists_canonical_split)
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A] {q : A → ℝ} {e : ℝ}

omit [DecidableEq A] in
theorem regularRate_upper (S : CanonicalSplit q e) (hq : IsLaw q) (he : 0 < e) :
    ∃ m ≤ 3076*regularRate S hq, ∃ f, GoodTest q e m f := by
  obtain ⟨j,hcross,hvalue,_⟩ := firstDyadic_spec _ (regular_crossing_exists S hq he)
  let n := (2:ℕ)^j
  have hn : 0 < n := by dsimp [n]; positivity
  have hcast : (n:ℝ) = (2:ℝ)^j := by simp [n]
  obtain ⟨m,hm,f,hf⟩ := regular_quantile_upper_sum S.pulledLaw (S.pulledLaw_isLaw hq)
    (fun i => S.head_pos i) hn (S.tailMass_le hq.total) (by simp only [hcast]; exact hcross)
  exact ⟨m,by simpa only [regularRate,hvalue] using hm,(S.goodTest_iff m).mp ⟨f,hf⟩⟩

/-- Rate with no optimizations over distributions or tests. A canonical split is obtained
by sorting the nonnegative reference probabilities, with arbitrary tie breaking. -/
def finiteRate (q : A → ℝ) (hq : IsLaw q) (e : ℝ) (he : 0 < e) : ℕ := by
  classical
  exact if ha : ∃ a, e < 1-q a then
    if 16*(1-e) ≤ nearMoment q (1-e) then directRate q (1-e)
    else
      let he1 : e < 1 := by
        obtain ⟨a,ha⟩ := ha
        linarith [hq.nonneg a]
      regularRate (exists_canonical_split q hq.total he.le he1).some hq
  else 0

/-- Universal comparison constants, independent of alphabet, reference and distance.
The statement permits every randomized test on the actual ordered iid observations,
including zero observations for empty strict alternatives. -/
theorem finite_rate_characterization (q : A → ℝ) (hq : IsLaw q) (e : ℝ) (he : 0 < e) :
    (∀ m : ℕ, (∃ f, GoodTest q e m f) →
      (finiteRate q hq e he : ℝ) ≤ max 65 lowerFactor * m) ∧
    ∃ n ≤ 49152*finiteRate q hq e he, ∃ f, GoodTest q e n f := by
  classical
  by_cases halt : ∃ a, e < 1-q a
  · have he1 : e < 1 := by
      obtain ⟨a,ha⟩ := halt
      linarith [hq.nonneg a]
    have hd : 0 < 1-e := by linarith
    have hfar := (strict_alternative_iff_atom q hq e).mpr halt
    by_cases hnear : 16*(1-e) ≤ nearMoment q (1-e)
    · have bound := directRate_comparison q hq hd hnear (by simpa using hfar)
      rw [show 1-(1-e)=e by ring] at bound
      simp only [finiteRate,dite_eq_left halt,ite_eq_left hnear]
      refine ⟨?_,bound.2⟩
      intro m hm
      have h : (directRate q (1-e):ℝ) ≤ 65*(m:ℝ) := by exact_mod_cast bound.1 m hm
      exact h.trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg m)
    · let S := (exists_canonical_split q hq.total he.le he1).some
      have eq : finiteRate q hq e he = regularRate S hq := by simp [finiteRate,halt,hnear,S]
      rw [eq]
      refine ⟨?_,?_⟩
      · intro m hm
        have hreg : nearMoment q (1-e) ≤ 32*(1-e) := by linarith [lt_of_not_ge hnear]
        exact (regularRate_le_of_test S hq he he1 hreg halt hm).trans <|
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg m)
      · obtain ⟨n,hn,ht⟩ := regularRate_upper S hq he
        exact ⟨n,by omega,ht⟩
  · have hzero : finiteRate q hq e he = 0 := by simp [finiteRate,halt]
    rw [hzero]
    refine ⟨fun m _ => ?_,0,by simp,zero_budget_when_vacuous q e (fun h =>
      halt ((strict_alternative_iff_atom q hq e).mp h))⟩
    simp only [Nat.cast_zero]
    exact mul_nonneg ((by norm_num : (0:ℝ)≤65).trans (le_max_left _ _)) (Nat.cast_nonneg m)

def sampleComplexity (q : A → ℝ) (e : ℝ) : ℕ := by
  classical
  exact if h : ∃ n, ∃ f, GoodTest q e n f then Nat.find h else 0

theorem finite_sample_complexity (q : A → ℝ) (hq : IsLaw q) (e : ℝ) (he : 0 < e) :
    (finiteRate q hq e he:ℝ) ≤ max 65 lowerFactor * sampleComplexity q e ∧
    sampleComplexity q e ≤ 49152*finiteRate q hq e he := by
  classical
  obtain ⟨hlo,n,hn,ht⟩ := finite_rate_characterization q hq e he
  have h : ∃ n, ∃ f, GoodTest q e n f := ⟨n,ht⟩
  simp only [sampleComplexity,dite_eq_left h]
  exact ⟨hlo _ (Nat.find_spec h),(Nat.find_min' h ht).trans hn⟩

end
end CanonneQuantile
