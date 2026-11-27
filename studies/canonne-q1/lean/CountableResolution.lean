import FiniteResolution
import CountableExistence

namespace CanonneCountable

open CanonneQuantile (finiteRate lowerFactor finite_rate_characterization)
open scoped BigOperators
noncomputable section

theorem projectedLaw {q : ℕ → ℝ} (hq : Law q) (m : ℕ) :
    CanonneDiffuse.IsLaw (project (prefixMap m) q) := finite_law_iff.mp (project_law hq _)

def prefixRate {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e) (m : ℕ) : ℕ :=
  finiteRate _ (projectedLaw hq m) e he

/-- Supremum of explicit finite profile values along the fixed singleton-prefix partitions. -/
def countableRate {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e) : ℕ := by
  classical
  exact if h : ∃ B : ℕ, ∀ m, prefixRate hq e he m ≤ B then Nat.find h else 0

theorem prefixRates_bounded_by_test {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e)
    {n : ℕ} (ht : ∃ f, GoodTest q e n f) :
    ∀ m, prefixRate hq e he m ≤ ⌊max 65 lowerFactor*(n:ℝ)⌋₊ := by
  intro m
  apply Nat.le_floor
  exact (finite_rate_characterization _ (projectedLaw hq m) e he).1 n
    ((good_test_iff_all_finite_prefix_tests hq).mp ht m)

theorem countable_bounds_of_existence {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e)
    (hex : ∃ n f, GoodTest q e n f) :
    (∀ m : ℕ, (∃ f, GoodTest q e m f) →
      (countableRate hq e he:ℝ) ≤ max 65 lowerFactor*m) ∧
      ∃ f, GoodTest q e (49152*countableRate hq e he) f := by
  classical
  obtain ⟨t,ht⟩ := hex
  have h : ∃ B : ℕ, ∀ m, prefixRate hq e he m ≤ B :=
    ⟨_,prefixRates_bounded_by_test hq e he (n:=t) ht⟩
  have hr : countableRate hq e he = Nat.find h := by simp [countableRate,h]
  constructor
  · intro m hm
    rw [hr]
    have floorBound := Nat.find_min' h (prefixRates_bounded_by_test hq e he hm)
    have hh : (0:ℝ) ≤ max 65 lowerFactor*(m:ℝ) := mul_nonneg
      ((by norm_num : (0:ℝ) ≤ 65).trans (le_max_left _ _)) (Nat.cast_nonneg m)
    exact (Nat.cast_le.mpr floorBound).trans (Nat.floor_le hh)
  · apply (good_test_iff_all_finite_prefix_tests hq).mpr
    intro m
    have hpm := Nat.find_spec h m
    obtain ⟨k,hk,ht⟩ := (finite_rate_characterization _ (projectedLaw hq m) e he).2
    rw [hr]
    exact CanonneNearOneTesting.good_test_budget_monotone (projectedLaw hq m)
      (hk.trans (Nat.mul_le_mul_left 49152 hpm)) ht

theorem countable_rate_characterization {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e) :
    (∀ m : ℕ, (∃ f, GoodTest q e m f) →
      (countableRate hq e he:ℝ) ≤ max 65 lowerFactor*m) ∧
      ∃ f, GoodTest q e (49152*countableRate hq e he) f := by
  apply countable_bounds_of_existence hq e he
  apply good_test_exists_of_finite_half_radius hq he
  intro m
  obtain ⟨n,_,ht⟩ := (finite_rate_characterization _ (projectedLaw hq m) (e/2) (by positivity)).2
  exact ⟨n,ht⟩

def countableSampleComplexity (q : ℕ → ℝ) (e : ℝ) : ℕ := by
  classical
  exact if h : ∃ n f, GoodTest q e n f then Nat.find h else 0

theorem countable_sample_complexity {q : ℕ → ℝ} (hq : Law q) (e : ℝ) (he : 0 < e) :
    (countableRate hq e he:ℝ) ≤ max 65 lowerFactor * countableSampleComplexity q e ∧
    countableSampleComplexity q e ≤ 49152*countableRate hq e he := by
  classical
  obtain ⟨hlo,ht⟩ := countable_rate_characterization hq e he
  have h : ∃ n f, GoodTest q e n f := ⟨_,ht⟩
  simp only [countableSampleComplexity,dite_eq_left h]
  exact ⟨hlo _ (Nat.find_spec h),Nat.find_min' h ht⟩

end
end CanonneCountable
