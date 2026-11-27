import CountableLift
import TestingBaseline

namespace CanonneCountable

open scoped BigOperators
noncomputable section

/-- Agreement of the countable PMF law with the finite law used by the
formalized finite characterization. -/
theorem finite_law_iff {A : Type*} [Fintype A] {p : A → ℝ} :
    Law p ↔ CanonneDiffuse.IsLaw p := by
  constructor
  · intro hp
    exact ⟨hp.nonneg, by simpa only [tsum_fintype] using hp.total⟩
  · intro hp
    exact ⟨hp.nonneg, hp.total ▸ hasSum_fintype p⟩

theorem finite_expectation_eq {A : Type*} [Fintype A] (p : A → ℝ) (n : ℕ)
    (f : (Fin n → A) → ℝ) :
    expectation (iid p n) f =
      CanonneNearOneTesting.rejection (CanonneHeadTransfer.pilotLaw p) f := by
  simp only [expectation, iid, CanonneNearOneTesting.rejection, CanonneHeadTransfer.pilotLaw, tsum_fintype]

theorem finite_tv_eq {A : Type*} [Fintype A] (p q : A → ℝ) :
    tv p q = CanonneDiffuse.totalVariation p q := by
  simp only [tv, CanonneDiffuse.totalVariation, tsum_fintype]

/-- Finite projected tests have precisely the same semantics as the finite
GoodTest already used in the sample-size argument. -/
theorem finite_good_test_iff {A : Type*} [Fintype A] {q : A → ℝ} {e : ℝ} {n : ℕ} :
    (∃ f, GoodTest q e n f) ↔ (∃ f, CanonneNearOneTesting.GoodTest q e n f) := by
  constructor
  · intro ⟨f, hnull, halt⟩
    refine ⟨fun x => (f x : ℝ), fun x => (f x).2, ?_, ?_⟩
    · simpa only [finite_expectation_eq] using hnull
    · intro p hp hfar
      rw [← finite_tv_eq] at hfar
      simpa only [finite_expectation_eq] using halt p (finite_law_iff.mpr hp) hfar
  · intro ⟨f, hf, hnull, halt⟩
    let g (x : Fin n → A) : Set.Icc (0:ℝ) 1 := ⟨f x, hf x⟩
    refine ⟨g, ?_, ?_⟩
    · simpa only [finite_expectation_eq] using hnull
    · intro p hp hfar
      rw [finite_tv_eq] at hfar
      simpa only [finite_expectation_eq] using halt p (finite_law_iff.mp hp) hfar

/-- Exact fixed-budget equivalence between countably many labels and
every finite prefix projection, in the existing finite GoodTest semantics. -/
theorem good_test_iff_all_finite_prefix_tests {q : ℕ → ℝ} (hq : Law q)
    {e : ℝ} {n : ℕ} :
    (∃ f, GoodTest q e n f) ↔
      ∀ m, ∃ f, CanonneNearOneTesting.GoodTest (project (prefixMap m) q) e n f := by
  rw [good_test_iff_all_prefix_tests hq]
  exact forall_congr' (fun _ => finite_good_test_iff)

/-- A countable test inherits exact fixed-budget monotonicity from its
finite projections, by ignoring extra ordered records. -/
theorem countable_good_test_budget_monotone {q : ℕ → ℝ} (hq : Law q) {e : ℝ}
    {m n : ℕ} (hmn : m ≤ n) (htest : ∃ f, GoodTest q e m f) :
    ∃ f, GoodTest q e n f := by
  apply (good_test_iff_all_finite_prefix_tests hq).2
  intro j
  exact CanonneNearOneTesting.good_test_budget_monotone
    (finite_law_iff.mp (project_law hq (prefixMap j))) hmn
    ((good_test_iff_all_finite_prefix_tests hq).1 htest j)

end
end CanonneCountable
