import RegularHeadGlue
import HeadTrimming
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneIIDHead CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The head bulk and omitted mass in original probability units. -/
def originalPrefixCost (q s : A → ℝ) (O R : Finset A) (n : ℕ) : ℝ :=
  bulk (∑ i ∈ R, (s i)^2) n + mass q (O \ R)

def originalHeadProxy (q s : A → ℝ) (O : Finset A) (cuts : Finset (Finset A))
    (hc : cuts.Nonempty) (n : ℕ) : ℝ :=
  cuts.inf' hc (fun R => originalPrefixCost q s O R n)

/-- All the upper-branch test components are constructed from the
minimizing admissible prefix; no conditional head test is assumed. -/
theorem regular_upper_at_prefix_minimum (q : A → ℝ) (hq : IsLaw q)
    (T : Finset A) {a : A} (ha : a ∉ T) (s : A → ℝ)
    (hs : ∀ i ∈ Tᶜ.erase a, 0 < s i)
    (cube : ∀ i ∈ Tᶜ.erase a, q i = (s i)^3)
    (cuts : Finset (Finset A)) (hc : cuts.Nonempty)
    (subcut : ∀ R ∈ cuts, R ⊆ Tᶜ.erase a)
    {n : ℕ} (hn : 0 < n) {e : ℝ} (hΔ : mass q T ≤ e)
    (strong : 4000000*(groupScale q T n/(n : ℝ)+originalHeadProxy q s (Tᶜ.erase a) cuts hc n) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2) :
    ∃ j ≤ 3076*n, ∃ f, GoodTest q e j f := by
  let O := Tᶜ.erase a
  obtain ⟨R, hmem, hR⟩ := Finset.exists_mem_eq_inf' hc (fun R => originalPrefixCost q s O R n)
  have hsub := subcut R hmem
  let B := bulk (∑ i ∈ R, (s i)^2) n
  have hB : 0 ≤ B := bulk_nonneg _ _
  have nul := exists_trimmed_prefix_test q hq R s
    (fun i hi => hs i (hsub hi)) (fun i hi => cube i (hsub hi)) n hn
  obtain ⟨K,hKR,trim,f,hUnit,hNull,hAlt⟩ := nul
  have hstrong : 4000000*(groupScale q T n/(n : ℝ)+B+mass q (O \ R)) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2 := by
    change originalHeadProxy q s O cuts hc n = originalPrefixCost q s O R n at hR
    change 4000000*(groupScale q T n/(n : ℝ)+originalHeadProxy q s O cuts hc n) ≤ _ at strong
    rw [hR] at strong
    simpa only [originalPrefixCost, B, ← add_assoc] using strong
  obtain ⟨j,hj,g,hg⟩ := regular_upper_from_prefix_test q hq T R K ha hKR hsub hn hΔ hB trim
    hstrong hUnit hNull hAlt
  exact ⟨j, by omega, g, hg⟩

def canonicalHeadProxy (q : A → ℝ) (O : Finset A) (cuts : Finset (Finset A))
    (hc : cuts.Nonempty) (n : ℕ) : ℝ :=
  originalHeadProxy q (fun i => (q i)^(1/3 : ℝ)) O cuts hc n

/-- Canonical prefix minimum for positive head atoms, without a separately
supplied system of cube roots. -/
theorem regular_upper_at_canonical_prefix (q : A → ℝ) (hq : IsLaw q)
    (T : Finset A) {a : A} (ha : a ∉ T)
    (positive : ∀ i ∈ Tᶜ.erase a, 0 < q i)
    (cuts : Finset (Finset A)) (hc : cuts.Nonempty)
    (subcut : ∀ R ∈ cuts, R ⊆ Tᶜ.erase a)
    {n : ℕ} (hn : 0 < n) {e : ℝ} (hΔ : mass q T ≤ e)
    (strong : 4000000*(groupScale q T n/(n : ℝ)+canonicalHeadProxy q (Tᶜ.erase a) cuts hc n) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2) :
    ∃ j ≤ 3076*n, ∃ f, GoodTest q e j f := by
  let s (i : A) := (q i)^(1/3 : ℝ)
  have hs (i : A) (hi : i ∈ Tᶜ.erase a) : 0 < s i :=
    Real.rpow_pos_of_pos (positive i hi) _
  have cube (i : A) (hi : i ∈ Tᶜ.erase a) : q i = (s i)^3 := by
    symm
    dsimp only [s]
    calc
      _ = ((q i)^(1/3 : ℝ))^(3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ = (q i)^((1/3 : ℝ)*3) := (Real.rpow_mul (positive i hi).le _ _).symm
      _ = _ := by norm_num
  exact regular_upper_at_prefix_minimum q hq T ha s hs cube cuts hc subcut hn hΔ strong

end
end CanonneQuantile
