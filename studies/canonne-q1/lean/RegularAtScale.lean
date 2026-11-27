import MarkerNecessity
import TailCalibration

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting
open CanonneQuantile
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- At a sufficiently enlarged root scale and integer floor, no successful
finite full test exists for the supplied hard reduced prior. -/
theorem no_good_test_at_regular_scale
    {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (hw : 0 < ∑ t : T, q (Sum.inr t)) {e x : ℝ} (hx : 0 < x)
    (hfloor : 8 ≤ (n : ℝ) * x)
    (hroot : 64 * root (fun t : T => q (Sum.inr t))
      (fun t => hq.nonneg (Sum.inr t)) (n : ℝ) (Nat.cast_nonneg n) ≤ Real.sqrt x)
    {weights : I → ℝ} (hweights : IsLaw weights)
    {alts : I → H ⊕ Unit → ℝ} (halts : ∀ i, IsLaw (alts i))
    (hdef : ∀ i, 0 < weights i →
      e - (∑ t : T, q (Sum.inr t)) + x < trueHeadDeficit q (alts i))
    (hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ 1/8) :
    ¬ ∃ f, GoodTest q e n f := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let tail (t : T) := q (Sum.inr t)
  have ht (t : T) : 0 ≤ tail t := hq.nonneg _
  obtain ⟨hc, hg⟩ := criterion_at_reverse_scale tail ht hnR hx hfloor hroot
  obtain ⟨hf, hl⟩ := heavy_light_budgets tail ht hnR hx
  have hcut : 0 < cutoff (n : ℝ) x := by unfold cutoff; positivity
  exact no_good_test_of_regular_cut hn hq hw hx hcut hc
    (by simpa only [mul_comm] using hf) (by simpa only [mul_comm] using hl)
    hg hweights halts hdef hprior

/-- The original full tester must pay the marker fluctuation term at the
tail-root reverse scale. This includes the zero-mass-tail case. -/
theorem marker_mass_necessary_at_regular_scale
    {n : ℕ} (hn : 0 < n) {q : H ⊕ T → ℝ} (hq : IsLaw q)
    {e x : ℝ} (hx : 0 < x) (hfloor : 8 ≤ (n : ℝ) * x)
    (hhead : 1 ≤ (n : ℝ) * (1 - ∑ t : T, q (Sum.inr t)))
    (hew : (∑ t : T, q (Sum.inr t)) ≤ e)
    (hroot : 64 * root (fun t : T => q (Sum.inr t))
      (fun t => hq.nonneg (Sum.inr t)) (n : ℝ) (Nat.cast_nonneg n) ≤ Real.sqrt x)
    (htest : ∃ f, GoodTest q e n f) :
    let w := ∑ t : T, q (Sum.inr t)
    Real.sqrt (w*(1-w)/(n : ℝ)) ≤ 8*(e-w+x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let tail (t : T) := q (Sum.inr t)
  have ht (t : T) : 0 ≤ tail t := hq.nonneg _
  obtain ⟨hc, hg⟩ := criterion_at_reverse_scale tail ht hnR hx hfloor hroot
  obtain ⟨hf, hl⟩ := heavy_light_budgets tail ht hnR hx
  have hcut : 0 < cutoff (n : ℝ) x := by unfold cutoff; positivity
  exact marker_mass_necessary_of_regular_cut hn hq hx hcut hc hhead hew
    (by simpa only [mul_comm] using hf) (by simpa only [mul_comm] using hl) hg htest

end
end CanonneRegularTransfer
