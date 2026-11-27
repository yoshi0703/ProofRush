import ColoredCoupling
import PilotCosts

namespace CanonneColoredPilot

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {B A : Type*} [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]

/-- Joint pilot rounding and likelihood comparison, at the unrounded
sum of bin-specific collision/overlap moments. -/
theorem rounded_colored_iid_tv {n : ℕ} {c s : ℝ} {b u : B → ℝ}
    (hc : 0 < c) (hs : 0 ≤ s) (hb : ∀ j, 0 < b j) (hu : ∀ j, 0 < u j)
    (htotal : ∑ j, s * b j ≤ 1)
    {fresh : A → ℝ} {r : B → A → ℝ} (hf : IsLaw fresh) (hr : ∀ j, IsLaw (r j)) :
    totalVariation
      (sharedSample (n := n) (coloredLatent (fun j => pilotCount c (b j) (u j))
        (fun j => s * b j)) fresh (fun slot => r slot.1))
      (pilotLaw (bandedLabel (fun j => s * b j) fresh r)) ≤
      (n.choose 2 : ℝ) * ((s^2 / c) * ∑ j, b j * Real.sqrt (u j)) := by
  refine (colored_iid_tv (fun j => pilotCount_pos hc (hb j) (hu j))
    (fun j => mul_nonneg hs (hb j).le) htotal hf hr).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => collision_cost_upper hc (hb j) (hu j))

end
end CanonneColoredPilot
