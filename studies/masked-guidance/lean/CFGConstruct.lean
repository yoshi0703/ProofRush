import CFGSelection
import Mathlib.Tactic.LinearCombination

/-! The recurrence for computing endpoint exponents and leading coefficients
one subset of revealed coordinates at a time. Children corresponding to a
different output word have zero continuation probability and are omitted. -/
namespace CFGConstruct
open CFGSelection Filter
open scoped Topology BigOperators
noncomputable section

/-- Dynamic programming step for the exact leading asymptotic. The common
denominator counts all feasible successors; children in J agree with the
fixed output. Ties contribute additively. -/
theorem subset_step {ι : Type*} (out : Outgoing ι) (J : Finset ι)
    (child : ι → ℝ → ℝ) (cost coeff : ι → ℝ) (m : ℝ)
    (below : ∀ e ∈ J, m ≤ out.gap e + cost e)
    (known : ∀ e ∈ J, Tendsto (fun w => Real.exp (w * cost e) * child e w) atTop (𝓝 (coeff e))) :
    Tendsto (fun w => Real.exp (w * m) * ∑ e ∈ J, out.probability w e * child e w) atTop
      (𝓝 (∑ e ∈ J, if out.gap e + cost e = m then out.base e * coeff e / out.maxWeight else 0)) := by
  simp only [Finset.mul_sum]
  apply tendsto_finsetSum
  intro e he
  have gap := tendsto_gap_exp (out.gap e + cost e - m) (sub_nonneg.mpr (below e he))
  have h := ((tendsto_const_nhds (x := out.base e)).mul (known e he)).mul gap
  have hd := h.div out.denominator_limit out.maxWeight_pos.ne'
  simp only [sub_eq_zero] at hd
  have iden (w : ℝ) :
      (out.base e * (Real.exp (w * cost e) * child e w) *
        Real.exp (-(w * (out.gap e + cost e - m)))) / out.denominator w =
      Real.exp (w * m) * (out.probability w e * child e w) := by
    unfold Outgoing.probability
    have ex : Real.exp (w * cost e) * Real.exp (-(w * (out.gap e + cost e - m))) =
        Real.exp (w * m) * Real.exp (-(w * out.gap e)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    linear_combination (out.base e * child e w / out.denominator w) * ex
  have completed := hd.congr iden
  by_cases hbest : out.gap e + cost e = m
  · simpa only [ite_eq_left hbest, mul_one] using completed
  · simpa only [ite_eq_right hbest, mul_zero, zero_div] using completed

end
end CFGConstruct
