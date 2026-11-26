import Model
import Mathlib.Tactic.FieldSimp

namespace Canonne

open scoped BigOperators
noncomputable section

private def clip (x scale : ℝ) : ℝ := min 1 (x ^ (1/3 : ℝ) / scale)

private theorem clip_nonneg {x scale : ℝ} (hx : 0 ≤ x) (hscale : 0 < scale) :
    0 ≤ clip x scale :=
  le_min zero_le_one <| div_nonneg (Real.rpow_nonneg hx _) hscale.le

private theorem square_cuberoot {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1/3 : ℝ)) ^ 2 = x ^ (2/3 : ℝ) := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

private theorem clip_energy {x scale : ℝ} (hx : 0 ≤ x) (hscale : 0 < scale) :
    clip x scale ^ 2 ≤ x ^ (2/3 : ℝ) / scale ^ 2 := by
  rw [← square_cuberoot hx, ← div_pow]
  exact pow_le_pow_left₀ (clip_nonneg hx hscale) (min_le_right _ _) 2

/-- The largest possible clipping deficit divided by the (2/3) weight
    is exactly bounded by the maximum of a quadratic. -/
private theorem clip_deficit {x scale : ℝ} (hx : 0 ≤ x) (hscale : 0 < scale) :
    x ≤ x * clip x scale + (scale / 4) * x ^ (2/3 : ℝ) := by
  let t := x ^ (1/3 : ℝ)
  change x ≤ x * min 1 (t / scale) + (scale / 4) * x ^ (2/3 : ℝ)
  by_cases htscale : 1 ≤ t / scale
  · rw [min_eq_left htscale, mul_one]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.rpow_nonneg hx _))
  · rw [min_eq_right (le_of_not_ge htscale)]
    have cube : t ^ 3 = x := by
      dsimp [t]
      rw [← Real.rpow_mul_natCast hx]
      norm_num
    have quadratic : t * (1 - t / scale) ≤ scale / 4 := by
      have quad : (t * (1 - t / scale)) * scale ≤ (scale / 4) * scale := by
        have hcancel : t / scale * scale = t := div_mul_cancel₀ _ hscale.ne'
        rw [mul_assoc, sub_mul, one_mul, hcancel]
        nlinarith [sq_nonneg (t - scale / 2)]
      exact (mul_le_mul_iff_of_pos_right hscale).mp quad
    have weighted := mul_le_mul_of_nonneg_left quadratic (sq_nonneg t)
    have hs : t ^ 2 = x ^ (2/3 : ℝ) := square_cuberoot hx
    calc
      x = x * (t / scale) + t^2 * (t * (1 - t / scale)) := by rw [← cube]; ring
      _ ≤ x * (t / scale) + t^2 * (scale/4) := add_le_add (le_refl _) weighted
      _ = x * (t / scale) + scale/4 * x ^ (2/3 : ℝ) := by rw [hs, mul_comm (scale/4)]

/-- Construct the explicit clipped, finitely supported vector on the retained
    prefix. Only the mass requirement of the cut is needed for this direction. -/
theorem exists_upper_witness {p : ℕ → ℝ} {η u : ℝ} {k : ℕ}
    (hp : Law p) (hc : Cut p η k) (hgap : η < u) :
    ∃ z, Feasible p u z ∧
      ell2 z ≤ Real.sqrt (1 + (phiAt p k / (4 * (u - η))) ^ 2) := by
  let S := powerSum p k
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hp.nonneg (i+1)) _
  let scale : ℝ := if S = 0 then 1 else 4 * (u - η) / S
  have hδ : 0 < u - η := sub_pos.mpr hgap
  have hscale : 0 < scale := by
    dsimp [scale]
    split
    · norm_num
    · exact div_pos (by positivity) (lt_of_le_of_ne hS (Ne.symm ‹S ≠ 0›))
  let z : ℕ → ℝ
    | 0 => 1
    | i+1 => if i < k then clip (p (i+1)) scale else 0
  have onPrefix (i : ℕ) (hi : i ∈ Finset.range k) :
      z (i+1) = clip (p (i+1)) scale := by
    simp [z, Finset.mem_range.mp hi]
  have outside (i : ℕ) (hi : i ∉ Finset.range (k+1)) : z i = 0 := by
    cases i with
    | zero => exact False.elim <| hi <| Finset.mem_range.mpr (Nat.zero_lt_succ k)
    | succ i =>
      have hn : ¬ i < k := by
        intro hl
        exact hi (Finset.mem_range.mpr (Nat.succ_lt_succ hl))
      simp [z, hn]
  have nonneg (i : ℕ) : 0 ≤ z i := by
    cases i with
    | zero => exact zero_le_one
    | succ i =>
      change 0 ≤ if i < k then clip (p (i+1)) scale else 0
      split
      · exact clip_nonneg (hp.nonneg _) hscale
      · exact le_refl 0
  have leOne (i : ℕ) : z i ≤ 1 := by
    cases i with
    | zero => exact le_refl 1
    | succ i =>
      change (if i < k then clip (p (i+1)) scale else 0) ≤ 1
      split
      · exact min_le_left _ _
      · exact zero_le_one
  have suppCapture (i : ℕ) (hi : i ∉ Finset.range (k+1)) :
      p i * z i = 0 := by rw [outside i hi, mul_zero]
  have suppEnergy (i : ℕ) (hi : i ∉ Finset.range (k+1)) :
      z i ^ 2 = 0 := by rw [outside i hi]; norm_num
  have hbudget : scale / 4 * S ≤ u - η := by
    by_cases hzero : S = 0
    · rw [hzero, mul_zero]
      exact hδ.le
    · rw [show scale = 4 * (u - η) / S by simp [scale, hzero]]
      have eq : 4 * (u - η) / S / 4 * S = u - η := by
        field_simp
      rw [eq]
  have hprefix : 1 - η ≤ (∑ i ∈ Finset.range k, p (i+1)) + p 0 := by
    simpa only [Finset.sum_range_succ'] using hc.1
  have hsum : (∑ i ∈ Finset.range k, p (i+1)) ≤
      (∑ i ∈ Finset.range k, p (i+1) * z (i+1)) + scale / 4 * S := by
    unfold S powerSum
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    rw [onPrefix i hi]
    exact clip_deficit (hp.nonneg _) hscale
  have hcapture : 1 - u ≤ ∑' i, p i * z i := by
    rw [tsum_eq_sum suppCapture, Finset.sum_range_succ']
    change 1 - u ≤ (∑ i ∈ Finset.range k, p (i + 1) * z (i + 1)) + p 0 * 1
    linarith
  have hEnBound : (∑ i ∈ Finset.range k, z (i+1) ^ 2) ≤ S / scale^2 := by
    unfold S powerSum
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => by
      rw [onPrefix i hi]
      exact clip_energy (hp.nonneg _) hscale
  have hEnIdentity : S / scale ^ 2 = (phiAt p k / (4 * (u - η))) ^ 2 := by
    have cube : phiAt p k ^ 2 = S ^ 3 := by
      change (S ^ (3/2 : ℝ)) ^ 2 = S ^ 3
      rw [← Real.rpow_mul_natCast hS]
      norm_num [Real.rpow_natCast]
    rw [div_pow, cube]
    by_cases hzero : S = 0
    · simp [hzero]
    · rw [show scale = 4 * (u - η) / S by simp [scale, hzero]]
      have hden : 4 * (u - η) ≠ 0 := by positivity
      field_simp
  refine ⟨z, ⟨nonneg, leOne, summable_of_ne_finset_zero suppEnergy, hcapture⟩, ?_⟩
  apply Real.sqrt_le_sqrt
  rw [tsum_eq_sum suppEnergy, Finset.sum_range_succ']
  change (∑ i ∈ Finset.range k, z (i+1) ^ 2) + (1:ℝ)^2 ≤
    1 + (phiAt p k / (4 * (u - η))) ^ 2
  linarith

end

end Canonne
