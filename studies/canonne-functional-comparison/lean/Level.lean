import Peetre
import Mathlib.Tactic.FieldSimp

namespace Canonne
open scoped BigOperators
noncomputable section

private theorem split_bound {p a b : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ i, a i + b i = p i) (ha : Summable fun i => |a i|)
    (hb : Summable fun i => b i ^ 2) :
    peetre p t ≤ (∑' i, |a i|) + t * ell2 b :=
  csInf_le (costs_bounded p ht) ⟨a,b,h,ha,hb,rfl⟩

private theorem increasing {p : ℕ → ℝ} (hp : Law p) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) :
    peetre p r ≤ peetre p t := by
  refine le_csInf (costs_nonempty hp t) ?_
  rintro _ ⟨a,b,h,ha,hb,rfl⟩
  exact (split_bound hr h ha hb).trans
    (add_le_add_right (mul_le_mul_of_nonneg_right hrt (Real.sqrt_nonneg _)) _)

private theorem concave_mix {p : ℕ → ℝ} (hp : Law p) {r t w : ℝ}
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hw : 0 ≤ w) (hw' : w ≤ 1) :
    (1-w)*peetre p r + w*peetre p t ≤ peetre p ((1-w)*r + w*t) := by
  refine le_csInf (costs_nonempty hp _) ?_
  rintro _ ⟨a,b,h,ha,hb,rfl⟩
  have hu := add_le_add
    (mul_le_mul_of_nonneg_left (split_bound hr h ha hb) (sub_nonneg.mpr hw'))
    (mul_le_mul_of_nonneg_left (split_bound ht h ha hb) hw)
  exact hu.trans_eq (by ring)

/-- Below the top plateau, the target level is met at only one nonnegative parameter.
    In particular either usual inverse convention gives the same result. -/
theorem peetre_level_iff {p : ℕ → ℝ} {u t : ℝ} (hp : Law p)
    (hu : 0 < u) (hu' : u < 1) (ht : 0 ≤ t) :
    peetre p t = 1-u ↔ t = inverseK p u := by
  obtain ⟨z,hz,heq,hlevel⟩ := inverse_attained hp hu hu'
  constructor
  · intro h
    have hmin : inverseK p u ≤ t := csInf_le (s := {v : ℝ | 0 ≤ v ∧ 1-u ≤ peetre p v})
      ⟨0,fun _ h => h.1⟩ ⟨ht,h.ge⟩
    by_contra hn
    have hlt : ell2 z < t := heq.trans_lt (lt_of_le_of_ne hmin (Ne.symm hn))
    obtain ⟨y,_,_,hy⟩ := inverse_attained hp (show 0 < u/2 by linarith) (show u/2 < 1 by linarith)
    have str : 1-u < peetre p (ell2 y) := by rw [hy]; linarith
    have htY : t < ell2 y := by
      by_contra! hle
      have hm := increasing hp (show 0 ≤ ell2 y from Real.sqrt_nonneg _) hle
      linarith
    let w := (t-ell2 z)/(ell2 y-ell2 z)
    have denom : 0 < ell2 y-ell2 z := sub_pos.mpr (hlt.trans htY)
    have wp : 0 < w := div_pos (sub_pos.mpr hlt) denom
    have w1 : w ≤ 1 := (div_le_one denom).mpr (by linarith)
    have interpolate : (1-w)*ell2 z + w*ell2 y = t := by
      dsimp only [w]
      field_simp [denom.ne']
      ring
    have hm := concave_mix (r := ell2 z) (t := ell2 y) hp (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) wp.le w1
    rw [interpolate,hlevel,h] at hm
    nlinarith [mul_pos wp (sub_pos.mpr str)]
  · rintro rfl
    rwa [← heq]

end
end Canonne
