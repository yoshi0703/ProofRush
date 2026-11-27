import ColoredPilot
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace CanonneColoredPilot

open scoped BigOperators
noncomputable section

/-- Bin pilots trade the same weighted bin moment between occupancy cost
and overlap cost, while rounding contributes at most one top atom per bin. -/
def pilotCount (c b u : ℝ) : ℕ := ⌈c * b / Real.sqrt u⌉₊

theorem pilotCount_pos {c b u : ℝ} (hc : 0 < c) (hb : 0 < b) (hu : 0 < u) :
    0 < pilotCount c b u := by
  rw [pilotCount, Nat.ceil_pos]
  exact div_pos (mul_pos hc hb) (Real.sqrt_pos.2 hu)

theorem support_cost_upper {c b u : ℝ} (hc : 0 < c) (hb : 0 < b) (hu : 0 < u) :
    (pilotCount c b u : ℝ) * u ≤ c * b * Real.sqrt u + u := by
  have hroot := Real.sqrt_pos.2 hu
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ c * b / Real.sqrt u by positivity)).le
  have hm := mul_le_mul_of_nonneg_right hceil hu.le
  have hu' := Real.sq_sqrt hu.le
  unfold pilotCount
  calc
    _ ≤ (c * b / Real.sqrt u + 1) * u := hm
    _ = _ := by
      calc
        _ = (c * b / Real.sqrt u + 1) * (Real.sqrt u)^2 := by rw [hu']
        _ = _ := by field_simp [hroot.ne']; nlinarith

theorem collision_cost_upper {c b u s : ℝ} (hc : 0 < c) (hb : 0 < b) (hu : 0 < u) :
    (s*b)^2 / (pilotCount c b u : ℝ) ≤ (s^2 / c) * (b * Real.sqrt u) := by
  have hroot := Real.sqrt_pos.2 hu
  let a := c * b / Real.sqrt u
  have ha : 0 < a := div_pos (mul_pos hc hb) hroot
  calc
    _ ≤ (s*b)^2 / a := div_le_div_of_nonneg_left (sq_nonneg _) ha (Nat.le_ceil a)
    _ = _ := by
      dsimp [a]
      field_simp [hc.ne', hb.ne', hroot.ne']

theorem light_bin_moment {X : Type*} (band : Finset X) (r : X → ℝ) (u : ℝ)
    (nonneg : ∀ i ∈ band, 0 ≤ r i) (ratio : ∀ i ∈ band, u ≤ 2 * r i) :
    (∑ i ∈ band, r i) * Real.sqrt u ≤
      Real.sqrt 2 * ∑ i ∈ band, r i * Real.sqrt (r i) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := Real.sqrt_le_sqrt (ratio i hi)
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num)] at hh
  calc
    _ ≤ r i * (Real.sqrt 2 * Real.sqrt (r i)) := mul_le_mul_of_nonneg_left hh (nonneg i hi)
    _ = _ := by ring

theorem dyadic_top_sum {top : ℝ} (htop : 0 ≤ top) (bins : Finset ℕ) :
    ∑ j ∈ bins, top * (1/2 : ℝ)^j ≤ 2 * top := by
  obtain ⟨J, hJ⟩ := Finset.exists_nat_subset_range bins
  have geom (m : ℕ) : (∑ j ∈ Finset.range m, top * (1/2 : ℝ)^j)
      + 2 * top * (1/2 : ℝ)^m = 2 * top := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith
  calc
    _ ≤ ∑ j ∈ Finset.range J, top * (1/2 : ℝ)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hJ fun _ _ _ => by positivity
    _ ≤ _ := by linarith [geom J, show 0 ≤ 2 * top * (1/2 : ℝ)^J by positivity]

end
end CanonneColoredPilot
