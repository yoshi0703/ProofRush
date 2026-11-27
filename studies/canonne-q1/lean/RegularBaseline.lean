import TestingBaseline
import RegularAtScale

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting
open CanonneQuantile
open scoped BigOperators
noncomputable section

theorem testing_baseline_budgets {A : Type*} [Fintype A] {q : A → ℝ} (hq : IsLaw q)
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hregular : CanonneNearOne.nearOneMoment q (1-e) ≤ 32*(1-e))
    (hfar : ∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q)
    {m : ℕ} (htest : ∃ f, GoodTest q e m f) :
    0 < m ∧ (1:ℝ)/3 ≤ (m:ℝ)*e ∧ (1:ℝ)/2048 < (m:ℝ)*(1-e) := by
  classical
  have hm : 0 < m := by
    by_contra hb
    have hz : m = 0 := Nat.eq_zero_of_not_pos hb
    exact no_zero_sample_good_test hfar (hz ▸ htest)
  refine ⟨hm, good_test_radius_budget hq he hfar htest, ?_⟩
  by_contra hb
  have hsmall : (m:ℝ)*CanonneNearOne.nearOneMoment q (1-e) ≤ 1/64 := by
    nlinarith only [mul_le_mul_of_nonneg_left hregular (Nat.cast_nonneg m : (0:ℝ) ≤ m), le_of_not_gt hb]
  exact no_good_test_small_near_one_moment hq hm (sub_pos.mpr he1) hsmall
    (show ∃ f, GoodTest q (1-(1-e)) m f by
      rw [show 1-(1-e) = e by ring]
      exact htest)

def amplifiedBudget (m : ℕ) : ℕ := 8796093022208 * m

/-- If the two basic budgets are large, the marker necessary condition
alone removes the \(1/n\) floor from the weak crossing. This remains true
when the marker has zero mass. -/
theorem regular_signal_ge_integer_floor {n e w X : ℝ} (hn : 0 < n)
    (hw0 : 0 ≤ w) (hwe : w ≤ e) (he1 : e < 1) (hX : 0 ≤ X)
    (hne : 4294967296 ≤ n*e) (hnd : 4294967296 ≤ n*(1-e))
    (hmarker : Real.sqrt (w*(1-w)/n) ≤ 8*(e-w+4096*max X (1/n))) :
    1 ≤ n*(e-w+X) := by
  by_contra hb
  have hsmall := lt_of_not_ge hb
  have hDelta : n*(e-w) < 1 := by nlinarith [mul_nonneg hn.le hX]
  have hXn : X ≤ 1/n := by
    apply (le_div_iff₀ hn).mpr
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hwe)]
  rw [max_eq_right hXn] at hmarker
  have h1 : n*(4096*(1/n)) = 4096 := by field_simp [hn.ne']
  have h0 : 0 ≤ w*(1-w)/n := by
    exact div_nonneg (mul_nonneg hw0 (by linarith)) hn.le
  have hscaled : n*Real.sqrt (w*(1-w)/n) ≤ 32776 := by
    nlinarith only [mul_le_mul_of_nonneg_left hmarker hn.le, hDelta, h1]
  have hsq : (n*Real.sqrt (w*(1-w)/n))^2 = n*w*(1-w) := by
    rw [mul_pow, Real.sq_sqrt h0]
    field_simp [hn.ne']
  have hbinom : n*w*(1-w) ≤ (32776:ℝ)^2 := by
    rw [← hsq]
    exact (sq_le_sq₀ (mul_nonneg hn.le (Real.sqrt_nonneg _)) (by norm_num)).mpr hscaled
  by_cases hw : w ≤ 1/2
  · have hh := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ 1-w by linarith)
      (mul_nonneg hn.le hw0)
    nlinarith only [hbinom, hh, hne, hDelta]
  · have hh := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ w by linarith)
      (show 0 ≤ n*(1-w) by exact mul_nonneg hn.le (by linarith))
    have hsub := mul_le_mul_of_nonneg_left (show 1-e ≤ 1-w by linarith) hn.le
    nlinarith only [hbinom, hh, hsub, hnd]

section Crossing

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- X at sample budget n, in the original (unsquared) probability-mass
coordinates of the testing problem. The root is in square-root coordinates. -/
def tailOverlapSquare (q : H ⊕ T → ℝ) (hq : IsLaw q) (n : ℕ) : ℝ :=
  (root (fun t : T => q (Sum.inr t)) (fun t => hq.nonneg (Sum.inr t)) n (Nat.cast_nonneg n)) ^ 2

def reverseTolerance (q : H ⊕ T → ℝ) (hq : IsLaw q) (n : ℕ) : ℝ :=
  4096*max (tailOverlapSquare q hq n) (1/(n:ℝ))

/-- Use the same statistical error levels at the enlarged fixed budget
by selecting the first m records. The supplied head contribution is the
only external part of the weak crossing inequality. -/
theorem weak_crossing_at_fixed_amplification
    {q : H ⊕ T → ℝ} (hq : IsLaw q) {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hwe : (∑ t : T, q (Sum.inr t)) ≤ e)
    (hreg : CanonneNearOne.nearOneMoment q (1-e) ≤ 32*(1-e))
    (hnonempty : ∃ p : H ⊕ T → ℝ, IsLaw p ∧ e < totalVariation p q)
    {m : ℕ} (htest : ∃ f, GoodTest q e m f)
    {CH cost : ℝ} (hCH : 0 ≤ CH)
    (hhead : let n := amplifiedBudget m
      (∃ f, GoodTest q e n f) →
      cost ≤ CH*(e-(∑ t : T, q (Sum.inr t))+reverseTolerance q hq n)) :
    let n := amplifiedBudget m
    let w := ∑ t : T, q (Sum.inr t)
    let X := tailOverlapSquare q hq n
    let D := Real.sqrt (w*(1-w)/(n:ℝ)) + 1/(n:ℝ) + cost
    D ≤ ((8+CH)*4097+1)*(e-w+X) := by
  classical
  let n := amplifiedBudget m
  let w := ∑ t : T, q (Sum.inr t)
  let R := root (fun t : T => q (Sum.inr t)) (fun t => hq.nonneg (Sum.inr t)) n (Nat.cast_nonneg n)
  let X := tailOverlapSquare q hq n
  let x := reverseTolerance q hq n
  let Y := e-w+X
  have hXdef : X = R^2 := rfl
  have hxdef : x = 4096*max X (1/(n:ℝ)) := rfl
  change Real.sqrt (w*(1-w)/(n:ℝ)) + 1/(n:ℝ) + cost ≤ ((8+CH)*4097+1)*Y
  have hw : 0 ≤ w := Finset.sum_nonneg (fun t _ => hq.nonneg _)
  have hX : 0 ≤ X := by rw [hXdef]; exact sq_nonneg _
  have hY : 0 ≤ Y := by unfold Y; linarith
  obtain ⟨hm, hme, hmd⟩ := testing_baseline_budgets hq he he1 hreg hnonempty htest
  have hmn : m ≤ n := Nat.le_mul_of_pos_left m (by decide)
  have hn : 0 < n := hm.trans_le hmn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have htestN : ∃ f, GoodTest q e n f := good_test_budget_monotone hq hmn htest
  have hNcast : (n:ℝ) = 8796093022208*(m:ℝ) := by unfold n amplifiedBudget; norm_num
  have hNe : 4294967296 ≤ (n:ℝ)*e := by rw [hNcast]; nlinarith only [hme]
  have hNδ : 4294967296 ≤ (n:ℝ)*(1-e) := by rw [hNcast]; nlinarith only [hmd]
  have hNA : 1 ≤ (n:ℝ)*(1-w) := by
    nlinarith only [hNδ, mul_le_mul_of_nonneg_left (show 1-e ≤ 1-w by linarith) hnR.le]
  have hxf : 4096*(1/(n:ℝ)) ≤ x :=
    hxdef ▸ mul_le_mul_of_nonneg_left (le_max_right X _) (by norm_num)
  have hx : 0 < x := (by positivity : 0 < 4096*(1/(n:ℝ))).trans_le hxf
  have hnx : 8 ≤ (n:ℝ)*x := by
    have heq : (n:ℝ)*(4096*(1/(n:ℝ))) = 4096 := by field_simp [hnR.ne']
    nlinarith only [heq, mul_le_mul_of_nonneg_left hxf hnR.le]
  have hroot : 64*R ≤ Real.sqrt x := by
    have hR : 0 ≤ R := (root_spec (fun t : T => q (Sum.inr t))
      (fun t => hq.nonneg (Sum.inr t)) (Nat.cast_nonneg n)).1
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) hR) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hx.le, show (64*R)^2 = 4096*X by rw [hXdef]; ring]
    exact hxdef ▸ mul_le_mul_of_nonneg_left (le_max_left X _) (by norm_num)
  have hmass := marker_mass_necessary_at_regular_scale hn hq hx hnx hNA hwe hroot htestN
  change Real.sqrt (w*(1-w)/(n:ℝ)) ≤ 8*(e-w+x) at hmass
  have hheadCost : cost ≤ CH*(e-w+x) := hhead htestN
  have hYfloor : 1 ≤ (n:ℝ)*Y :=
    regular_signal_ge_integer_floor hnR hw hwe he1 hX hNe hNδ (by simpa only [hxdef] using hmass)
  have hInv : (1:ℝ)/(n:ℝ) ≤ Y := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith only [hYfloor]
  have hXY : X ≤ Y := by unfold Y; linarith
  have hxY : x ≤ 4096*Y := hxdef ▸ mul_le_mul_of_nonneg_left (max_le hXY hInv) (by norm_num)
  have hDeltaX : e-w+x ≤ 4097*Y := by unfold Y at *; linarith
  nlinarith only [hmass, hheadCost, hInv,
    mul_le_mul_of_nonneg_left hDeltaX (show 0 ≤ 8+CH by linarith)]

end Crossing

end
end CanonneRegularTransfer
