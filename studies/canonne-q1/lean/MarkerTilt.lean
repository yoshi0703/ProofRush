import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CanonneMarker

open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A]

def recordLaw (q : A → ℝ) {n : ℕ} (x : Fin n → A) : ℝ := ∏ i, q (x i)

theorem record_moment (q f : A → ℝ) (n : ℕ) :
    (∑ x : Fin n → A, recordLaw q x * recordLaw f x) = (∑ i, q i * f i)^n := by
  classical
  unfold recordLaw
  simp only [← Finset.prod_mul_distrib]
  calc
    _ = ∏ _i : Fin n, ∑ a, q a*f a :=
      (Fintype.prod_sum (fun (_ : Fin n) (a : A) => q a*f a)).symm
    _ = _ := by simp

theorem weighted_absolute_sq (q r : A → ℝ) (hq : ∀ i, 0 ≤ q i) :
    (∑ i, q i * |r i|)^2 ≤ (∑ i, q i) * ∑ i, q i*(r i)^2 := by
  have hprod (i : A) : Real.sqrt (q i) * (Real.sqrt (q i)*|r i|) = q i*|r i| := by
    rw [← mul_assoc, Real.mul_self_sqrt (hq i)]
  have hsquare (i : A) : (Real.sqrt (q i)*|r i|)^2 = q i*(r i)^2 := by
    rw [mul_pow, Real.sq_sqrt (hq i), sq_abs]
  simpa only [hprod, Real.sq_sqrt (hq _), hsquare] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (q i))
      (fun i => Real.sqrt (q i)*|r i|))

/-- The squared L1 distance of the actual ordered product laws is bounded
by their chi-square divergence; zero atoms outside the likelihood support
are allowed for the null. -/
theorem product_likelihood_L1_sq (q L : A → ℝ) (hq : ∀ i, 0 ≤ q i)
    (h1 : ∑ i, q i = 1) (hL : ∑ i, q i*L i = 1) (n : ℕ) :
    (∑ x : Fin n → A, |recordLaw (fun i => q i*L i) x - recordLaw q x|)^2
      ≤ (∑ i, q i*(L i)^2)^n - 1 := by
  classical
  let Q := recordLaw (n := n) q
  let R := recordLaw (n := n) L
  have hQ x : 0 ≤ Q x := Finset.prod_nonneg fun i _ => hq (x i)
  have heq (x : Fin n → A) :
      |recordLaw (fun i => q i*L i) x - recordLaw q x| = Q x*|R x-1| := by
    change |(∏ i, q (x i)*L (x i)) - Q x| = _
    rw [Finset.prod_mul_distrib]
    change |Q x*R x-Q x| = _
    rw [← mul_sub_one, abs_mul, abs_of_nonneg (hQ x)]
  have hQ1 : ∑ x, Q x = 1 := by
    simpa only [recordLaw, Finset.prod_const_one, mul_one, h1, one_pow, Q]
      using record_moment q (fun _ => 1) n
  have hR1 : ∑ x, Q x*R x = 1 := by simpa [Q,R,hL] using record_moment q L n
  have hR2 : (∑ x, Q x*(R x)^2) = (∑ i, q i*(L i)^2)^n := by
    have he (x : Fin n → A) : (R x)^2 = recordLaw (fun i => (L i)^2) x := by
      simp only [R,recordLaw,pow_two,Finset.prod_mul_distrib]
    simpa only [he,Q] using record_moment q (fun i => (L i)^2) n
  have hdiff (x) : Q x*(R x-1)^2 = Q x*(R x)^2-2*(Q x*R x)+Q x := by ring
  have hsum : (∑ x, Q x*(R x-1)^2) = (∑ i, q i*(L i)^2)^n - 1 := by
    rw [Finset.sum_congr rfl (fun x _ => hdiff x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hR2, hR1, hQ1]
    ring
  have hv := weighted_absolute_sq Q (fun x => R x-1) hQ
  rw [hQ1,one_mul,hsum] at hv
  simpa only [heq] using hv

variable [DecidableEq A]

theorem tag_sums (q : A → ℝ) (T : Finset A) {w : ℝ} (hT : ∑ i ∈ T, q i = w)
    (h1 : ∑ i, q i = 1) (u v : ℝ) :
    (∑ i, q i*(if i ∈ T then u else v)) = w*u+(1-w)*v := by
  have hc : ∑ i ∈ Tᶜ, q i = 1-w := by linarith [T.sum_add_sum_compl q]
  rw [← T.sum_add_sum_compl]
  have eq1 : (∑ i ∈ T, q i*(if i ∈ T then u else v)) = (∑ i ∈ T, q i)*u := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => by rw [ite_eq_left hi])
  have eq2 : (∑ i ∈ Tᶜ, q i*(if i ∈ T then u else v)) = (∑ i ∈ Tᶜ, q i)*v := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => by rw [ite_eq_right (Finset.mem_compl.mp hi)])
  rw [eq1,eq2,hT,hc]

def shifted (q : A → ℝ) (T : Finset A) (w d : ℝ) (i : A) : ℝ :=
  q i * (if i ∈ T then (w+d)/w else (1-w-d)/(1-w))

theorem shifted_law (q : A → ℝ) (hq : ∀ i, 0 ≤ q i) (h1 : ∑ i, q i = 1)
    (T : Finset A) {w d : ℝ} (hT : ∑ i ∈ T, q i = w) (hw : 0 < w) (hA : w < 1)
    (hplus : 0 ≤ w+d) (hrest : 0 ≤ 1-w-d) :
    (∀ i, 0 ≤ shifted q T w d i) ∧ (∑ i, shifted q T w d i = 1) := by
  constructor
  · intro i
    apply mul_nonneg (hq i)
    split
    · exact div_nonneg hplus hw.le
    · exact div_nonneg hrest (sub_nonneg.mpr hA.le)
  · unfold shifted
    rw [tag_sums q T hT h1]
    field_simp [hw.ne', (sub_pos.mpr hA).ne']
    ring

theorem marker_L1_sq (q : A → ℝ) (hq : ∀ i, 0 ≤ q i) (h1 : ∑ i, q i = 1)
    (T : Finset A) {w d : ℝ} (hT : ∑ i ∈ T, q i = w) (hw : 0 < w) (hA : w < 1)
    (hplus : 0 ≤ w+d) (hrest : 0 ≤ 1-w-d) (n : ℕ) :
    (∑ x : Fin n → A, |recordLaw (shifted q T w d) x-recordLaw q x|)^2
      ≤ (1+d^2/(w*(1-w)))^n - 1 := by
  let u := (w+d)/w
  let v := (1-w-d)/(1-w)
  let L (i : A) := if i ∈ T then u else v
  have hL : ∑ i, q i*L i = 1 := (shifted_law q hq h1 T hT hw hA hplus hrest).2
  have heq (i : A) : (L i)^2 = if i ∈ T then u^2 else v^2 := by by_cases h : i ∈ T <;> simp [L,h]
  have h2 : (∑ i, q i*(L i)^2) = 1+d^2/(w*(1-w)) := by
    simp only [heq, tag_sums q T hT h1]
    unfold u v
    field_simp [hw.ne', (sub_pos.mpr hA).ne']
    ring
  have hm := product_likelihood_L1_sq q L hq h1 hL n
  rw [h2] at hm
  exact hm

private theorem small_power (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hsmall : n*x ≤ 1/64) :
    (1+x)^n ≤ 64/63 := by
  have hx1 : 0 < 1+x := by linarith
  have ha : 0 ≤ (1+x)⁻¹ := inv_nonneg.mpr hx1.le
  have hcomp : -x ≤ (1+x)⁻¹-1 := by
    by_contra! hh
    have h := mul_lt_mul_of_pos_left hh hx1
    nlinarith [mul_inv_cancel₀ hx1.ne', sq_nonneg x]
  have hn : (0 : ℝ) ≤ n := by positivity
  have hlo := one_add_mul_sub_le_pow (show -1 ≤ (1+x)⁻¹ by linarith) n
  rw [inv_pow] at hlo
  have hbound : 63/64 ≤ ((1+x)^n)⁻¹ := by
    linarith [mul_le_mul_of_nonneg_left hcomp hn]
  have hmul := mul_le_mul_of_nonneg_right hbound (pow_nonneg hx1.le n)
  rw [inv_mul_cancel₀ (pow_ne_zero n hx1.ne')] at hmul
  linarith

theorem marker_tv_at_scale (q : A → ℝ) (hq : ∀ i, 0 ≤ q i) (h1 : ∑ i, q i = 1)
    (T : Finset A) {w d : ℝ} (hT : ∑ i ∈ T, q i = w) (hw : 0 < w) (hA : w < 1)
    (hplus : 0 ≤ w+d) (hrest : 0 ≤ 1-w-d) (n : ℕ)
    (hshift : n*(d^2/(w*(1-w))) ≤ 1/64) :
    (∑ x : Fin n → A, |recordLaw (shifted q T w d) x-recordLaw q x|)/2 ≤ 1/12 := by
  have hwA : 0 < w*(1-w) := mul_pos hw (sub_pos.mpr hA)
  have hchi := marker_L1_sq q hq h1 T hT hw hA hplus hrest n
  have hpow := small_power n (div_nonneg (sq_nonneg d) hwA.le) hshift
  nlinarith [sq_nonneg ((∑ x : Fin n → A, |recordLaw (shifted q T w d) x-recordLaw q x|)-1/6)]

end
end CanonneMarker
