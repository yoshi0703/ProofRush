import CrossBirthday

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem law_mass_bounds (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    0 ≤ mass p T ∧ mass p T ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun a _ => hp.nonneg a), ?_⟩
  rw [← hp.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun a _ _ => hp.nonneg a)

def groupValue (T : Finset A) (a : A) : ℝ := if a ∈ T then 1 else 0

def groupCount {n : ℕ} (T : Finset A) (x : Fin n → A) : ℝ := ∑ i, groupValue T (x i)

/-- Exact binomial variance under the literal ordered iid product law. -/
theorem group_count_variance {n : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    (∑ x : Fin n → A, pilotLaw p x *
      (groupCount T x-(n : ℝ)*mass p T)^2) =
      (n : ℝ)*mass p T*(1-mass p T) := by
  let s := mass p T
  let g (a : A) := groupValue T a-s
  have first : (∑ a, p a * groupValue T a) = s := by simp [groupValue, s, mass, mul_ite]
  have hconst : (∑ a, p a*s) = s := by rw [← Finset.sum_mul, hp.total, one_mul]
  have mean : ∑ a, p a*g a = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, first, hconst, sub_self]
  have transform (x : Fin n → A) : (∑ i, g (x i)) = groupCount T x-(n : ℝ)*s := by
    simp [groupCount, g, Finset.sum_sub_distrib, nsmul_eq_mul]
  have second : (∑ a, p a*(g a)^2) = s*(1-s) := by
    have point (a : A) : p a*(g a)^2 = (1-2*s)*(p a*groupValue T a)+p a*s^2 := by
      by_cases h : a ∈ T
      · simp [g, groupValue, h]
        ring
      · simp [g, groupValue, h]
    simp only [point, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.sum_mul, first, hp.total, one_mul]
    ring
  have h := centered_sum_second_moment (n := n) hp g mean
  simp only [transform, second] at h
  calc
    _ = (n : ℝ)*(s*(1-s)) := h
    _ = _ := by dsimp [s]; ring

theorem group_count_deviation {n : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    {d : ℝ} (hd : 0 < d) :
    eventMass (pilotLaw p) (fun x : Fin n → A =>
      d ≤ |groupCount T x-(n : ℝ)*mass p T|) ≤
      ((n : ℝ)*mass p T*(1-mass p T))/d^2 := by
  simpa only [group_count_variance T hp] using
    finite_squared_deviation_bound (pilotLaw_isLaw hp).nonneg
      (fun x : Fin n → A => groupCount T x-(n : ℝ)*mass p T) hd

def groupScale (q : A → ℝ) (T : Finset A) (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ)*(mass q T*(1-mass q T)))+1

def groupMassReject {n : ℕ} (q : A → ℝ) (T : Finset A) (x : Fin n → A) : Prop :=
  512*groupScale q T n < |groupCount T x-(n : ℝ)*mass q T|

omit [DecidableEq A] in
theorem groupScale_div (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {n : ℕ} (hn : 0 < n) :
    groupScale q T n/(n : ℝ) =
      Real.sqrt (mass q T*(1-mass q T)/(n : ℝ))+1/(n : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨h₁,h₂⟩ := law_mass_bounds T hq
  have hv : 0 ≤ mass q T*(1-mass q T) := mul_nonneg h₁ (sub_nonneg.mpr h₂)
  unfold groupScale
  rw [add_div, Real.sqrt_mul hn'.le, Real.sqrt_div hv]
  congr 1
  have hr := Real.sqrt_pos.mpr hn'
  field_simp [hn'.ne', hr.ne']
  rw [Real.sq_sqrt hn'.le]
  ring

theorem group_gate_null {n : ℕ} (q : A → ℝ) (hq : IsLaw q) (T : Finset A) :
    eventMass (pilotLaw q) (groupMassReject (n := n) q T) ≤ 1/100 := by
  have hpos : 0 < 512*groupScale q T n := by unfold groupScale; positivity
  refine (finite_eventMass_mono (pilotLaw_isLaw hq).nonneg (fun x hx => (show
    512*groupScale q T n < |groupCount T x-(n : ℝ)*mass q T| from hx).le)).trans
    ((group_count_deviation T hq hpos).trans ?_)
  obtain ⟨h₁,h₂⟩ := law_mass_bounds T hq
  have hv : 0 ≤ (n : ℝ)*(mass q T*(1-mass q T)) :=
    mul_nonneg (Nat.cast_nonneg n) (mul_nonneg h₁ (sub_nonneg.mpr h₂))
  rw [div_le_iff₀ (sq_pos_of_pos hpos)]
  have hL : (n : ℝ)*(mass q T*(1-mass q T)) ≤ (groupScale q T n)^2 := by
    unfold groupScale
    nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg ((n : ℝ)*(mass q T*(1-mass q T)))]
  nlinarith [sq_nonneg (groupScale q T n)]

private theorem quadratic_mass_variance_le {s w : ℝ}
    (hs : 0 ≤ s ∧ s ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    s*(1-s) ≤ w*(1-w)+|s-w| := by
  have hf : |1-s-w| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2,hw.2],by linarith [hs.1,hw.1]⟩
  have point : s*(1-s)-w*(1-w)=(s-w)*(1-s-w) := by ring
  have hm := (le_abs_self ((s-w)*(1-s-w))).trans (show
    |(s-w)*(1-s-w)| ≤ |s-w| by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hf)
  linarith

theorem group_gate_alternative {n : ℕ} (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {p : A → ℝ} (hp : IsLaw p)
    (hfar : 1024*groupScale q T n < (n : ℝ)*|mass p T-mass q T|) :
    eventMass (pilotLaw p) (fun x => ¬ groupMassReject (n := n) q T x) ≤ 1/100 := by
  let w := mass q T
  let s := mass p T
  let d := (n : ℝ)*|s-w|
  let L := groupScale q T n
  have hL : 1 ≤ L := by unfold L groupScale; linarith [Real.sqrt_nonneg ((n : ℝ)*(w*(1-w)))]
  have hlarge : 1024*L ≤ d := hfar.le
  have hd : 0 < d/2 := by linarith
  refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg ?_).trans
    ((group_count_deviation T hp hd).trans ?_)
  · intro x hx
    have ht : |groupCount T x-(n : ℝ)*w| ≤ 512*L := le_of_not_gt hx
    have hh := abs_sub_le ((n : ℝ)*s) (groupCount T x) ((n : ℝ)*w)
    have eq : |(n : ℝ)*s-(n : ℝ)*w|=d := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [eq, abs_sub_comm ((n : ℝ)*s)] at hh
    change d/2 ≤ |groupCount T x-(n : ℝ)*s|
    linarith
  · have hw := law_mass_bounds T hq
    have hs := law_mass_bounds T hp
    have hv : 0 ≤ (n : ℝ)*(w*(1-w)) :=
      mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hw.1 (sub_nonneg.mpr hw.2))
    have hvL : (n : ℝ)*(w*(1-w)) ≤ L^2 := by
      change _ ≤ (Real.sqrt ((n : ℝ)*(w*(1-w)))+1)^2
      nlinarith [Real.sq_sqrt hv, Real.sqrt_nonneg ((n : ℝ)*(w*(1-w)))]
    have hc := mul_le_mul_of_nonneg_left (quadratic_mass_variance_le hs hw) (Nat.cast_nonneg n)
    change (n : ℝ)*(s*(1-s)) ≤ (n : ℝ)*(w*(1-w)+|s-w|) at hc
    have first : L^2 ≤ (d/1024)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have second := mul_le_mul_of_nonneg_right (show (1024 : ℝ) ≤ d by linarith)
      (show 0 ≤ d by linarith)
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    change (n : ℝ)*s*(1-s) ≤ _
    have he : d = (n : ℝ)*|s-w| := rfl
    nlinarith

/-- The same fixed-size gate detects a sufficiently large surplus on a
light label set, including when the null mass of the set is zero. -/
theorem group_gate_light_power {n : ℕ} (hn : 0 < n) (q : A → ℝ) (hq : IsLaw q)
    (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    (hfar : 4096*(mass q T+1/(n : ℝ)) < mass p T) :
    eventMass (pilotLaw p) (fun z => ¬ groupMassReject (n := n) q T z) ≤ 1/100 := by
  let w := mass q T
  let s := mass p T
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hw := law_mass_bounds T hq
  change 0 ≤ w ∧ w ≤ 1 at hw
  have hw' : 0 ≤ (n : ℝ)*w := mul_nonneg hn'.le hw.1
  have hv : (n : ℝ)*(w*(1-w)) ≤ (n : ℝ)*w := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right hw.1 (by linarith [hw.1])) hn'.le
  have lower : Real.sqrt ((n : ℝ)*w) ≤ (n : ℝ)*w+1 := by
    nlinarith [Real.sq_sqrt hw', sq_nonneg (Real.sqrt ((n : ℝ)*w) - 1/2)]
  have scale : groupScale q T n ≤ (n : ℝ)*w+2 := by
    change Real.sqrt ((n : ℝ)*(w*(1-w)))+1 ≤ _
    linarith [(Real.sqrt_le_sqrt hv).trans lower]
  have mul := mul_lt_mul_of_pos_left hfar hn'
  change (n : ℝ)*(4096*(w+1/(n : ℝ))) < (n : ℝ)*s at mul
  have same : (n : ℝ)*(4096*(w+1/(n : ℝ))) = 4096*((n : ℝ)*w+1) := by
    field_simp [hn'.ne']
  rw [same] at mul
  have large : 1024*groupScale q T n < (n : ℝ)*(s-w) := by
    nlinarith
  exact group_gate_alternative q hq T hp
    (large.trans_le (mul_le_mul_of_nonneg_left (le_abs_self _) hn'.le))

end
end CanonneQuantile
