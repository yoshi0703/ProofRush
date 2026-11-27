import IIDHead
import CrossBirthday

namespace CanonneIIDHead

open CanonneDiffuse CanonneHeadTransfer CanonneQuantile
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def rawScore {n : ℕ} (q u : A → ℝ) (z : Fin (n+n) → A) : ℝ :=
  pairScore u q (firstBatch z) (lastBatch z)

def rejects {n : ℕ} (q u : A → ℝ) (t : ℝ) (z : Fin (n+n) → A) : Prop :=
  32*(n:ℝ)^2*t < rawScore q u z

theorem score_null_error {q : A → ℝ} (hq : IsLaw q) (u : A → ℝ) {n : ℕ} (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) (hW : (∑ a, (u a)^2*(q a)^2) ≤ ((n:ℝ)*t)^2) :
    eventMass (pilotLaw q) (rejects (n:=n) q u t) ≤ 1/100 := by
  let a := 32*(n:ℝ)^2*t
  have ha : 0 < a := by dsimp [a]; positivity
  have hsecond := iid_head_quadratic_error hq q u n
  simp only [shapeSignal,sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,Finset.sum_const_zero,
    sub_zero, add_zero] at hsecond
  have hM := finite_squared_deviation_bound (pilotLaw_isLaw (I:=Fin (n+n)) hq).nonneg
    (rawScore (n:=n) q u) ha
  have herr : eventMass (pilotLaw q) (rejects (n:=n) q u t) ≤
      eventMass (pilotLaw q) (fun z => a ≤ |rawScore (n:=n) q u z|) := by
    classical
    apply finite_eventMass_mono (pilotLaw_isLaw hq).nonneg
    intro z hz
    exact (le_of_lt hz).trans (le_abs_self _)
  refine herr.trans (hM.trans ?_)
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  change E (pilotLaw q) (fun z : Fin (n+n) → A => (rawScore q u z)^2) ≤ _
  refine hsecond.trans ?_
  dsimp [a]
  nlinarith only [mul_le_mul_of_nonneg_left hW (sq_nonneg (n:ℝ)),
      sq_nonneg ((n:ℝ)^2*t)]

omit [DecidableEq A] in
theorem square_budget_alternative (p q u : A → ℝ) (hu : ∀ a, 0 ≤ u a) (U : ℝ)
    (hcap : ∀ a, u a ≤ U) :
    (∑ a, (u a)^2*(p a)^2) ≤ 2*(∑ a, (u a)^2*(q a)^2) + 2*U*shapeSignal u p q := by
  unfold shapeSignal
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have h1 : (p a)^2 ≤ 2*(q a)^2+2*(p a-q a)^2 := by nlinarith [sq_nonneg (p a-2*q a)]
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (u a))
  have h3 := mul_le_mul_of_nonneg_right (hcap a) (mul_nonneg (hu a) (sq_nonneg (p a-q a)))
  nlinarith

omit [DecidableEq A] in
theorem linear_budget_alternative {p q u : A → ℝ} (hu : ∀ a, 0 ≤ u a) {n t : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hcap : ∀ a, u a ≤ n^2*t) (hnull : ∀ a, u a*q a ≤ n*t)
    (hpower : 100000000*t ≤ shapeSignal u p q) :
    (∑ a, p a*(u a*(p a-q a))^2) ≤ (n*t+n*shapeSignal u p q/10000)*shapeSignal u p q := by
  classical
  let V := shapeSignal u p q
  have hV : 0 < V := (mul_pos (by norm_num) ht).trans_le hpower
  have hcoord (a) : u a * (p a-q a)^2 ≤ V :=
    Finset.single_le_sum (fun a _ => mul_nonneg (hu a) (sq_nonneg _)) (Finset.mem_univ a)
  have hbound (a) : u a*(p a-q a) ≤ n*V/10000 := by
    have hp := mul_le_mul (hcap a) (hcoord a)
      (mul_nonneg (hu a) (sq_nonneg _)) (mul_nonneg (sq_nonneg n) ht.le)
    have hscale := mul_le_mul_of_nonneg_right hpower (mul_nonneg (sq_nonneg n) hV.le)
    have hsq : (u a*(p a-q a))^2 ≤ (n*V/10000)^2 := by
      change 100000000*t ≤ V at hpower
      change (100000000*t)*(n^2*V) ≤ V*(n^2*V) at hscale
      nlinarith only [hp,hscale]
    exact le_of_sq_le_sq hsq (by positivity)
  have hpoint a : u a*p a ≤ n*t+n*V/10000 := by linarith [hnull a,hbound a]
  change _ ≤ (n*t+n*V/10000)*shapeSignal u p q
  unfold shapeSignal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  nlinarith only [mul_le_mul_of_nonneg_right (hpoint a) (mul_nonneg (hu a) (sq_nonneg (p a-q a)))]

theorem score_alt_error {p q u : A → ℝ} (hp : IsLaw p) (hu : ∀ a, 0 ≤ u a)
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t)
    (hW : (∑ a, (u a)^2*(q a)^2) ≤ ((n:ℝ)*t)^2) (hcap : ∀ a, u a ≤ (n:ℝ)^2*t)
    (hnull : ∀ a, u a*q a ≤ (n:ℝ)*t) (hpower : 100000000*t ≤ shapeSignal u p q) :
    eventMass (pilotLaw p) (fun z => ¬ rejects (n:=n) q u t z) ≤ 1/100 := by
  let V := shapeSignal u p q
  let L := (n:ℝ)^2*V/2
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hV : 0 < V := (mul_pos (by norm_num) ht).trans_le hpower
  have hL : 0 < L := by dsimp [L]; positivity
  have hth : 32*(n:ℝ)^2*t ≤ (n:ℝ)^2*V/2 := by
    have hrel : 32*t ≤ V/2 := by change 100000000*t ≤ V at hpower; linarith
    nlinarith only [mul_le_mul_of_nonneg_left hrel (sq_nonneg (n:ℝ))]
  let g (z : Fin (n+n) → A) := rawScore q u z - (n:ℝ)^2*V
  have hevent : eventMass (pilotLaw p) (fun z => ¬ rejects (n:=n) q u t z) ≤
      eventMass (pilotLaw p) (fun z => L ≤ |g z|) := by
    apply finite_eventMass_mono (pilotLaw_isLaw hp).nonneg
    intro z hz
    change ¬(32*(n:ℝ)^2*t < rawScore q u z) at hz
    have h := le_of_not_gt hz
    have hneg : L ≤ -g z := by dsimp [g,L]; linarith
    exact hneg.trans (neg_le_abs _)
  have htail := finite_squared_deviation_bound (pilotLaw_isLaw hp).nonneg g hL
  refine hevent.trans (htail.trans ?_)
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  change E (pilotLaw p) (fun z : Fin (n+n) → A => (g z)^2) ≤ _
  have hZ := iid_head_quadratic_error hp q u n
  refine hZ.trans ?_
  have hB := square_budget_alternative p q u hu ((n:ℝ)^2*t) hcap
  have hB' : (∑ a, (u a)^2*(p a)^2) ≤ 2*((n:ℝ)*t)^2+2*(n:ℝ)^2*t*V := by linarith
  have hQ := linear_budget_alternative hu hnR ht hcap hnull hpower
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hB' (by positivity : 0 ≤ 3*(n:ℝ)^2))
    (mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 6*(n:ℝ)^3))
  refine hbound.trans ?_
  change 3*(n:ℝ)^2*(2*((n:ℝ)*t)^2+2*(n:ℝ)^2*t*V) +
    6*(n:ℝ)^3*(((n:ℝ)*t+(n:ℝ)*V/10000)*V) ≤ (1/100 : ℝ)*((n:ℝ)^2*V/2)^2
  have htv : t*V ≤ V^2/100000000 := by
    change 100000000*t ≤ V at hpower
    nlinarith only [mul_le_mul_of_nonneg_right hpower hV.le]
  have htt : t^2 ≤ t*V := by
    have h : t ≤ V := by change 100000000*t ≤ V at hpower; linarith
    nlinarith only [mul_le_mul_of_nonneg_left h ht.le]
  nlinarith only [mul_le_mul_of_nonneg_left htv (pow_nonneg hnR.le 4),
    mul_le_mul_of_nonneg_left htt (pow_nonneg hnR.le 4), sq_nonneg ((n:ℝ)^2*V)]

end
end CanonneIIDHead
