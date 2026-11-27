import BirthdayIID
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Marginal law when the first draw selects a finite conditional law. -/
def mixLaw (p : X → ℝ) (f : X → Y → ℝ) (y : Y) : ℝ :=
  ∑ x, p x * f x y

omit [Fintype Y] in
theorem coarsen_eventMass [DecidableEq Y] (f : X → Y) (p : X → ℝ) (y : Y) :
    coarsen f p y = eventMass p (fun x => f x = y) := by
  classical
  unfold coarsen
  rw [Finset.sum_filter, eventMass_eq_sum]

/-- Mixing with a common mixing law contracts the average conditional TV. -/
theorem totalVariation_mix_le (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (f g : X → Y → ℝ) :
    totalVariation (mixLaw p f) (mixLaw p g) ≤ ∑ x, p x * totalVariation (f x) (g x) := by
  have aux (y : Y) : |mixLaw p f y - mixLaw p g y| ≤ ∑ x, p x * |f x y - g x y| := by
    unfold mixLaw
    rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    calc
      _ ≤ ∑ x, |p x * (f x y - g x y)| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_of_nonneg (hp _)]
  unfold totalVariation
  calc
    _ ≤ (∑ y : Y, ∑ x : X, p x * |f x y - g x y|) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun y _ => aux y) (by norm_num)
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]
      simp only [← Finset.mul_sum, mul_div_assoc]

theorem totalVariation_le_one {p q : X → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    totalVariation p q ≤ 1 := by
  rw [totalVariation_eq_deficit hp hq, ← hq.total]
  exact Finset.sum_le_sum fun x _ => max_le (sub_le_self _ (hp.nonneg x)) (hq.nonneg x)

/-- On a finite set of latent values where both conditional laws agree,
their contribution to the TV distance vanishes. -/
theorem totalVariation_mix_le_bad (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f g : X → Y → ℝ) (hf : ∀ x, IsLaw (f x)) (hg : ∀ x, IsLaw (g x))
    (bad : X → Prop) (hgood : ∀ x, ¬ bad x → f x = g x) :
    totalVariation (mixLaw p f) (mixLaw p g) ≤ eventMass p bad := by
  classical
  refine (totalVariation_mix_le p hp f g).trans ?_
  rw [eventMass_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : bad x
  · rw [ite_eq_left h]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (totalVariation_le_one (hf x) (hg x)) (hp x)
  · rw [ite_eq_right h, hgood x h]
    simp [totalVariation]

section Products

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]

theorem product_event_coordinates (r : A → ℝ) (P : I → A → Prop) :
    eventMass (pilotLaw r) (fun x : I → A => ∀ i, P i (x i)) =
      ∏ i, eventMass r (P i) := by
  classical
  let f (i : I) (a : A) : ℝ := if P i a then 1 else 0
  calc
    _ = ∑ x : I → A, pilotLaw r x * ∏ i, f i (x i) := by
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro x _
      unfold f
      rw [product_zero_one]
      by_cases h : ∀ i, P i (x i) <;> simp [h]
    _ = ∏ i : I, ∑ a : A, r a * f i a := pilot_weighted_product r f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : P i a <;> simp [h, f]

end Products

section Emission

variable {n K : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

def replacementMasked (K : ℕ) (w : ℝ) (r : A → ℝ) : (Fin n → Option A) → ℝ :=
  mixLaw (pilotLaw (latent K w)) (fun x => coarsen (maskedEmit x) (pilotLaw r))

def freshMasked (K : ℕ) (w : ℝ) (r : A → ℝ) : (Fin n → Option A) → ℝ :=
  mixLaw (pilotLaw (latent K w)) (fun x => coarsen (independentEmit x) (pilotLaw r))

def visibleTail (w : ℝ) (r : A → ℝ) : Option A → ℝ
  | none => 1 - w
  | some a => w * r a

theorem fresh_one_site {r : A → ℝ} (hr : IsLaw r) (hK : 0 < K) (w : ℝ) (y : Option A) :
    (∑ x : Option (Fin K), latent K w x *
      eventMass r (fun a => (if x.isSome then some a else none) = y)) =
      visibleTail w r y := by
  classical
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  cases y with
  | none =>
    simp [latent, visibleTail, eventMass, hr.total]
  | some b =>
    simp only [Fintype.sum_option, latent, visibleTail, eventMass, Option.isSome_none, Option.isSome_some,
      ite_false, ite_true, reduceCtorEq, Finset.sum_const_zero, mul_zero, zero_add,
      Option.some.injEq, Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const,
      Fintype.card_fin, Finset.card_univ, nsmul_eq_mul]
    field_simp [hK']

/-- After mixing over all masks and latent indices, the fresh experiment is
literally the iid law that records each head label only as `none`. -/
theorem freshMasked_eq_iid (K : ℕ) (w : ℝ) (hK : 0 < K) {r : A → ℝ} (hr : IsLaw r) :
    freshMasked (n := n) K w r = pilotLaw (visibleTail w r) := by
  classical
  funext out
  let f (i : Fin n) (x : Option (Fin K)) : ℝ :=
    eventMass r (fun a => (if x.isSome then some a else none) = out i)
  have conditional (x : Fin n → Option (Fin K)) :
      coarsen (independentEmit x) (pilotLaw r) out = ∏ i, f i (x i) := by
    rw [coarsen_eventMass]
    have hc (z : Fin n → A) : independentEmit x z = out ↔
        ∀ i, (if (x i).isSome then some (z i) else none) = out i := by
      exact ⟨fun h => congrFun h, fun h => funext h⟩
    rw [eventMass_congr _ hc]
    exact product_event_coordinates r (fun i a => (if (x i).isSome then some a else none) = out i)
  rw [freshMasked, mixLaw]
  simp only [conditional]
  rw [pilot_weighted_product]
  unfold pilotLaw
  apply Finset.prod_congr rfl
  intro i _
  exact fresh_one_site hr hK w (out i)

/-- The actual replacement-pilot sample law differs from the iid tail-and-mask
experiment by at most `choose(n,2) * w^2 / K`. -/
theorem masked_pilot_tv {r : A → ℝ} (hr : IsLaw r)
    (hK : 0 < K) {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    totalVariation (replacementMasked (n := n) K w r) (pilotLaw (visibleTail w r)) ≤
      (n.choose 2 : ℝ) * w^2 / K := by
  rw [← freshMasked_eq_iid (n := n) K w hK hr]
  apply le_trans (totalVariation_mix_le_bad (pilotLaw (latent K w))
    (pilotLaw_isLaw (latent_isLaw hK hw₀ hw₁)).nonneg
    (fun x => coarsen (maskedEmit x) (pilotLaw r))
    (fun x => coarsen (independentEmit x) (pilotLaw r))
    (fun x => coarsen_isLaw _ (pilotLaw_isLaw hr))
    (fun x => coarsen_isLaw _ (pilotLaw_isLaw hr))
    maskedRepeat ?_)
  · exact masked_repeat_bound hK hw₀ hw₁
  · intro x good
    funext out
    simp only [coarsen_eventMass]
    exact clean_masked_law hr good out

end Emission
end
end CanonneHeadTransfer
