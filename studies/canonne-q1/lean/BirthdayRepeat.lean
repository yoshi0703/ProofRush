import PilotSupport
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FieldSimp

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

variable {X J : Type*} [Fintype X]

/-- Exact finite event probability, with no approximation to the product law. -/
def eventMass (p : X → ℝ) (event : X → Prop) : ℝ := by
  classical exact ∑ x, if event x then p x else 0

theorem eventMass_eq_sum (p : X → ℝ) (event : X → Prop) [DecidablePred event] :
    eventMass p event = ∑ x, if event x then p x else 0 := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x <;> simp [hx]

theorem eventMass_union_le (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (witnesses : Finset J) (event : J → X → Prop) :
    eventMass p (fun x => ∃ j ∈ witnesses, event j x) ≤ ∑ j ∈ witnesses, eventMass p (event j) := by
  classical
  unfold eventMass
  calc
    _ ≤ ∑ x : X, ∑ j ∈ witnesses, (if event j x then p x else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases h : ∃ j ∈ witnesses, event j x
      · obtain ⟨j, hj, he⟩ := h
        rw [ite_eq_left (show ∃ j ∈ witnesses, event j x from ⟨j, hj, he⟩)]
        calc
          p x = (if event j x then p x else 0) := (ite_eq_left he).symm
          _ ≤ ∑ k ∈ witnesses, (if event k x then p x else 0) :=
            Finset.single_le_sum (f := fun k => if event k x then p x else 0)
              (fun _ _ => by split <;> simp [hp x]) hj
      · rw [ite_eq_right h]
        exact Finset.sum_nonneg (fun _ _ => by split <;> simp [hp x])
    _ = _ := Finset.sum_comm

theorem eventMass_congr (p : X → ℝ) {E F : X → Prop}
    (agree : ∀ x, E x ↔ F x) : eventMass p E = eventMass p F := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x
  · simp [h, (agree x).mp h]
  · have hf : ¬ F x := fun h' => h ((agree x).mpr h')
    simp [h, hf]

section Products

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]

/-- A weighted product separates into independent single-coordinate expectations. -/
theorem pilot_weighted_product (p : A → ℝ) (f : I → A → ℝ) :
    (∑ x : I → A, pilotLaw p x * ∏ i, f i (x i)) =
      ∏ i, ∑ a, p a * f i a := by
  unfold pilotLaw
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => p a * f i a)).symm

theorem pilot_two_marginal {p : A → ℝ} (hp : IsLaw p) {i j : I} (hij : i ≠ j)
    (f g : A → ℝ) :
    (∑ x : I → A, pilotLaw p x * (f (x i) * g (x j))) =
      (∑ a, p a * f a) * (∑ a, p a * g a) := by
  classical
  let w (k : I) (a : A) : ℝ := (if k = i then f a else 1) * (if k = j then g a else 1)
  have input (x : I → A) : (∏ k, w k (x k)) = f (x i) * g (x j) := by
    unfold w
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  have output (k : I) :
      (∑ a, p a * w k a) =
        (if k = i then (∑ a, p a * f a) else 1) *
        (if k = j then (∑ a, p a * g a) else 1) := by
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all [w, hp.total]
  calc
    _ = ∑ x : I → A, pilotLaw p x * ∏ k, w k (x k) := by simp only [input]
    _ = ∏ k, ∑ a, p a * w k a := pilot_weighted_product p w
    _ = _ := by simp only [output, Finset.prod_mul_distrib, Fintype.prod_ite_eq']

theorem two_coordinate_event {p : A → ℝ} (hp : IsLaw p) {i j : I}
    (hij : i ≠ j) (a b : A) :
    eventMass (pilotLaw p) (fun x : I → A => x i = a ∧ x j = b) = p a * p b := by
  classical
  rw [eventMass_eq_sum]
  have hpoint (x : I → A) :
      (if x i = a ∧ x j = b then pilotLaw p x else 0) =
        pilotLaw p x * (((if x i = a then 1 else 0) : ℝ) * (if x j = b then 1 else 0)) := by
    by_cases hi : x i = a <;> by_cases hj : x j = b <;> simp [hi, hj]
  simp only [hpoint]
  rw [pilot_two_marginal hp hij (fun c => if c = a then 1 else 0) (fun c => if c = b then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Products

/-- One latent draw is a head observation or a uniformly chosen tail pilot index. -/
def latent (K : ℕ) (w : ℝ) : Option (Fin K) → ℝ
  | none => 1 - w
  | some _ => w / K

theorem latent_isLaw {K : ℕ} (hK : 0 < K) {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    IsLaw (latent K w) := by
  refine ⟨?_, ?_⟩
  · intro v
    cases v with
    | none => exact sub_nonneg.mpr hw₁
    | some i => exact div_nonneg hw₀ (by positivity)
  · simp only [Fintype.sum_option, latent, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    field_simp [hK']
    ring

def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  ((Finset.univ : Finset (Fin n)) ×ˢ Finset.univ).filter (fun a => a.1 < a.2)

theorem orderedPairs_card (n : ℕ) : (orderedPairs n).card = n.choose 2 := by
  simpa only [orderedPairs, Finset.card_univ, Fintype.card_fin]
    using Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n)))

def maskedRepeat {n K : ℕ} (x : Fin n → Option (Fin K)) : Prop :=
  ∃ a ∈ orderedPairs n, ∃ k : Fin K, x a.1 = some k ∧ x a.2 = some k

/-- The weighted birthday union bound for the actual ordered mask-and-index law.
Only pairs of tail observations sharing the same pilot index are counted. -/
theorem masked_repeat_bound {n K : ℕ} (hK : 0 < K) {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    eventMass (pilotLaw (latent K w)) (maskedRepeat (n := n) (K := K)) ≤
      (n.choose 2 : ℝ) * w^2 / K := by
  let p := pilotLaw (I := Fin n) (latent K w)
  have hLaw := latent_isLaw hK hw₀ hw₁
  have hp := (pilotLaw_isLaw (I := Fin n) hLaw).nonneg
  unfold maskedRepeat
  refine (eventMass_union_le p hp (orderedPairs n) ?_).trans ?_
  have pairbound (a : Fin n × Fin n) (ha : a ∈ orderedPairs n) :
      eventMass p (fun x => ∃ k : Fin K, x a.1 = some k ∧ x a.2 = some k) ≤ w^2 / K := by
    have halt : a.1 < a.2 := (Finset.mem_filter.mp ha).2
    have hunion := eventMass_union_le p hp (Finset.univ : Finset (Fin K))
      (fun k x => x a.1 = some k ∧ x a.2 = some k)
    have he :
        eventMass p (fun x => ∃ k : Fin K, x a.1 = some k ∧ x a.2 = some k) =
        eventMass p (fun x => ∃ k ∈ (Finset.univ : Finset (Fin K)), x a.1 = some k ∧ x a.2 = some k) := by
      apply eventMass_congr
      simp
    rw [he]
    refine hunion.trans ?_
    simp only [p, two_coordinate_event hLaw halt.ne, latent, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
    apply le_of_eq
    field_simp [hK']
  calc
    _ ≤ ∑ _a ∈ orderedPairs n, w^2 / (K : ℝ) := Finset.sum_le_sum pairbound
    _ = _ := by simp [orderedPairs_card, nsmul_eq_mul, mul_div_assoc]

end
end CanonneHeadTransfer
