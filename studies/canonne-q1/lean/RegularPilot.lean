import RegularTransfer
import Mathlib.Logic.Equiv.Prod

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot CanonneNearOneTesting
open scoped BigOperators
noncomputable section

section FreshSlots

variable {A J : Type*} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J] {n : ℕ}

/-- The point mass at a given realized pilot label. -/
def pointLaw (a : A) (b : A) : ℝ := if a = b then 1 else 0

omit [Fintype J] [DecidableEq J] in
theorem pointLaw_isLaw (a : A) : IsLaw (pointLaw a) := by
  refine ⟨fun b => by unfold pointLaw; split <;> norm_num, ?_⟩
  simp [pointLaw]

/-- A selected slot is deterministic given the list. Unmasked draws are
fresh each time and are not part of the list. -/
def givenFreshSlot (fresh : A → ℝ) (z : J → A) (key : Option J) : A → ℝ :=
  key.elim fresh (fun j => pointLaw (z j))

def freshSlotLabel (key : Option J → ℝ) (fresh : A → ℝ) (z : J → A) : A → ℝ :=
  mixLaw key (givenFreshSlot fresh z)

omit [Fintype A] [DecidableEq J] in
theorem freshSlotLabel_apply (key : Option J → ℝ) (fresh : A → ℝ) (z : J → A) (a : A) :
    freshSlotLabel key fresh z a = key none * fresh a + ∑ j, key (some j) * pointLaw (z j) a := by
  unfold freshSlotLabel mixLaw
  rw [Fintype.sum_option]
  rfl

/-- The coupling's head/frozen draws remain fresh, even after conditioning
on all pilot slots. -/
theorem coarsened_keys_eq_fresh_mixture {fresh : A → ℝ} (hfresh : IsLaw fresh)
    (r : J → A → ℝ) (keys : Fin n → Option J) (out : Fin n → A) :
    coarsen (fun z i => z (selectKey keys i))
      (independentLaw (byKey (n := n) fresh r)) out =
      ∑ z : J → A, independentLaw r z *
        independentLaw (fun i => givenFreshSlot fresh z (keys i)) out := by
  classical
  let e := Equiv.sumArrowEquivProdArrow J (Fin n) A
  let E := fun (z : J → A) (s : Fin n → A) (i : Fin n) =>
    (keys i).elim (s i) z = out i
  rw [coarsen_eventMass, eventMass_eq_sum]
  calc
    _ = ∑ pair : (J → A) × (Fin n → A),
        if ∀ i, E pair.1 pair.2 i then independentLaw r pair.1 * pilotLaw fresh pair.2 else 0 := by
      apply Fintype.sum_equiv e
      intro lists
      have hcond : ((fun i => lists (selectKey keys i)) = out) ↔
          ∀ i, E (e lists).1 (e lists).2 i := by
        constructor <;> intro h
        · intro i
          have hi := congrFun h i
          cases hk : keys i <;> simpa [E, e, selectKey, hk] using hi
        · funext i
          have hi := h i
          cases hk : keys i <;> simpa [E, e, selectKey, hk] using hi
      have hprod : independentLaw (byKey (n := n) fresh r) lists =
          independentLaw r (e lists).1 * pilotLaw fresh (e lists).2 := by
        unfold independentLaw pilotLaw
        rw [Fintype.prod_sum_type]
        rfl
      by_cases he : (fun i => lists (selectKey keys i)) = out
      · rw [ite_eq_left he, ite_eq_left (hcond.mp he), hprod]
      · rw [ite_eq_right he, ite_eq_right (fun h => he (hcond.mpr h))]
    _ = ∑ z : J → A, independentLaw r z *
        eventMass (pilotLaw fresh) (fun s : Fin n → A => ∀ i, E z s i) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _
      rw [eventMass_eq_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : ∀ i, E z s i
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      apply congrArg (fun v => independentLaw r z * v)
      change eventMass (pilotLaw fresh) (fun s : Fin n → A =>
        ∀ i, (keys i).elim (s i) z = out i) = _
      rw [product_event_coordinates fresh (fun i a => (keys i).elim a z = out i)]
      unfold independentLaw
      apply Finset.prod_congr rfl
      intro i _
      rw [eventMass_eq_sum]
      cases hk : keys i with
      | none =>
        simp only [givenFreshSlot, hk, Option.elim_none]
        rw [Finset.sum_eq_single (out i)]
        · simp
        · intro a _ ha
          simp [ha]
        · simp
      | some j =>
        by_cases he : z j = out i
        · simpa [givenFreshSlot, pointLaw, hk, he] using hfresh.total
        · simp [givenFreshSlot, pointLaw, hk, he]

theorem sharedSample_eq_mixture_with_fresh (key : Option J → ℝ)
    {fresh : A → ℝ} (hfresh : IsLaw fresh) (r : J → A → ℝ) :
    sharedSample (n := n) key fresh r =
      mixLaw (independentLaw r) (fun z => pilotLaw (freshSlotLabel key fresh z)) := by
  unfold sharedSample
  have hco (keys : Fin n → Option J) :
      coarsen (fun z i => z (selectKey keys i))
        (independentLaw (byKey (n := n) fresh r)) =
        mixLaw (independentLaw r) (fun z => orderedChannel (givenFreshSlot fresh z) keys) := by
    funext out
    exact coarsened_keys_eq_fresh_mixture hfresh r keys out
  simp only [hco]
  rw [mix_commutes]
  simp only [iid_through_ordered_channel, freshSlotLabel]

end FreshSlots

end
end CanonneRegularTransfer
