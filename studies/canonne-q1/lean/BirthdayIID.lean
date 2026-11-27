import BirthdayRepeat

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

section Injective

variable {I J A : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]

theorem product_zero_one {Z : Type*} [Fintype Z] (P : Z → Prop) [DecidablePred P] :
    (∏ z, (if P z then 1 else 0 : ℝ)) = if ∀ z, P z then 1 else 0 := by
  classical
  by_cases hall : ∀ z, P z
  · simp [hall]
  · obtain ⟨z, hz⟩ := not_forall.mp hall
    rw [ite_eq_right hall]
    exact Finset.prod_eq_zero (Finset.mem_univ z) (ite_eq_right hz)

omit [DecidableEq I] in
/-- Distinct selected indices in an ordered iid pilot tuple give exactly
the iid law on the corresponding ordered selected labels. -/
theorem injective_pilot_draws {r : A → ℝ} (hr : IsLaw r)
    (f : I → J) (hinj : Function.Injective f) (y : I → A) :
    eventMass (pilotLaw r) (fun z : J → A => ∀ i, z (f i) = y i) = pilotLaw r y := by
  classical
  let weight (j : J) (a : A) : ℝ :=
    if h : ∃ i, f i = j then if a = y (Classical.choose h) then 1 else 0 else 1
  have w_hit (i : I) (a : A) : weight (f i) a = if a = y i then 1 else 0 := by
    let h : ∃ k, f k = f i := ⟨i, rfl⟩
    have hchoose : Classical.choose h = i := hinj (Classical.choose_spec h)
    rw [show weight (f i) a = (if a = y (Classical.choose h) then 1 else 0) by
      unfold weight; rw [dite_eq_left h], hchoose]
  have w_miss (j : J) (hj : j ∉ Finset.univ.image f) (a : A) : weight j a = 1 := by
    unfold weight
    apply dite_eq_right
    rintro ⟨i, he⟩
    exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  have pointProduct (z : J → A) :
      (∏ j, weight j (z j)) = if ∀ i, z (f i) = y i then 1 else 0 := by
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f))
      (fun j _ hj => w_miss j hj (z j)), Finset.prod_image (g := f) (fun _ _ _ _ h => hinj h)]
    simpa only [w_hit] using product_zero_one (fun i => z (f i) = y i)
  have productMass :
      (∏ j, ∑ a, r a * weight j a) = pilotLaw r y := by
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f)) (fun j _ hj => by
      simp [w_miss j hj, hr.total]), Finset.prod_image (g := f) (fun _ _ _ _ h => hinj h)]
    unfold pilotLaw
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [w_hit, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc
    _ = ∑ z : J → A, pilotLaw r z * ∏ j, weight j (z j) := by
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [pointProduct]
      by_cases h : ∀ i, z (f i) = y i <;> simp [h]
    _ = _ := (pilot_weighted_product r weight).trans productMass

end Injective

section Masks

variable {n K : ℕ} {A : Type*} [Fintype A]

def active (x : Fin n → Option (Fin K)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (x i).isSome)

def activeIndex (x : Fin n → Option (Fin K)) (i : active x) : Fin K :=
  (x i.1).get (Finset.mem_filter.mp i.2).2

theorem activeIndex_eq (x : Fin n → Option (Fin K)) (i : active x) :
    x i.1 = some (activeIndex x i) :=
  (Option.some_get (Finset.mem_filter.mp i.2).2).symm

theorem activeIndex_injective {x : Fin n → Option (Fin K)} (good : ¬maskedRepeat x) :
    Function.Injective (activeIndex x) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have ha := activeIndex_eq x a
  have hb := activeIndex_eq x b
  rw [← hab] at hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply good
    exact ⟨(a.1, b.1), by simp [orderedPairs, hlt], activeIndex x a, ha, hb⟩
  · apply good
    exact ⟨(b.1, a.1), by simp [orderedPairs, hgt], activeIndex x a, hb, ha⟩

def maskedEmit (x : Fin n → Option (Fin K)) (pilots : Fin K → A) : Fin n → Option A :=
  fun i => (x i).map pilots

def independentEmit (x : Fin n → Option (Fin K)) (fresh : Fin n → A) : Fin n → Option A :=
  fun i => if (x i).isSome then some (fresh i) else none

/-- At every fixed clean latent tuple, the ordered observations match the
conditional iid-label mask experiment, even for nonuniform reference labels. -/
theorem clean_masked_law {r : A → ℝ} (hr : IsLaw r)
    {x : Fin n → Option (Fin K)} (good : ¬ maskedRepeat x) (out : Fin n → Option A) :
    eventMass (pilotLaw r) (fun z : Fin K → A => maskedEmit x z = out) =
      eventMass (pilotLaw r) (fun z : Fin n → A => independentEmit x z = out) := by
  classical
  by_cases shaped : ∀ i : Fin n, (out i).isSome = (x i).isSome
  · let observed (i : active x) : A :=
      (out i.1).get ((shaped i.1).trans (Finset.mem_filter.mp i.2).2)
    have observed_eq (i : active x) : out i.1 = some (observed i) :=
      (Option.some_get ((shaped i.1).trans (Finset.mem_filter.mp i.2).2)).symm
    have condition (dec : Fin n → A) :
        (fun i => if (x i).isSome then some (dec i) else none) = out ↔
        ∀ i : active x, dec i.1 = observed i := by
      constructor
      · intro he i
        have point := congrFun he i.1
        rw [ite_eq_left (Finset.mem_filter.mp i.2).2, observed_eq i] at point
        exact Option.some.inj point
      · intro hf
        funext i
        by_cases hi : (x i).isSome
        · let j : active x := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          rw [ite_eq_left hi, observed_eq j, hf j]
        · rw [ite_eq_right hi]
          have hnone : out i = none := by
            cases h : out i with
            | none => rfl
            | some a => exact (hi ((shaped i).symm.trans (by rw [h]; rfl))).elim
          exact hnone.symm
    have restrict_left (z : Fin K → A) : maskedEmit x z = out ↔
        ∀ i : active x, z (activeIndex x i) = observed i := by
      constructor
      · intro he i
        have point := congrFun he i.1
        change (x i.1).map z = out i.1 at point
        rw [activeIndex_eq x i, observed_eq i] at point
        exact Option.some.inj point
      · intro hf
        funext i
        change (x i).map z = out i
        by_cases hi : (x i).isSome
        · let j : active x := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
          change (x j.1).map z = out j.1
          rw [activeIndex_eq x j, observed_eq j]
          exact congrArg some (hf j)
        · have hx : x i = none := by
            cases h : x i with
            | none => rfl
            | some k => exact (hi (by rw [h]; rfl)).elim
          have hnone : out i = none := by
            cases h : out i with
            | none => rfl
            | some a => exact (hi ((shaped i).symm.trans (by rw [h]; rfl))).elim
          simp [hx, hnone]
    unfold independentEmit
    rw [eventMass_congr _ restrict_left, eventMass_congr _ condition,
      injective_pilot_draws hr (activeIndex x) (activeIndex_injective good),
      injective_pilot_draws hr Subtype.val Subtype.val_injective]
  · have noLeft (z : Fin K → A) : ¬ maskedEmit x z = out := by
      intro he
      apply shaped
      intro i
      rw [← he]
      cases h : x i <;> simp [maskedEmit, h]
    have noRight (z : Fin n → A) : ¬ independentEmit x z = out := by
      intro he
      apply shaped
      intro i
      rw [← he]
      cases h : x i <;> simp [independentEmit, h]
    simp [eventMass, noLeft, noRight]

end Masks
end
end CanonneHeadTransfer
