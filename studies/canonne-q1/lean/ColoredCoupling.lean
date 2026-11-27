import ColoredPilot

namespace CanonneColoredPilot

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

section Products

variable {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]

/-- A product law whose marginal can depend on the coordinate. -/
def independentLaw (r : I → A → ℝ) (z : I → A) : ℝ := ∏ i, r i (z i)

variable [DecidableEq I]

theorem independentLaw_isLaw {r : I → A → ℝ} (hr : ∀ i, IsLaw (r i)) :
    IsLaw (independentLaw r) := by
  refine ⟨fun z => Finset.prod_nonneg fun i _ => (hr i).nonneg (z i), ?_⟩
  unfold independentLaw
  rw [← Fintype.prod_sum]
  simp only [(hr _).total, Finset.prod_const_one]

theorem independent_weighted_product (r f : I → A → ℝ) :
    (∑ z : I → A, independentLaw r z * ∏ i, f i (z i)) =
      ∏ i, ∑ a, r i a * f i a := by
  simp only [independentLaw, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => r i a * f i a)).symm

theorem independent_event_coordinates (r : I → A → ℝ) (P : I → A → Prop) :
    eventMass (independentLaw r) (fun z : I → A => ∀ i, P i (z i)) =
      ∏ i, eventMass (r i) (P i) := by
  classical
  let f (i : I) (a : A) : ℝ := if P i a then 1 else 0
  calc
    _ = ∑ z : I → A, independentLaw r z * ∏ i, f i (z i) := by
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro z _
      unfold f
      rw [product_zero_one]
      by_cases h : ∀ i, P i (z i) <;> simp [h]
    _ = ∏ i, ∑ a, r i a * f i a := independent_weighted_product r f
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : P i a <;> simp [h, f]

omit [DecidableEq I] in
theorem independent_draws_at_injective_keys [DecidableEq J] {r : J → A → ℝ} (hr : ∀ j, IsLaw (r j))
    (f : I → J) (inj : Function.Injective f) (y : I → A) :
    eventMass (independentLaw r) (fun z : J → A => ∀ i, z (f i) = y i) =
      independentLaw (fun i => r (f i)) y := by
  classical
  let weight (j : J) (a : A) : ℝ :=
    if h : ∃ i, f i = j then if a = y (Classical.choose h) then 1 else 0 else 1
  have hit (i : I) (a : A) : weight (f i) a = if a = y i then 1 else 0 := by
    let h : ∃ k, f k = f i := ⟨i, rfl⟩
    have hc : Classical.choose h = i := inj (Classical.choose_spec h)
    rw [show weight (f i) a = (if a = y (Classical.choose h) then 1 else 0) by
      unfold weight; rw [dite_eq_left h], hc]
  have miss (j : J) (hj : j ∉ Finset.univ.image f) (a : A) : weight j a = 1 := by
    unfold weight
    apply dite_eq_right
    rintro ⟨i, he⟩
    exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  have pointProduct (z : J → A) :
      (∏ j, weight j (z j)) = if ∀ i, z (f i) = y i then 1 else 0 := by
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f))
      (fun j _ hj => miss j hj (z j)), Finset.prod_image (g := f) (fun _ _ _ _ h => inj h)]
    simpa only [hit] using product_zero_one (fun i => z (f i) = y i)
  have productMass : (∏ j, ∑ a, r j a * weight j a) = independentLaw (fun i => r (f i)) y := by
    rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image f)) (fun j _ hj => by
      simp [miss j hj, (hr j).total]), Finset.prod_image (g := f) (fun _ _ _ _ h => inj h)]
    unfold independentLaw
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hit, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc
    _ = ∑ z : J → A, independentLaw r z * ∏ j, weight j (z j) := by
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [pointProduct]
      by_cases h : ∀ i, z (f i) = y i <;> simp [h]
    _ = _ := (independent_weighted_product r weight).trans productMass

end Products

section Coupling

variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A] {n : ℕ}

def selectKey (x : Fin n → Option J) (i : Fin n) : J ⊕ Fin n :=
  (x i).elim (Sum.inr i) Sum.inl

omit [Fintype J] in
theorem selectKey_injective {x : Fin n → Option J} (good : ¬ activeRepeat x) :
    Function.Injective (selectKey x) := by
  intro i j h
  by_cases heq : i = j
  · exact heq
  · cases hi : x i with
    | none =>
      cases hj : x j with
      | none => simp [selectKey, hi, hj, heq] at h
      | some b => simp [selectKey, hi, hj] at h
    | some a =>
      cases hj : x j with
      | none => simp [selectKey, hi, hj] at h
      | some b =>
        have hab : a = b := by simpa [selectKey, hi, hj] using h
        subst b
        exfalso
        apply good
        rcases lt_or_gt_of_ne heq with hlt | hgt
        · exact ⟨(i,j), by simp [orderedPairs, hlt], a, hi, hj⟩
        · exact ⟨(j,i), by simp [orderedPairs, hgt], a, hj, hi⟩

def byKey (fresh : A → ℝ) (r : J → A → ℝ) : J ⊕ Fin n → A → ℝ :=
  Sum.elim r fun _ => fresh

def givenKey (fresh : A → ℝ) (r : J → A → ℝ) (x : Option J) : A → ℝ :=
  x.elim fresh r

omit [Fintype J] [DecidableEq A] in
theorem givenKey_isLaw {fresh : A → ℝ} {r : J → A → ℝ}
    (hfresh : IsLaw fresh) (hr : ∀ j, IsLaw (r j)) (x : Option J) :
    IsLaw (givenKey fresh r x) := by
  cases x
  · exact hfresh
  · exact hr _

def sharedSample [DecidableEq J] (p : Option J → ℝ) (fresh : A → ℝ) (r : J → A → ℝ) :
    (Fin n → A) → ℝ :=
  mixLaw (pilotLaw p) (fun x =>
    coarsen (fun z i => z (selectKey x i)) (independentLaw (byKey (n := n) fresh r)))

def averagedLabel (p : Option J → ℝ) (fresh : A → ℝ) (r : J → A → ℝ) : A → ℝ :=
  fun a => ∑ j, p j * givenKey fresh r j a

omit [Fintype A] [DecidableEq A] in
theorem freshSamples_eq_product (p : Option J → ℝ) (fresh : A → ℝ) (r : J → A → ℝ) :
    mixLaw (pilotLaw p) (fun x : Fin n → Option J =>
      independentLaw (fun i => givenKey fresh r (x i))) =
      pilotLaw (averagedLabel p fresh r) := by
  classical
  funext y
  unfold mixLaw independentLaw
  exact pilot_weighted_product p (fun i j => givenKey fresh r j (y i))

/-- The entire ordered replacement law, with heterogeneous slot label laws
and an independent fresh law at each unmasked site. -/
theorem shared_iid_tv [DecidableEq J] {p : Option J → ℝ} (hp : IsLaw p) {fresh : A → ℝ} {r : J → A → ℝ}
    (hfresh : IsLaw fresh) (hr : ∀ j, IsLaw (r j)) :
    totalVariation (sharedSample (n := n) p fresh r) (pilotLaw (averagedLabel p fresh r)) ≤
      (n.choose 2 : ℝ) * ∑ j : J, p (some j)^2 := by
  have hkey (j : J ⊕ Fin n) : IsLaw (byKey fresh r j) := by
    cases j
    · exact hr _
    · exact hfresh
  rw [← freshSamples_eq_product (n := n) p fresh r]
  unfold sharedSample
  apply (totalVariation_mix_le_bad _ (pilotLaw_isLaw hp).nonneg _ _ ?_ ?_ (activeRepeat (n := n) (X := J)) ?_).trans
    (active_repeat_bound (n := n) hp)
  · intro x
    exact coarsen_isLaw (fun z i => z (selectKey x i)) (independentLaw_isLaw hkey)
  · intro x
    exact independentLaw_isLaw (fun i => givenKey_isLaw hfresh hr (x i))
  · intro x hgood
    funext y
    rw [coarsen_eventMass]
    rw [eventMass_congr _ (show ∀ z : J ⊕ Fin n → A,
        (fun i => z (selectKey x i)) = y ↔ ∀ i, z (selectKey x i) = y i by
          intro z
          constructor
          · intro h
            exact congrFun h
          · intro h
            exact funext h)]
    rw [independent_draws_at_injective_keys hkey _ (selectKey_injective hgood)]
    congr 1
    funext i
    cases hi : x i <;> simp [byKey, selectKey, givenKey, hi]

end Coupling

section Colors

variable {B A : Type*} [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A] {n : ℕ}

def bandedLabel (a : B → ℝ) (fresh : A → ℝ) (r : B → A → ℝ) : A → ℝ :=
  fun y => (1 - ∑ b, a b) * fresh y + ∑ b, a b * r b y

omit [DecidableEq B] [Fintype A] [DecidableEq A] in

theorem colored_fresh_label {K : B → ℕ} {a : B → ℝ}
    (hK : ∀ b, 0 < K b) (fresh : A → ℝ) (r : B → A → ℝ) :
    averagedLabel (coloredLatent K a) fresh (fun j => r j.1) = bandedLabel a fresh r := by
  funext y
  unfold averagedLabel bandedLabel
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [coloredLatent, givenKey, Option.elim_none, Option.elim_some]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : (K b : ℝ) ≠ 0 := by exact_mod_cast (hK b).ne'
  field_simp [hb]

/-- Joint TV comparison on the visible ordered samples for bins with distinct
pilot counts and conditional laws. The fresh component can include all
unchanged labels in addition to the actual head. -/
theorem colored_iid_tv {K : B → ℕ} {a : B → ℝ}
    (hK : ∀ b, 0 < K b) (ha : ∀ b, 0 ≤ a b) (hsum : ∑ b, a b ≤ 1)
    {fresh : A → ℝ} {r : B → A → ℝ}
    (hFresh : IsLaw fresh) (hr : ∀ b, IsLaw (r b)) :
    totalVariation (sharedSample (n := n) (coloredLatent K a) fresh (fun j => r j.1))
        (pilotLaw (bandedLabel a fresh r)) ≤
      (n.choose 2 : ℝ) * ∑ b, (a b)^2 / K b := by
  rw [← colored_fresh_label hK fresh r, ← colored_slot_square_sum hK]
  exact shared_iid_tv (coloredLatent_isLaw hK ha hsum) hFresh (fun j => hr j.1)

end Colors

end
end CanonneColoredPilot
