import RegularTailPullback

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Exact rejection probability of any real-valued test after an
injective projection from a longer ordered iid record. -/
theorem projection_rejection {m n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    (positions : Fin m → Fin n) (hinj : Function.Injective positions) (f : (Fin m → A) → ℝ) :
    tailRejection p (fun x : Fin n → A => f (fun i => x (positions i))) = tailRejection p f := by
  classical
  let project (x : Fin n → A) : Fin m → A := fun i => x (positions i)
  have marg : coarsen project (pilotLaw p) = pilotLaw p := by
    funext y
    rw [coarsen_eventMass]
    have same (x : Fin n → A) : project x = y ↔ ∀ i, x (positions i) = y i :=
      ⟨fun h => congrFun h, fun h => funext h⟩
    rw [eventMass_congr _ same, injective_pilot_draws hp positions hinj y]
  unfold tailRejection
  change (∑ x : Fin n → A, pilotLaw p x * f (project x)) = _
  rw [← marg]
  simp only [coarsen, Finset.sum_filter, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit [DecidableEq A] in
theorem test_rejection_mono {n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    {f g : (Fin n → A) → ℝ} (h : ∀ z, f z ≤ g z) :
    tailRejection p f ≤ tailRejection p g := by
  unfold tailRejection
  exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) ((pilotLaw_isLaw hp).nonneg z))

omit [DecidableEq A] in
theorem test_rejection_add {n : ℕ} (p : A → ℝ) (f g : (Fin n → A) → ℝ) :
    tailRejection p (fun z => f z+g z) = tailRejection p f + tailRejection p g := by
  simp only [tailRejection, mul_add, Finset.sum_add_distrib]

def batchOr {m n : ℕ} (f : (Fin m → A) → ℝ) (g : (Fin n → A) → ℝ)
    (z : Fin (m+n) → A) : ℝ :=
  let a := f (fun i => z (Fin.castAdd n i))
  let b := g (fun i => z (Fin.natAdd m i))
  a+b-a*b

private theorem scalar_or_bounds {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    (0 ≤ a+b-a*b ∧ a+b-a*b ≤ 1) ∧
      a ≤ a+b-a*b ∧ b ≤ a+b-a*b ∧ a+b-a*b ≤ a+b := by
  have up := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  have left := mul_nonneg hb.1 (sub_nonneg.mpr ha.2)
  have right := mul_nonneg ha.1 (sub_nonneg.mpr hb.2)
  have both := mul_nonneg ha.1 hb.1
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩ <;> nlinarith

omit [Fintype A] [DecidableEq A] in
theorem batchOr_unit {m n : ℕ} {f : (Fin m → A) → ℝ} {g : (Fin n → A) → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (z : Fin (m+n) → A) : 0 ≤ batchOr f g z ∧ batchOr f g z ≤ 1 :=
  (scalar_or_bounds (hf _) (hg _)).1

private theorem left_indices_injective (m n : ℕ) :
    Function.Injective (Fin.castAdd n : Fin m → Fin (m+n)) := by
  intro i j h
  have hval := congrArg (fun i : Fin (m+n) => i.val) h
  exact Fin.ext hval

/-- Rejection of the composed randomized test dominates both components
and is at most their sum, on every normalized input law. -/
theorem batchOr_bounds {m n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    {f : (Fin m → A) → ℝ} {g : (Fin n → A) → ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    tailRejection p f ≤ tailRejection p (batchOr f g) ∧
    tailRejection p g ≤ tailRejection p (batchOr f g) ∧
    tailRejection p (batchOr f g) ≤ tailRejection p f + tailRejection p g := by
  let fl (z : Fin (m+n) → A) := f (fun i => z (Fin.castAdd n i))
  let gr (z : Fin (m+n) → A) := g (fun i => z (Fin.natAdd m i))
  have leL : tailRejection p fl = tailRejection p f :=
    projection_rejection hp _ (left_indices_injective m n) f
  have leR : tailRejection p gr = tailRejection p g :=
    projection_rejection hp _ (Fin.natAdd_injective n m) g
  rw [← leL, ← leR, ← test_rejection_add]
  exact ⟨test_rejection_mono hp (fun z => (scalar_or_bounds (hf _) (hg _)).2.1),
    test_rejection_mono hp (fun z => (scalar_or_bounds (hf _) (hg _)).2.2.1),
    test_rejection_mono hp (fun z => (scalar_or_bounds (hf _) (hg _)).2.2.2)⟩

omit [DecidableEq A] in
theorem rejection_indicator {n : ℕ} (p : A → ℝ) (E : (Fin n → A) → Prop)
    [DecidablePred E] :
    tailRejection p (fun z => if E z then 1 else 0) = eventMass (pilotLaw p) E := by
  rw [tailRejection, eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : E z <;> simp [h]

omit [DecidableEq A] in
theorem eventMass_complement {X : Type*} [Fintype X] {p : X → ℝ} (hp : IsLaw p)
    (E : X → Prop) : eventMass p E + eventMass p (fun z => ¬E z) = 1 := by
  classical
  rw [eventMass_eq_sum, eventMass_eq_sum, ← Finset.sum_add_distrib, ← hp.total]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : E z <;> simp [h]

end
end CanonneQuantile
