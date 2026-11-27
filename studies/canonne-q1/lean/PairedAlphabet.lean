import AmbientTransfers
import Mathlib.Logic.Equiv.Set

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {ι α : Type*}

noncomputable def pairedAlphabetEquiv (e : (ι × Bool) ↪ α) :
    ((ι × Bool) ⊕ {a : α // a ∉ Set.range e}) ≃ α := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem pairedAlphabetEquiv_inl (e : (ι × Bool) ↪ α) (a : ι × Bool) :
    pairedAlphabetEquiv e (Sum.inl a) = e a := rfl

@[simp] theorem pairedAlphabetEquiv_inr (e : (ι × Bool) ↪ α)
    (a : {a : α // a ∉ Set.range e}) :
    pairedAlphabetEquiv e (Sum.inr a) = a := rfl

noncomputable def embeddedLaw (e : (ι × Bool) ↪ α) (h : α → ℝ) (z : ι → ℝ)
    (s : ι → Bool) (a : α) : ℝ :=
  ambientLaw (h ∘ pairedAlphabetEquiv e) z s ((pairedAlphabetEquiv e).symm a)

theorem embeddedLaw_unchanged (e : (ι × Bool) ↪ α) (h : α → ℝ) (z : ι → ℝ)
    (s : ι → Bool) {a : α} (ha : a ∉ Set.range e) :
    embeddedLaw e h z s a = h a := by
  have he : a = pairedAlphabetEquiv e (Sum.inr ⟨a,ha⟩) := rfl
  have hs : (pairedAlphabetEquiv e).symm a = Sum.inr ⟨a,ha⟩ :=
    (pairedAlphabetEquiv e).injective (by rw [(pairedAlphabetEquiv e).apply_symm_apply]; exact he)
  simp [embeddedLaw, hs, ambientLaw]

variable [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Disjoint paired modifications of an arbitrary finite law, including untouched zero-mass labels. -/
theorem embedded_iid_mixture_bound (n : ℕ) (e : (ι × Bool) ↪ α) (h : α → ℝ) (z : ι → ℝ)
    (hp : ∀ a : ι × Bool, 0 < h (e a)) (hn : ∑ a, h a = 1)
    (hw : ∀ a, 0 ≤ h a) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ a : ι × Bool, z a.1 ≤ h (e a)) :
    (∀ s : ι → Bool, (∀ a, 0 ≤ embeddedLaw e h z s a) ∧
      (∑ a, embeddedLaw e h z s a) = 1 ∧
      (∑ a, |embeddedLaw e h z s a - h a|) / 2 = ∑ i, z i) ∧
    let M := mixture (fun s : ι → Bool ↦ iidMass n (embeddedLaw e h z s))
    overlapKernel (iidMass n h) M M ≤
      Real.exp (∑ i, ((n : ℝ) * pairCoefficient (h ∘ e) z i)^2 / 2) := by
  let _ : Fintype {a : α // a ∉ Set.range e} := Fintype.ofFinite _
  let E := pairedAlphabetEquiv e
  let h' := h ∘ E
  have h'p : ∀ a : ι × Bool, 0 < h' (Sum.inl a) := hp
  have h'n : ∑ a, h' a = 1 := (E.sum_comp h).trans hn
  have h'u : ∀ a, 0 ≤ h' (Sum.inr a) := fun a ↦ hw a
  have h'b : ∀ a : ι × Bool, z a.1 ≤ h' (Sum.inl a) := hb
  have he (s : ι → Bool) (a : (ι × Bool) ⊕ {a : α // a ∉ Set.range e}) :
      embeddedLaw e h z s (E a) = ambientLaw h' z s a := by
    change ambientLaw h' z s (E.symm (E a)) = _
    rw [E.symm_apply_apply]
  constructor
  · intro s
    refine ⟨?_, ?_, ?_⟩
    · intro a
      obtain ⟨a, rfl⟩ := E.surjective a
      rw [he]
      exact ambientLaw_nonnegative h' z s h'u hz h'b a
    · rw [← E.sum_comp (embeddedLaw e h z s)]
      simp_rw [he]
      exact ambientLaw_normalized h' z s h'n
    · rw [← E.sum_comp (fun a ↦ |embeddedLaw e h z s a - h a|)]
      simp_rw [he]
      exact ambientLaw_tv h' z s hz
  · dsimp only
    unfold overlapKernel
    rw [← (Equiv.piCongrRight (fun _ : Fin n ↦ E)).sum_comp]
    have hiids (s : ι → Bool) (x : Fin n → (ι × Bool) ⊕ {a : α // a ∉ Set.range e}) :
        iidMass n (embeddedLaw e h z s) ((Equiv.piCongrRight (fun _ : Fin n ↦ E)) x) =
          iidMass n (ambientLaw h' z s) x := by
      change (∏ j, embeddedLaw e h z s (E (x j))) = _
      simp_rw [he]
      rfl
    have hiid (x : Fin n → (ι × Bool) ⊕ {a : α // a ∉ Set.range e}) :
        iidMass n h ((Equiv.piCongrRight (fun _ : Fin n ↦ E)) x) = iidMass n h' x := rfl
    simp_rw [mixture, hiids, hiid]
    exact ambient_iid_mixture_second_moment_le n h' z h'p h'n h'u hz h'b

end CanonneHeadEnvelope
