import HeadProfile
import SortedAlphabet

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {A B : Type*} [Fintype A] [Fintype B]

theorem goodIdentityTest_pullback (e : A ≃ B) {n : ℕ} {q : B → ℝ} {ε : ℝ}
    (ht : GoodIdentityTest n q ε) : GoodIdentityTest n (q ∘ e) ε := by
  obtain ⟨f,hf₀,hf₁,hnull,halt⟩ := ht
  let E := Equiv.piCongrRight (fun _ : Fin n ↦ e)
  have hs (p : B → ℝ) :
      (∑ x : Fin n → A, iidMass n (p ∘ e) x * f (E x)) =
        ∑ x : Fin n → B, iidMass n p x * f x := by
    exact E.sum_comp (fun x ↦ iidMass n p x * f x)
  refine ⟨fun x ↦ f (E x), fun x ↦ hf₀ _, fun x ↦ hf₁ _, ?_, ?_⟩
  · rw [hs]
    exact hnull
  · intro p hp hp1 hfar
    let p' := p ∘ e.symm
    have hp' : ∀ b, 0 ≤ p' b := fun b ↦ hp _
    have hp'1 : ∑ b, p' b = 1 := (e.symm.sum_comp p).trans hp1
    have heq : p' ∘ e = p := by ext x; simp [p']
    have hfar' : ε < (∑ b, |p' b - q b|) / 2 := by
      rw [← e.sum_comp (fun b ↦ |p' b - q b|)]
      simpa [p'] using hfar
    rw [← heq, hs]
    exact halt p' hp' hp'1 hfar'

theorem goodIdentityTest_equiv (e : A ≃ B) {n : ℕ} {q : B → ℝ} {ε : ℝ} :
    GoodIdentityTest n (q ∘ e) ε ↔ GoodIdentityTest n q ε := by
  constructor
  · intro h
    have h' := goodIdentityTest_pullback e.symm h
    simpa [Function.comp_def] using h'
  · exact goodIdentityTest_pullback e

/-- The source-profile bound applies to an arbitrary finite alphabet after sorting its labels.
The equivalence is retained so that subsequent constructions can refer to the original labels. -/
theorem exists_sorted_profile_bound {n : ℕ} [Nonempty A] {q : A → ℝ}
    (hn : 0 < n) (hq : ∀ a, 0 < q a) (hm : ∑ a, q a = 1) :
    ∃ d : ℕ, ∃ e : Fin (d+1) ≃ A,
      Antitone (q ∘ e) ∧ ∀ ε : ℝ, 32*ε < headProfile n (q ∘ e) → ¬ GoodIdentityTest n q ε := by
  obtain ⟨d,e,he⟩ := exists_sorted_succ_equiv q
  refine ⟨d,e,he,fun ε hfar ht ↦ ?_⟩
  exact head_profile_no_test hn (fun i ↦ hq _) he ((e.sum_comp q).trans hm)
    hfar (goodIdentityTest_pullback e ht)

end CanonneHeadEnvelope
