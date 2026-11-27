import PairedTesting

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {α S : Type*} [Fintype α] [Fintype S]

private theorem rejection_mixture (p : S → α → ℝ) (f : α → ℝ) :
    (∑ a, mixture p a * f a) = (∑ s, ∑ a, p s a * f a) / (Fintype.card S : ℝ) := by
  unfold mixture
  simp_rw [div_eq_mul_inv]
  conv_rhs =>
    rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_mul]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contradiction for a test of strict-radius alternatives when the paired witness is far and
the sum of its error budgets and the mixture TV bound is less than one. -/
theorem embedded_iid_no_test (n : ℕ) (e : (ι × Bool) ↪ α) (h : α → ℝ) (z : ι → ℝ)
    (hp : ∀ a : ι × Bool, 0 < h (e a)) (hn : ∑ a, h a = 1)
    (hw : ∀ a, 0 ≤ h a) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ a : ι × Bool, z a.1 ≤ h (e a))
    {ε aErr bErr : ℝ} (hfar : ε < ∑ i, z i)
    (hgap : aErr + bErr +
      Real.sqrt (Real.exp (∑ i, ((n : ℝ) * pairCoefficient (h ∘ e) z i)^2 / 2) - 1) / 2 < 1) :
    ¬ ∃ f : (Fin n → α) → ℝ,
      (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∑ x, iidMass n h x * f x) ≤ aErr ∧
      ∀ p : α → ℝ, (∀ a, 0 ≤ p a) → (∑ a, p a) = 1 →
        ε < (∑ a, |p a - h a|) / 2 →
        1 - bErr ≤ ∑ x, iidMass n p x * f x := by
  rintro ⟨f,hf₀,hf₁,hnull,halt⟩
  let c := (Fintype.card (ι → Bool) : ℝ)
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  let P := fun s : ι → Bool ↦ iidMass n (embeddedLaw e h z s)
  obtain ⟨hM, _⟩ := embedded_iid_mixture_bound n e h z hp hn hw hz hb
  have hpower (s : ι → Bool) : 1 - bErr ≤ ∑ x, P s x * f x :=
    halt _ (hM s).1 (hM s).2.1 (by rw [(hM s).2.2]; exact hfar)
  have hfull := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ι → Bool))) ↦ hpower s
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfull
  have havg : 1 - bErr ≤ ∑ x, mixture P x * f x := by
    rw [rejection_mixture, le_div_iff₀ hc, mul_comm]
    exact hfull
  have h1 : ∑ x, mixture P x = ∑ x, iidMass n h x :=
    (mixture_normalized fun s ↦ iidMass_normalized n (hM s).2.1).trans
      (iidMass_normalized n hn).symm
  have hTV := embedded_iid_mixture_tv_bound n e h z hp hn hw hz hb
  dsimp only at hTV
  have htest := (rejection_gap_le_tv hf₀ hf₁ h1).trans hTV
  linarith

end CanonneHeadEnvelope
