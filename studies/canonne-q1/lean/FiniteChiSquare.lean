import SignedTransfers
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {α S : Type*} [Fintype α] [Fintype S]

theorem iidMass_normalized (n : ℕ) {p : α → ℝ} (hn : ∑ a, p a = 1) :
    ∑ x, iidMass n p x = 1 := by
  have ht := Finset.sum_pow' (Finset.univ : Finset α) p n
  rw [show (Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset α))) = Finset.univ by
    ext x
    simp, hn, one_pow] at ht
  exact ht.symm

omit [Fintype α] in
theorem iidMass_supported (n : ℕ) {p q : α → ℝ} (hs : ∀ a, q a = 0 → p a = 0)
    {x : Fin n → α} (hx : iidMass n q x = 0) : iidMass n p x = 0 := by
  unfold iidMass at hx ⊢
  obtain ⟨j,hj,hq⟩ := Finset.prod_eq_zero_iff.mp hx
  exact Finset.prod_eq_zero_iff.mpr ⟨j,hj,hs _ hq⟩

theorem mixture_normalized [Nonempty S] {p : S → α → ℝ} (hn : ∀ s, ∑ a, p s a = 1) :
    ∑ a, mixture p a = 1 := by
  unfold mixture
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_comm]
  simp only [hn, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem finite_tv_le_chiSquare {p q : α → ℝ} (hq : ∀ a, 0 ≤ q a)
    (hp1 : ∑ a, p a = 1) (hq1 : ∑ a, q a = 1)
    (hz : ∀ a, q a = 0 → p a = 0) :
    (∑ a, |p a - q a|) / 2 ≤ Real.sqrt (overlapKernel q p p - 1) / 2 := by
  let f := fun a ↦ Real.sqrt (q a)
  let g := fun a ↦ |p a - q a| / Real.sqrt (q a)
  have hfg (a : α) : f a * g a = |p a - q a| := by
    by_cases h : q a = 0
    · simp [f, g, h, hz _ h]
    · have hpos := lt_of_le_of_ne (hq a) (Ne.symm h)
      have hs := (Real.sqrt_pos.2 hpos).ne'
      dsimp [f, g]
      field_simp
  have hf : ∑ a, (f a)^2 = 1 := by
    simpa only [f, Real.sq_sqrt (hq _)] using hq1
  have hg : ∑ a, (g a)^2 = overlapKernel q p p - 1 := by
    have hi (a : α) : (g a)^2 = p a * p a / q a - 2 * p a + q a := by
      by_cases h : q a = 0
      · simp [g, h, hz _ h]
      · simp only [g, div_pow, sq_abs, Real.sq_sqrt (hq a)]
        field_simp
        ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, hq1]
    unfold overlapKernel
    ring
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g
  simp_rw [hfg] at hh
  rw [hf, hg, Real.sqrt_one, one_mul] at hh
  linarith

/-- Bound the change in rejection probability of any randomized finite-alphabet test. -/
theorem rejection_gap_le_tv {p q f : α → ℝ} (hf₀ : ∀ a, 0 ≤ f a) (hf₁ : ∀ a, f a ≤ 1)
    (hpq : ∑ a, p a = ∑ a, q a) :
    (∑ a, p a * f a) - (∑ a, q a * f a) ≤ (∑ a, |p a - q a|) / 2 := by
  rw [← Finset.sum_sub_distrib]
  have hh : ∀ a : α, p a * f a - q a * f a ≤ (|p a - q a| + (p a - q a)) / 2 := by
    intro a
    by_cases h : 0 ≤ p a - q a
    · rw [abs_of_nonneg h]
      have hm := mul_le_mul_of_nonneg_left (hf₁ a) h
      linarith [show (p a - q a) * f a = p a * f a - q a * f a by ring]
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
      have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge h)) (hf₀ a)
      linarith [show (p a - q a) * f a = p a * f a - q a * f a by ring]
  calc
    _ ≤ ∑ a, (|p a - q a| + (p a - q a)) / 2 := Finset.sum_le_sum fun a _ ↦ hh a
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, hpq, sub_self,
        add_zero]

end CanonneHeadEnvelope
