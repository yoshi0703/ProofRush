import SignedTransfers
import Mathlib.Data.Fintype.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {ι β : Type*} [Fintype ι] [Fintype β]

noncomputable def ambientLaw (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ) (s : ι → Bool) :
    (ι × Bool) ⊕ β → ℝ :=
  Sum.elim (signedLaw (h ∘ Sum.inl) z s) (h ∘ Sum.inr)

theorem ambientLaw_normalized (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (hn : ∑ a, h a = 1) :
    ∑ a, ambientLaw h z s a = 1 := by
  rw [← hn, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ambientLaw, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
  exact congrArg (· + ∑ b, h (Sum.inr b)) (signedLaw_mass (h ∘ Sum.inl) z s)

omit [Fintype ι] [Fintype β] in
theorem ambientLaw_nonnegative (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (hu : ∀ b, 0 ≤ h (Sum.inr b)) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ a : ι × Bool, z a.1 ≤ h (Sum.inl a)) (a : (ι × Bool) ⊕ β) :
    0 ≤ ambientLaw h z s a := by
  cases a with
  | inl a => exact signedLaw_nonnegative (h ∘ Sum.inl) z s hz hb a
  | inr b => exact hu b

theorem ambientLaw_tv (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (hz : ∀ i, 0 ≤ z i) :
    (∑ a, |ambientLaw h z s a - h a|) / 2 = ∑ i, z i := by
  rw [Fintype.sum_sum_type]
  simp only [ambientLaw, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, sub_self,
    abs_zero, Finset.sum_const_zero, add_zero]
  exact signedLaw_tv (h ∘ Sum.inl) z s hz

theorem ambientLaw_overlap (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ) (s t : ι → Bool)
    (hp : ∀ a : ι × Bool, 0 < h (Sum.inl a)) (hn : ∑ a, h a = 1) :
    overlapKernel h (ambientLaw h z s) (ambientLaw h z t) =
      1 + ∑ i, pairCoefficient (h ∘ Sum.inl) z i * signBit (s i) * signBit (t i) := by
  have ha : ∀ x : ℝ, x * x / x = x := by
    intro x
    by_cases hx : x = 0 <;> simp [hx]
  have hh := signedLaw_overlap_sum (h ∘ Sum.inl) z s t hp
  unfold overlapKernel at hh ⊢
  rw [← hn, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [ambientLaw, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, ha]
  simp only [Function.comp_apply] at hh
  rw [hh]
  ring

variable [DecidableEq ι]

theorem ambient_iid_mixture_second_moment (n : ℕ) (h : (ι × Bool) ⊕ β → ℝ) (z : ι → ℝ)
    (hp : ∀ a : ι × Bool, 0 < h (Sum.inl a)) (hn : ∑ a, h a = 1) :
    let m := mixture (fun s : ι → Bool ↦ iidMass n (ambientLaw h z s))
    overlapKernel (iidMass n h) m m =
      (∑ s : ι → Bool, ∑ t : ι → Bool,
        (1 + ∑ i, pairCoefficient (h ∘ Sum.inl) z i * signBit (s i) * signBit (t i))^n) /
          (Fintype.card (ι → Bool) : ℝ)^2 := by
  dsimp only
  rw [mixture_overlap_self]
  simp_rw [iidMass_overlap, ambientLaw_overlap _ _ _ _ hp hn]

private theorem exp_sum_signed (c : ι → ℝ) (s : ι → Bool) :
    ∑ t : ι → Bool, Real.exp (∑ i, c i * signBit (s i) * signBit (t i)) ≤
      (Fintype.card (ι → Bool) : ℝ) * Real.exp (∑ i, (c i)^2 / 2) := by
  simp_rw [Real.exp_sum]
  have hs := Finset.sum_prod_piFinset (ι := ι) (Finset.univ : Finset Bool)
    (fun i b ↦ Real.exp (c i * signBit (s i) * signBit b))
  rw [show (Fintype.piFinset (fun _ : ι ↦ (Finset.univ : Finset Bool))) = Finset.univ by
    ext x
    simp] at hs
  rw [hs, Fintype.card_fun]
  push_cast
  have hc : (∏ _i : ι, (Fintype.card Bool : ℝ)) =
      (Fintype.card Bool : ℝ) ^ Fintype.card ι := by simp
  rw [← hc, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le
  · intro i _
    rw [Fintype.sum_bool]
    calc
      _ = 2 * Real.cosh (c i) := by
        cases s i <;> simp [signBit, Real.cosh_eq] <;> ring
      _ ≤ (Fintype.card Bool : ℝ) * Real.exp ((c i)^2 / 2) := by
        simpa using mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq (c i))
          (by norm_num : (0 : ℝ) ≤ 2)

/-- An exponential upper bound on one plus chi-squared divergence of the actual paired iid prior. -/
theorem ambient_iid_mixture_second_moment_le (n : ℕ) (h : (ι × Bool) ⊕ β → ℝ)
    (z : ι → ℝ) (hp : ∀ a : ι × Bool, 0 < h (Sum.inl a)) (hn : ∑ a, h a = 1)
    (hu : ∀ b, 0 ≤ h (Sum.inr b)) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ a : ι × Bool, z a.1 ≤ h (Sum.inl a)) :
    let M := mixture (fun s : ι → Bool ↦ iidMass n (ambientLaw h z s))
    overlapKernel (iidMass n h) M M ≤
      Real.exp (∑ i, ((n : ℝ) * pairCoefficient (h ∘ Sum.inl) z i)^2 / 2) := by
  dsimp only
  rw [ambient_iid_mixture_second_moment n h z hp hn]
  set c := (Fintype.card (ι → Bool) : ℝ)
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
  rw [mul_comm, pow_two]
  calc
    _ ≤ ∑ s : ι → Bool, c *
        Real.exp (∑ i, ((n : ℝ) * pairCoefficient (h ∘ Sum.inl) z i)^2 / 2) := by
      apply Finset.sum_le_sum
      intro s _
      apply le_trans _ (exp_sum_signed (fun i ↦ (n : ℝ) * pairCoefficient (h ∘ Sum.inl) z i) s)
      apply Finset.sum_le_sum
      intro t _
      set x := ∑ i, pairCoefficient (h ∘ Sum.inl) z i * signBit (s i) * signBit (t i)
      have hx : 0 ≤ 1 + x := by
        rw [← ambientLaw_overlap _ _ _ _ hp hn]
        exact Finset.sum_nonneg fun a _ ↦ div_nonneg
          (mul_nonneg (ambientLaw_nonnegative h z s hu hz hb a)
            (ambientLaw_nonnegative h z t hu hz hb a))
          (by cases a with | inl a => exact (hp a).le | inr b => exact hu b)
      have he : (1+x)^n ≤ Real.exp ((n : ℝ)*x) := by
        rw [Real.exp_nat_mul]
        apply pow_le_pow_left₀ hx
        simpa [add_comm] using Real.add_one_le_exp x
      apply he.trans
      apply le_of_eq
      congr 1
      unfold x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

end CanonneHeadEnvelope
