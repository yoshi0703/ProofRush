import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {ι α S : Type*} [Fintype ι] [Fintype α] [Fintype S]

def signBit (b : Bool) : ℝ := if b then 1 else -1

noncomputable def signedLaw (h : ι × Bool → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (a : ι × Bool) : ℝ :=
  h a + z a.1 * signBit (s a.1) * signBit a.2

theorem signedLaw_mass (h : ι × Bool → ℝ) (z : ι → ℝ) (s : ι → Bool) :
    ∑ a, signedLaw h z s a = ∑ a, h a := by
  unfold signedLaw
  rw [Finset.sum_add_distrib]
  suffices ∑ a : ι × Bool, z a.1 * signBit (s a.1) * signBit a.2 = 0 by
    rw [this, add_zero]
  rw [Fintype.sum_prod_type]
  simp [signBit]

omit [Fintype ι] in
theorem signedLaw_nonnegative (h : ι × Bool → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (hz : ∀ i, 0 ≤ z i) (hb : ∀ a : ι × Bool, z a.1 ≤ h a) (a : ι × Bool) :
    0 ≤ signedLaw h z s a := by
  obtain ⟨i,b⟩ := a
  specialize hb (i,b)
  specialize hz i
  cases hs : s i <;> cases b <;> simp [signedLaw, signBit, hs] at * <;> linarith

theorem signedLaw_tv (h : ι × Bool → ℝ) (z : ι → ℝ) (s : ι → Bool)
    (hz : ∀ i, 0 ≤ z i) :
    (∑ a, |signedLaw h z s a - h a|) / 2 = ∑ i, z i := by
  unfold signedLaw
  simp only [add_sub_cancel_left, abs_mul]
  have hs (b : Bool) : |signBit b| = 1 := by cases b <;> norm_num [signBit]
  simp only [hs, mul_one]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, abs_of_nonneg (hz _), ← two_mul, ← Finset.mul_sum]
  ring

noncomputable def overlapKernel (h p q : α → ℝ) : ℝ :=
  ∑ a, p a * q a / h a

noncomputable def pairCoefficient (h : ι × Bool → ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  (z i)^2 * (1 / h (i,false) + 1 / h (i,true))

theorem signedLaw_overlap_sum (h : ι × Bool → ℝ) (z : ι → ℝ) (s t : ι → Bool)
    (hh : ∀ a, 0 < h a) :
    overlapKernel h (signedLaw h z s) (signedLaw h z t) =
      (∑ a, h a) + ∑ i, pairCoefficient h z i * signBit (s i) * signBit (t i) := by
  unfold overlapKernel
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fintype.sum_bool, signedLaw, pairCoefficient, signBit, Bool.false_eq_true,
    ↓reduceIte, mul_neg, mul_one]
  field_simp [(hh (i,false)).ne', (hh (i,true)).ne']
  ring

noncomputable def iidMass (n : ℕ) (p : α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ j, p (x j)

theorem iidMass_overlap (n : ℕ) (h p q : α → ℝ) :
    overlapKernel (iidMass n h) (iidMass n p) (iidMass n q) =
      overlapKernel h p q ^ n := by
  unfold overlapKernel iidMass
  rw [Finset.sum_pow']
  rw [show (Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset α))) = Finset.univ by
    ext x
    simp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]

noncomputable def mixture (p : S → α → ℝ) (a : α) : ℝ :=
  (∑ s, p s a) / (Fintype.card S : ℝ)

theorem mixture_overlap_self (h : α → ℝ) (p : S → α → ℝ) :
    overlapKernel h (mixture p) (mixture p) =
      (∑ s, ∑ t, overlapKernel h (p s) (p t)) / (Fintype.card S : ℝ)^2 := by
  unfold overlapKernel mixture
  set c := (Fintype.card S : ℝ)
  calc
    _ = (∑ a, (∑ s, p s a) * (∑ t, p t a) / h a) / c^2 := by
      conv_rhs =>
        rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      congr 1
      simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_mul]

variable [DecidableEq ι]

/-- Exact second moment of the uniformly signed paired iid alternative relative to the null. -/
theorem signed_iid_mixture_second_moment (n : ℕ) (h : ι × Bool → ℝ) (z : ι → ℝ)
    (hh : ∀ a, 0 < h a) (hn : ∑ a, h a = 1) :
    let m := mixture (fun s : ι → Bool ↦ iidMass n (signedLaw h z s))
    overlapKernel (iidMass n h) m m =
      (∑ s : ι → Bool, ∑ t : ι → Bool,
        (1 + ∑ i, pairCoefficient h z i * signBit (s i) * signBit (t i))^n) /
          (Fintype.card (ι → Bool) : ℝ)^2 := by
  dsimp only
  rw [mixture_overlap_self]
  simp_rw [iidMass_overlap, signedLaw_overlap_sum _ _ _ _ hh, hn]

end CanonneHeadEnvelope
