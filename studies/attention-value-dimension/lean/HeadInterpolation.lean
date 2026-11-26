import RootWindows
import Softmax
import Mathlib.Tactic.FieldSimp

namespace AttentionInterpolation
open Polynomial AttentionWindows AttentionModel
open scoped BigOperators
noncomputable section
variable {H d : ℕ}

/-- The common denominator with the h-th linear factor removed. -/
def cut (s : Fin H → ℝ) (h : Fin H) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase h, (X + C (s j))

theorem cut_le (s : Fin H → ℝ) (h : Fin H) : (cut s h).natDegree ≤ H := by
  unfold cut
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (s i))]
  simp

theorem cut_self_ne (s : Fin H → ℝ) (inj : Function.Injective s) (h : Fin H) :
    (cut s h).eval (-(s h)) ≠ 0 := by
  simp only [cut, eval_prod, eval_add, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj eq
  apply (Finset.mem_erase.mp hj).1
  apply inj
  linarith

theorem cut_other (s : Fin H → ℝ) {i j : Fin H} (ne : i ≠ j) :
    (cut s i).eval (-(s j)) = 0 := by
  simp only [cut, eval_prod, eval_add, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ne.symm,Finset.mem_univ j⟩) (neg_add_cancel _)

theorem cut_factor (s : Fin H → ℝ) (i : Fin H) (t : ℝ) :
    (t+s i) * (cut s i).eval t = (rootPoly s).eval t := by
  simpa only [cut, rootPoly, eval_prod, eval_add, eval_X, eval_C] using
    Finset.mul_prod_erase Finset.univ (fun j => t+s j) (Finset.mem_univ i)

def residue (s : Fin H → ℝ) (p : Polynomial ℝ) (h : Fin H) : ℝ :=
  p.eval (-(s h)) / (cut s h).eval (-(s h))

def remainder (s : Fin H → ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ h, C (residue s p h) * cut s h

theorem remainder_at_pole (s : Fin H → ℝ) (inj : Function.Injective s) (p : Polynomial ℝ)
    (j : Fin H) : (remainder s p).eval (-(s j)) = p.eval (-(s j)) := by
  simp only [remainder, eval_finsetSum, eval_mul, eval_C]
  rw [Finset.sum_eq_single j]
  · exact div_mul_cancel₀ _ (cut_self_ne s inj j)
  · intro h _ ne
    rw [cut_other s ne, mul_zero]
  · simp

theorem partial_fractions (s : Fin H → ℝ) (inj : Function.Injective s) (positive : ∀ i, 0 < s i)
    (p : Polynomial ℝ) (bounded : p.natDegree ≤ H) (hn : 0 < H) :
    ∃ a : ℝ, ∀ t : ℝ, 0 ≤ t →
      p.eval t / (rootPoly s).eval t = a + ∑ h, residue s p h / (t+s h) := by
  let r := p-remainder s p
  have smallRem : (remainder s p).natDegree ≤ H := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_le _ _).trans (cut_le s i)
  have small : r.natDegree ≤ H := by simpa [r] using natDegree_sub_le_of_le bounded smallRem
  have poles (i : Fin H) : r.eval (-(s i)) = 0 := by simp [r,remainder_at_pole s inj]
  have eq := identifies small hn s inj poles
  refine ⟨r.coeff H, fun t ht => ?_⟩
  have den : 0 < (rootPoly s).eval t := by
    simp only [rootPoly, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_pos (fun i _ => add_pos_of_nonneg_of_pos ht (positive i))
  have split := congrArg (fun v : Polynomial ℝ => v.eval t) eq
  change (p-remainder s p).eval t = (C (r.coeff H) * rootPoly s).eval t at split
  simp only [eval_sub, eval_mul, eval_C, remainder, eval_finsetSum] at split
  apply (div_eq_iff den.ne').2
  rw [add_mul, Finset.sum_mul]
  have cancel (i : Fin H) :
      residue s p i / (t+s i) * (rootPoly s).eval t = residue s p i * (cut s i).eval t := by
    rw [← cut_factor s i]
    have nz := (add_pos_of_nonneg_of_pos ht (positive i)).ne'
    field_simp
  simp_rw [cancel]
  linarith

/-- One ordinary two-token softmax head implements one constant plus a simple pole. -/
theorem one_head {s a b t : ℝ} (positive : 0 < s) (nonneg : 0 ≤ t) :
    head ((s+1)/s) (a+b/s) (a+b/(s+1)) t = a + b/(t+s) := by
  have hs := positive.ne'
  have h1 : s+1 ≠ 0 := by linarith
  have ht : t+s ≠ 0 := (add_pos_of_nonneg_of_pos nonneg positive).ne'
  unfold head headDen headNum
  have form : (1-t)+(s+1)/s*t = (t+s)/s := by field_simp; ring
  rw [form]
  field_simp
  ring

theorem shared_heads (s : Fin H → ℝ) (inj : Function.Injective s) (positive : ∀ i, 0 < s i)
    (features : Fin d → Polynomial ℝ) (deg : ∀ i, (features i).natDegree ≤ H) (hn : 0 < H) :
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ),
      (∀ h, 0 < r h) ∧ ∀ (i : Fin d) (t : ℝ), 0 ≤ t →
      heads r v0 v1 i t = (features i).eval t / (rootPoly s).eval t := by
  choose a hpartial using fun i => partial_fractions s inj positive (features i) (deg i) hn
  let r := fun h => (s h+1)/s h
  let v0 := fun h i => a i / H + residue s (features i) h / s h
  let v1 := fun h i => a i / H + residue s (features i) h / (s h+1)
  refine ⟨r,v0,v1,(fun h => div_pos (by linarith [positive h]) (positive h)),?_⟩
  intro i t ht
  rw [hpartial i t ht]
  simp only [heads,r,v0,v1, one_head (positive _) ht, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]
  field_simp [show (H:ℝ) ≠ 0 by exact_mod_cast hn.ne']

end
end AttentionInterpolation
