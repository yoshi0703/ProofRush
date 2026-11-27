import ClampedEnvelope
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace CanonneHeadEnvelope

def rightOffset (d : ℕ) (j : Fin ((d+1)/2)) : Fin d :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

def adjacentEmbedding (d : ℕ) : (Fin ((d+1)/2) × Bool) ↪ Fin (d+1) where
  toFun p := ⟨2 * p.1.val + (if p.2 then 1 else 0), by
    have := p.1.isLt
    cases p.2 <;> simp <;> omega⟩
  inj' := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    have hv := congrArg Fin.val h
    change 2 * i.val + (if b then 1 else 0) = 2 * j.val + (if c then 1 else 0) at hv
    have he : i = j := Fin.ext (by cases b <;> cases c <;> simp at hv <;> omega)
    have hb : b = c := by cases b <;> cases c <;> simp at hv ⊢ <;> omega
    exact Prod.ext he hb

theorem adjacentEmbedding_right (d : ℕ) (j : Fin ((d+1)/2)) :
    adjacentEmbedding d (j,true) = (rightOffset d j).succ := rfl

theorem adjacentEmbedding_left_le_right (d : ℕ) (j : Fin ((d+1)/2)) :
    adjacentEmbedding d (j,false) ≤ adjacentEmbedding d (j,true) := by
  change 2 * j.val + 0 ≤ 2 * j.val + 1
  omega

private theorem rightOffset_injective (d : ℕ) : Function.Injective (rightOffset d) := by
  intro a b h
  have hv := congrArg Fin.val h
  change 2 * a.val = 2 * b.val at hv
  exact Fin.ext (by omega)

private theorem sum_alternating_nat (f : ℕ → ℝ) (ha : Antitone f) (m : ℕ) :
    ∑ j ∈ Finset.range (2*m), f (j+1) ≤ 2 * ∑ j ∈ Finset.range m, f (2*j+1) := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [show 2 * (m + 1) = (2*m+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have hi : f (2*m+1+1) ≤ f (2*m+1) := ha (by omega)
    linarith

theorem adjacent_right_recovers_half {d : ℕ} {z : Fin (d+1) → ℝ} (hz : ∀ i, 0 ≤ z i)
    (ha : Antitone z) :
    ∑ i : Fin d, z i.succ ≤ 2 * ∑ j : Fin ((d+1)/2), z (adjacentEmbedding d (j,true)) := by
  let f : ℕ → ℝ := fun i ↦ if hi : i < d+1 then z ⟨i,hi⟩ else 0
  have hf (i : ℕ) : 0 ≤ f i := by
    dsimp [f]
    split
    · apply hz
    · rfl
  have hm : Antitone f := by
    intro i j hij
    by_cases hj : j < d+1
    · have hi : i < d+1 := lt_of_le_of_lt hij hj
      simpa only [f, dite_eq_left hi, dite_eq_left hj] using ha (show (⟨i,hi⟩ : Fin _) ≤ ⟨j,hj⟩ from hij)
    · simpa only [f, dite_eq_right hj] using hf i
  have hl : (∑ i : Fin d, z i.succ) = ∑ i ∈ Finset.range d, f (i+1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.val + 1 < d+1 := by have := i.isLt; omega
    change z i.succ = (if hj : i.val + 1 < d+1 then z ⟨i.val+1,hj⟩ else 0)
    rw [dite_eq_left hi]; rfl
  have hr : (∑ j : Fin ((d+1)/2), z (adjacentEmbedding d (j,true))) =
      ∑ j ∈ Finset.range ((d+1)/2), f (2*j+1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi : 2*i.val + 1 < d+1 := by have := i.isLt; omega
    change z (adjacentEmbedding d (i,true)) =
      (if hj : 2*i.val+1 < d+1 then z ⟨2*i.val+1,hj⟩ else 0)
    rw [dite_eq_left hi]; rfl
  rw [hl, hr]
  refine le_trans ?_ (sum_alternating_nat f hm ((d+1)/2))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun i _ _ ↦ hf (i+1))

theorem adjacent_right_sum_le {d : ℕ} {f : Fin d → ℝ} (hf : ∀ i, 0 ≤ f i) :
    ∑ j : Fin ((d+1)/2), f (rightOffset d j) ≤ ∑ i : Fin d, f i := by
  rw [← Finset.sum_image (rightOffset_injective d).injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hf i)

end CanonneHeadEnvelope
