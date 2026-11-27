import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {ι : Type*}

noncomputable def clamp (a : ι → ℝ) (l : ℝ) (i : ι) : ℝ :=
  min ((a i)^3) (l * (a i)^2)

noncomputable def quarticBudget (I : Finset ι) (a z : ι → ℝ) : ℝ :=
  ∑ i ∈ I, (z i)^4 / (a i)^6

noncomputable def bulk (b W : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (b * W) * W)

noncomputable def cutoffCost [DecidableEq ι] (I R : Finset ι) (a : ι → ℝ) (b : ℝ) : ℝ :=
  bulk b (∑ i ∈ R, (a i)^2) + ∑ i ∈ I \ R, (a i)^3

theorem bulk_pow_four {b W : ℝ} (hb : 0 ≤ b) (hW : 0 ≤ W) :
    (bulk b W)^4 = b * W^3 := by
  have hs : 0 ≤ Real.sqrt (b * W) * W := mul_nonneg (Real.sqrt_nonneg _) hW
  unfold bulk
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hs, mul_pow,
    Real.sq_sqrt (mul_nonneg hb hW)]
  ring

theorem sum_le_bulk {I : Finset ι} {a z : ι → ℝ} {b : ℝ}
    (ha : ∀ i ∈ I, 0 < a i) (hB : quarticBudget I a z ≤ b) :
    ∑ i ∈ I, z i ≤ bulk b (∑ i ∈ I, (a i)^2) := by
  let W := ∑ i ∈ I, (a i)^2
  let V := ∑ i ∈ I, (z i)^2 / (a i)^2
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ ↦ sq_nonneg (a i)
  have hC₁ := Finset.sum_mul_sq_le_sq_mul_sq I (fun i ↦ z i / a i) a
  have hV : ∑ i ∈ I, (z i / a i)^2 = V := by simp_rw [V, div_pow]
  have hA : ∑ i ∈ I, z i / a i * a i = ∑ i ∈ I, z i :=
    Finset.sum_congr rfl fun i hi ↦ div_mul_cancel₀ _ (ha i hi).ne'
  rw [hV, hA] at hC₁
  have hC₂ := Finset.sum_mul_sq_le_sq_mul_sq I (fun i ↦ (z i)^2 / (a i)^3) a
  have hX : ∑ i ∈ I, ((z i)^2 / (a i)^3)^2 = quarticBudget I a z := by
    unfold quarticBudget
    simp_rw [div_pow, ← pow_mul]
  have hY : ∑ i ∈ I, (z i)^2 / (a i)^3 * a i = V := by
    apply Finset.sum_congr rfl
    intro i hi
    have hai := (ha i hi).ne'
    field_simp
  rw [hX, hY] at hC₂
  have hV₂ : V ≤ Real.sqrt (b * W) :=
    Real.le_sqrt_of_sq_le (hC₂.trans (mul_le_mul_of_nonneg_right hB hW))
  exact Real.le_sqrt_of_sq_le (hC₁.trans (mul_le_mul_of_nonneg_right hV₂ hW))

theorem witness_le_every_cutoff [DecidableEq ι] {I R : Finset ι} {a z : ι → ℝ} {b : ℝ}
    (ha : ∀ i ∈ I, 0 < a i) (hz : ∀ i ∈ I, z i ≤ (a i)^3) (hs : R ⊆ I)
    (hB : quarticBudget I a z ≤ b) :
    ∑ i ∈ I, z i ≤ cutoffCost I R a b := by
  have hR : quarticBudget R a z ≤ b := by
    refine le_trans ?_ hB
    unfold quarticBudget
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro i hi _
    exact div_nonneg (by positivity) (pow_nonneg (ha i hi).le _)
  rw [← Finset.sum_sdiff hs, add_comm]
  exact add_le_add (sum_le_bulk (fun i hi ↦ ha i (hs hi)) hR)
    (Finset.sum_le_sum fun i hi ↦ hz i (Finset.mem_sdiff.mp hi).1)

theorem clamp_nonnegative {a : ι → ℝ} {l : ℝ} {i : ι}
    (ha : 0 ≤ a i) (hl : 0 ≤ l) : 0 ≤ clamp a l i :=
  le_min (pow_nonneg ha _) (mul_nonneg hl (sq_nonneg _))

theorem clamp_antitone {κ : Type*} [Preorder κ] {a : κ → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hm : Antitone a) {l : ℝ} (hl : 0 ≤ l) :
    Antitone (clamp a l) := by
  intro i j hij
  exact min_le_min (pow_le_pow_left₀ (ha j) (hm hij) _)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha j) (hm hij) _) hl)

theorem active_cutoff_of_exact_budget [DecidableEq ι] (I : Finset ι) (a : ι → ℝ)
    {l b : ℝ} (ha : ∀ i ∈ I, 0 < a i) (hl : 0 ≤ l)
    (hB : quarticBudget I a (clamp a l) = b) :
    cutoffCost I (I.filter fun i ↦ l < a i) a b ≤ 2 * ∑ i ∈ I, clamp a l i := by
  let R := I.filter fun i ↦ l < a i
  let W := ∑ i ∈ R, (a i)^2
  let U := ∑ i ∈ I \ R, (a i)^3
  let Q := ∑ i ∈ I \ R, (a i)^6
  have hRI : R ⊆ I := Finset.filter_subset _ _
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hU : 0 ≤ U := Finset.sum_nonneg fun i hi ↦
    pow_nonneg (ha i (Finset.mem_sdiff.mp hi).1).le _
  have hA (i : ι) (hi : i ∈ R) : clamp a l i = l * (a i)^2 := by
    apply min_eq_right
    have ht : l ≤ a i := (Finset.mem_filter.mp hi).2.le
    have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg (a i))
    nlinarith
  have hL (i : ι) (hi : i ∈ I \ R) : clamp a l i = (a i)^3 := by
    apply min_eq_left
    have ht : a i ≤ l := le_of_not_gt fun H ↦ (Finset.mem_sdiff.mp hi).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1,H⟩)
    have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg (a i))
    nlinarith
  have hS : ∑ i ∈ I, clamp a l i = l * W + U := by
    rw [← Finset.sum_sdiff hRI (f := fun i ↦ clamp a l i), add_comm]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hA
    · exact Finset.sum_congr rfl hL
  have hB' : b = l^4 * W + Q := by
    rw [← hB]
    unfold quarticBudget
    rw [← Finset.sum_sdiff hRI, add_comm]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hA i hi]
      have hz := (ha i (hRI hi)).ne'
      field_simp
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hL i hi]
      have hz := (ha i (Finset.mem_sdiff.mp hi).1).ne'
      field_simp
  have hQ : Q ≤ l^3 * U := by
    dsimp [Q, U]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have ht : a i ≤ l := le_of_not_gt fun H ↦ (Finset.mem_sdiff.mp hi).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1,H⟩)
    have hp := pow_nonneg (ha i (Finset.mem_sdiff.mp hi).1).le 3
    have hm := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (ha i (Finset.mem_sdiff.mp hi).1).le ht 3) hp
    nlinarith
  have hb : 0 ≤ b := by
    rw [← hB]
    exact Finset.sum_nonneg fun i hi ↦ div_nonneg (by positivity)
      (pow_nonneg (ha i hi).le _)
  have hh : bulk b W ≤ l*W + U := by
    apply (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
    change (bulk b W)^4 ≤ _
    rw [bulk_pow_four hb hW, hB']
    calc
      _ ≤ (l^4 * W + l^3 * U) * W^3 :=
        mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hQ) (pow_nonneg hW _)
      _ = (l*W)^4 + (l*W)^3 * U := by ring
      _ ≤ (l*W + U)^4 := by
        have h := mul_nonneg (pow_nonneg (mul_nonneg hl hW) 3) hU
        have h' := mul_nonneg (sq_nonneg (l*W)) (sq_nonneg U)
        have h'' := mul_nonneg (mul_nonneg hl hW) (pow_nonneg hU 3)
        nlinarith [pow_nonneg hU 4]
  change bulk b W + U ≤ _
  rw [hS]
  linarith [mul_nonneg hl hW]

private theorem clamp_eq_cube_of_le {a : ι → ℝ} {l : ℝ} {i : ι} (h : a i ≤ l) :
    clamp a l i = (a i)^3 := by
  apply min_eq_left
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (a i))
  nlinarith

private theorem budget_at_saturation (I : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ I, 0 < a i) {l : ℝ} (hl : ∀ i ∈ I, a i ≤ l) :
    quarticBudget I a (clamp a l) = ∑ i ∈ I, (a i)^6 := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [clamp_eq_cube_of_le (hl i hi)]
  have h := (ha i hi).ne'
  field_simp

theorem exists_clamped_cutoff [DecidableEq ι] (I : Finset ι) (a : ι → ℝ)
    {b : ℝ} (ha : ∀ i ∈ I, 0 < a i) (hb : 0 ≤ b) :
    ∃ l : ℝ, 0 ≤ l ∧
      quarticBudget I a (clamp a l) ≤ b ∧
      (∀ R ⊆ I, (∑ i ∈ I, clamp a l i) ≤ cutoffCost I R a b) ∧
      ∃ R ⊆ I, (R = ∅ ∨ R = I.filter (fun i ↦ l < a i)) ∧
        cutoffCost I R a b ≤ 2 * ∑ i ∈ I, clamp a l i := by
  let L := ∑ i ∈ I, a i
  have hL : 0 ≤ L := Finset.sum_nonneg fun i hi ↦ (ha i hi).le
  have hLi (i : ι) (hi : i ∈ I) : a i ≤ L :=
    Finset.single_le_sum (fun j hj ↦ (ha j hj).le) hi
  have hSat := budget_at_saturation I a ha hLi
  by_cases hcase : ∑ i ∈ I, (a i)^6 ≤ b
  · have hB : quarticBudget I a (clamp a L) ≤ b := hSat.trans_le hcase
    refine ⟨L,hL,hB,fun R hR ↦ witness_le_every_cutoff ha (fun _ _ ↦ min_le_left _ _) hR hB,
      ∅, Finset.empty_subset _, Or.inl rfl, ?_⟩
    have hS : ∑ i ∈ I, clamp a L i = ∑ i ∈ I, (a i)^3 :=
      Finset.sum_congr rfl fun i hi ↦ clamp_eq_cube_of_le (hLi i hi)
    have hnon : 0 ≤ ∑ i ∈ I, (a i)^3 :=
      Finset.sum_nonneg fun i hi ↦ pow_nonneg (ha i hi).le _
    simp [cutoffCost, bulk, hS]
    linarith
  · let B := fun l ↦ quarticBudget I a (clamp a l)
    have hB0 : B 0 = 0 := by
      unfold B quarticBudget
      apply Finset.sum_eq_zero
      intro i hi
      have hh := pow_nonneg (ha i hi).le 3
      simp [clamp, min_eq_right hh]
    have hcont : Continuous B := by
      apply continuous_finsetSum
      intro i _
      exact ((((continuous_const : Continuous fun _ : ℝ ↦ (a i)^3).min
        (continuous_id.mul continuous_const)).pow 4).div_const _)
    have htarget : b ∈ Set.Icc (B 0) (B L) := by
      rw [hB0, show B L = _ from hSat]
      exact ⟨hb, le_of_lt (lt_of_not_ge hcase)⟩
    obtain ⟨l,hl,hbl⟩ := intermediate_value_Icc hL hcont.continuousOn htarget
    have hE : quarticBudget I a (clamp a l) = b := hbl
    refine ⟨l,hl.1,hE.le,fun R hR ↦ witness_le_every_cutoff ha (fun _ _ ↦ min_le_left _ _) hR hE.le,
      I.filter (fun i ↦ l < a i), Finset.filter_subset _ _, Or.inr rfl, ?_⟩
    exact active_cutoff_of_exact_budget I a ha hl.1 hE

end CanonneHeadEnvelope
