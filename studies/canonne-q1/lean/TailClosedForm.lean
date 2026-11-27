import TailCrossing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max

open scoped BigOperators

namespace CanonneQuantile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def saturatedSet (q : ι → ℝ) (n y : ℝ) : Finset ι :=
  Finset.univ.filter (fun i ↦ 1 ≤ n*y*Real.sqrt (q i))

noncomputable def chosenMass (q : ι → ℝ) (S : Finset ι) : ℝ := ∑ i ∈ S, q i

noncomputable def remainingMoment (q : ι → ℝ) (n : ℝ) (S : Finset ι) : ℝ :=
  n * ∑ i ∈ Sᶜ, q i * Real.sqrt (q i)

noncomputable def positiveQuadraticRoot (B Q : ℝ) : ℝ :=
  (B + Real.sqrt (B^2+4*Q))/2

omit [Fintype ι] [DecidableEq ι] in
private theorem chosenMass_nonneg {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i) (S : Finset ι) :
    0 ≤ chosenMass q S :=
  Finset.sum_nonneg (fun i _ ↦ hq i)

private theorem remainingMoment_nonneg {q : ι → ℝ} (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) (S : Finset ι) : 0 ≤ remainingMoment q n S :=
  mul_nonneg hn (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hq i) (Real.sqrt_nonneg _)))

omit [DecidableEq ι] in
theorem tail_root_square_min_formula (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) :
    let y := root q hq n hn
    y^2 = ∑ i, min (q i) (y*(n*q i*Real.sqrt (q i))) := by
  intro y
  have hr := root_spec q hq hn
  change 0 ≤ y ∧ tail q n y = y at hr
  rcases hr.1.eq_or_lt with hy | hy
  · rw [← hy]
    simp [min_eq_right (hq _)]
  · calc
      _ = y * tail q n y := by rw [hr.2]; ring
      _ = _ := by
        rw [tail_eq_clipped q hq hn hy, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_min_of_nonneg _ _ hy.le]
        congr 1
        field_simp [hy.ne']

theorem tail_square_le_quadratic (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) (S : Finset ι) :
    let y := root q hq n hn
    y^2 ≤ chosenMass q S + remainingMoment q n S * y := by
  intro y
  have he := tail_root_square_min_formula q hq hn
  dsimp only at he
  rw [show y^2 = _ from he, ← Finset.sum_compl_add_sum S, add_comm]
  apply add_le_add
  · exact Finset.sum_le_sum (fun _ _ ↦ min_le_left _ _)
  · unfold remainingMoment
    rw [mul_comm _ y, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (min_le_right _ _).trans_eq (by ring)

theorem tail_square_eq_saturated_quadratic (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) :
    let y := root q hq n hn
    let S := saturatedSet q n y
    y^2 = chosenMass q S + remainingMoment q n S * y := by
  intro y S
  have hy := (root_spec q hq hn).1
  rw [show y^2 = _ from tail_root_square_min_formula q hq hn, ← Finset.sum_compl_add_sum S, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hS : 1 ≤ n*y*Real.sqrt (q i) := (Finset.mem_filter.mp hi).2
    apply min_eq_left
    calc
      q i = 1 * q i := (one_mul _).symm
      _ ≤ (n*y*Real.sqrt (q i))*q i := mul_le_mul_of_nonneg_right hS (hq i)
      _ = _ := by ring
  · unfold remainingMoment
    rw [mul_comm _ y, ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hS : n*y*Real.sqrt (q i) < 1 := by
      apply lt_of_not_ge
      intro h
      exact Finset.mem_compl.mp hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [show y * (n * q i * Real.sqrt (q i)) = y*n*(q i*Real.sqrt (q i)) by ring]
    apply min_eq_right
    calc
      _ = (n*y*Real.sqrt (q i))*q i := by ring
      _ ≤ 1 * q i := mul_le_mul_of_nonneg_right hS.le (hq i)
      _ = _ := one_mul _

omit [DecidableEq ι] in
theorem root_zero_implies_moment_zero (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) (hy : root q hq n hn = 0) :
    n * (∑ i, q i * Real.sqrt (q i)) = 0 := by
  have hr := (root_spec q hq hn).2
  rw [hy] at hr
  simpa [tail, Finset.mul_sum, mul_assoc] using hr

private theorem quadratic_root_props {B Q : ℝ} (_hB : 0 ≤ B) (hQ : 0 ≤ Q) :
    B ≤ positiveQuadraticRoot B Q ∧
      (positiveQuadraticRoot B Q)^2 = Q+B*positiveQuadraticRoot B Q := by
  have h0 : 0 ≤ B^2+4*Q := by positivity
  have hS := Real.sq_sqrt h0
  have hm : B ≤ Real.sqrt (B^2+4*Q) := Real.le_sqrt_of_sq_le (by linarith)
  constructor
  · unfold positiveQuadraticRoot
    linarith
  · unfold positiveQuadraticRoot
    nlinarith

theorem le_positiveQuadraticRoot_of_square_le {y B Q : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (hy : y^2 ≤ Q+B*y) :
    y ≤ positiveQuadraticRoot B Q := by
  let r := positiveQuadraticRoot B Q
  have ⟨hrB,hrEq⟩ := quadratic_root_props hB hQ
  by_contra h
  have hyρ : r < y := lt_of_not_ge h
  have hn : 0 < y+r-B := by linarith [show 0 ≤ r from hB.trans hrB]
  have hh := mul_pos (sub_pos.mpr hyρ) hn
  change r^2 = Q+B*r at hrEq
  nlinarith

theorem eq_positiveQuadraticRoot_of_square_eq {y B Q : ℝ} (hB : 0 ≤ B)
    (hQ : 0 ≤ Q) (hy : 0 < y) (heq : y^2 = Q+B*y) :
    y = positiveQuadraticRoot B Q := by
  let r := positiveQuadraticRoot B Q
  have ⟨hrB,hrEq⟩ := quadratic_root_props hB hQ
  have hR : y+r-B ≠ 0 := by linarith
  have hEq : (y-r)*(y+r-B) = 0 := by
    change r^2 = Q+B*r at hrEq
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hEq).resolve_right hR)

theorem tail_root_eq_saturated_quadratic (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) :
    let y := root q hq n hn
    let S := saturatedSet q n y
    y = positiveQuadraticRoot (remainingMoment q n S) (chosenMass q S) := by
  intro y S
  have hr := root_spec q hq hn
  change 0 ≤ y ∧ tail q n y = y at hr
  rcases hr.1.eq_or_lt with h0 | hpos
  · have hS : S = ∅ := by simp [S, saturatedSet, ← h0]
    have hM := root_zero_implies_moment_zero q hq hn h0.symm
    simp [← h0,hS, positiveQuadraticRoot, chosenMass, remainingMoment, hM]
  · exact eq_positiveQuadraticRoot_of_square_eq (remainingMoment_nonneg hq hn S)
      (chosenMass_nonneg hq S) hpos (tail_square_eq_saturated_quadratic q hq hn)

noncomputable def tailQuadraticMinimum (q : ι → ℝ) (n : ℝ) : ℝ :=
  (Finset.univ.powerset).inf' (Finset.powerset_nonempty _)
    (fun S ↦ positiveQuadraticRoot (remainingMoment q n S) (chosenMass q S))

theorem tail_root_eq_quadratic_minimum (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) : root q hq n hn = tailQuadraticMinimum q n := by
  refine le_antisymm ?_ ?_
  · apply Finset.le_inf'
    intro S _
    exact le_positiveQuadraticRoot_of_square_le (remainingMoment_nonneg hq hn S)
      (chosenMass_nonneg hq S) (tail_square_le_quadratic q hq hn S)
  · rw [tail_root_eq_saturated_quadratic q hq hn]
    exact Finset.inf'_le _ (Finset.mem_powerset.mpr (Finset.subset_univ _))

noncomputable def tailProxyMinimum (q : ι → ℝ) (n : ℝ) : ℝ :=
  (Finset.univ.powerset).inf' (Finset.powerset_nonempty _)
    (fun S ↦ max (chosenMass q S) ((remainingMoment q n S)^2))

private theorem square_le_four_max_of_square_le {y B Q : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B)
    (hQ : 0 ≤ Q) (he : y^2 ≤ Q+B*y) : y^2 ≤ 4*max Q (B^2) := by
  let M := max Q (B^2)
  have hM : 0 ≤ M := hQ.trans (le_max_left _ _)
  have h₂ : B ≤ Real.sqrt M := Real.le_sqrt_of_sq_le (le_max_right _ _)
  have h₃ : y^2 ≤ M + Real.sqrt M*y := he.trans
    (add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right h₂ hy))
  have hs := Real.sq_sqrt hM
  have hx : y ≤ 2 * Real.sqrt M := by
    by_contra h
    have hm := mul_pos (sub_pos.mpr (lt_of_not_ge h))
      (show 0 < y+Real.sqrt M by linarith [Real.sqrt_nonneg M])
    linarith [show (y-2*Real.sqrt M)*(y+Real.sqrt M) =
      y^2-Real.sqrt M*y-2*M by nlinarith]
  have hh := pow_le_pow_left₀ hy hx 2
  nlinarith

theorem tail_root_square_proxy_bounds (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    {n : ℝ} (hn : 0 ≤ n) :
    let y := root q hq n hn
    tailProxyMinimum q n ≤ y^2 ∧ y^2 ≤ 4*tailProxyMinimum q n := by
  intro y
  have hy : 0 ≤ y := (root_spec q hq hn).1
  let S := saturatedSet q n y
  let B := remainingMoment q n S
  let Q := chosenMass q S
  have hS : S ∈ Finset.univ.powerset := Finset.mem_powerset.mpr (Finset.subset_univ _)
  have he : y^2 = Q+B*y := tail_square_eq_saturated_quadratic q hq hn
  have hB : 0 ≤ B := remainingMoment_nonneg hq hn S
  have hQ : 0 ≤ Q := chosenMass_nonneg hq S
  constructor
  · refine (Finset.inf'_le _ hS).trans (max_le ?_ ?_)
    · linarith [mul_nonneg hB hy]
    · change B^2 ≤ y^2
      rcases hy.eq_or_lt with h0 | hp
      · have hSE : S = ∅ := by simp [S,saturatedSet,← h0]
        have hM := root_zero_implies_moment_zero q hq hn h0.symm
        have hB0 : B = 0 := by simp [B,remainingMoment,hSE,hM]
        simp [hB0,← h0]
      · have hb : B ≤ y := by
          apply le_of_not_gt
          intro hh
          nlinarith [mul_pos (sub_pos.mpr hh) hp]
        exact pow_le_pow_left₀ hB hb 2
  · obtain ⟨U,_,hU⟩ := Finset.exists_mem_eq_inf'
      (Finset.powerset_nonempty (s := (Finset.univ : Finset ι)))
      (fun S ↦ max (chosenMass q S) ((remainingMoment q n S)^2))
    change tailProxyMinimum q n = _ at hU
    rw [hU]
    exact square_le_four_max_of_square_le hy (remainingMoment_nonneg hq hn U)
      (chosenMass_nonneg hq U) (tail_square_le_quadratic q hq hn U)

end CanonneQuantile
