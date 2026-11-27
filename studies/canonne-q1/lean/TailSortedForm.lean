import TailClosedForm

open scoped BigOperators

namespace CanonneQuantile

def tailPrefix (d j : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun i ↦ i.val < j)

theorem saturated_is_prefix {d : ℕ} (q : Fin d → ℝ) (hq : Antitone q)
    {n y : ℝ} (hn : 0 ≤ n) (hy : 0 ≤ y) :
    ∃ j ≤ d, saturatedSet q n y = tailPrefix d j := by
  let t := fun i : Fin d ↦ n*y*Real.sqrt (q i)
  have hmono : Antitone t := fun i j hij ↦
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hq hij)) (mul_nonneg hn hy)
  let U : Finset (Fin d) := Finset.univ.filter (fun i ↦ t i < 1)
  by_cases hU : U.Nonempty
  · let j := U.min' hU
    have hj : t j < 1 := (Finset.mem_filter.mp (Finset.min'_mem U hU)).2
    refine ⟨j.val,j.isLt.le,?_⟩
    ext i
    change (i ∈ Finset.univ.filter (fun i ↦ 1 ≤ t i)) ↔ i ∈ tailPrefix d j.val
    simp only [tailPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hn
      exact (not_lt_of_ge (hi.trans (hmono (show j ≤ i from Nat.le_of_not_gt hn)))) hj
    · intro hi
      by_contra hn
      have hi' : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hn⟩
      exact (Nat.not_le_of_gt hi) (Finset.min'_le U i hi')
  · refine ⟨d,le_rfl,?_⟩
    ext i
    change (i ∈ Finset.univ.filter (fun i ↦ 1 ≤ t i)) ↔ i ∈ tailPrefix d d
    simp only [tailPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ ↦ i.isLt, fun _ ↦ le_of_not_gt
      (fun hi ↦ hU ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)⟩

noncomputable def tailPrefixQuadraticMinimum {d : ℕ} (q : Fin d → ℝ) (n : ℝ) : ℝ :=
  (Finset.range (d+1)).inf' ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
    (fun j ↦ positiveQuadraticRoot (remainingMoment q n (tailPrefix d j))
      (chosenMass q (tailPrefix d j)))

/-- The exact tail root is a minimum of only d+1 explicit quantities for a sorted d-label tail. -/
theorem tail_root_eq_prefix_quadratic_minimum {d : ℕ} (q : Fin d → ℝ)
    (hq : ∀ i, 0 ≤ q i) (ho : Antitone q) {n : ℝ} (hn : 0 ≤ n) :
    root q hq n hn = tailPrefixQuadraticMinimum q n := by
  let y := root q hq n hn
  have hy : 0 ≤ y := (root_spec q hq hn).1
  obtain ⟨j,hj,hS⟩ := saturated_is_prefix q ho hn hy
  have hj' : j ∈ Finset.range (d+1) := Finset.mem_range.mpr (by omega)
  refine le_antisymm ?_ ?_
  · apply Finset.le_inf'
    intro j _
    exact le_positiveQuadraticRoot_of_square_le
      (mul_nonneg hn (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hq i) (Real.sqrt_nonneg _))))
      (Finset.sum_nonneg (fun i _ ↦ hq i))
      (tail_square_le_quadratic q hq hn (tailPrefix d j))
  · have he : y = positiveQuadraticRoot (remainingMoment q n (tailPrefix d j))
        (chosenMass q (tailPrefix d j)) := by
      have h := tail_root_eq_saturated_quadratic q hq hn
      dsimp only at h
      change y = positiveQuadraticRoot (remainingMoment q n (saturatedSet q n y))
        (chosenMass q (saturatedSet q n y)) at h
      rw [hS] at h
      exact h
    exact (Finset.inf'_le _ hj').trans he.ge

end CanonneQuantile
