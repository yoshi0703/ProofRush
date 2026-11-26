import GridBarrier
import Bridge

namespace AttentionWindows
open scoped BigOperators
open AttentionGrid AttentionModel AttentionBridge AttentionChart Polynomial
noncomputable section

theorem cleared_degree {H D d M : ℕ} (ps : Fin (d+1) → Polynomial ℝ)
    (bounded : ∀ row, (ps row).natDegree ≤ H) (w : Fin M → ℝ)
    (exponent : Fin M → Fin d → ℕ) (deg : ∀ k, mass d M exponent k ≤ D) :
    (cleared (D := D) ps w exponent).natDegree ≤ H*D := by
  unfold cleared
  apply natDegree_sum_le_of_forall_le
  intro k _
  calc
    _ ≤ (C (w k) * ps 0 ^ (D-mass d M exponent k)).natDegree +
        (∏ i, ps i.succ ^ exponent k i).natDegree := natDegree_mul_le
    _ ≤ (ps 0 ^ (D-mass d M exponent k)).natDegree +
        ∑ i, (ps i.succ ^ exponent k i).natDegree := by
      exact Nat.add_le_add (natDegree_C_mul_le ..) (natDegree_prod_le ..)
    _ ≤ H*(D-mass d M exponent k) + ∑ i, H*exponent k i := by
      apply Nat.add_le_add
      · rw [Nat.mul_comm H (D-mass d M exponent k)]
        exact natDegree_pow_le_of_le _ (bounded 0)
      · apply Finset.sum_le_sum
        intro i _
        rw [Nat.mul_comm H (exponent k i)]
        exact natDegree_pow_le_of_le _ (bounded i.succ)
    _ = _ := by
      rw [← Finset.mul_sum, ← Nat.mul_add]
      exact congrArg (H*·) (Nat.sub_add_cancel (deg k))

/-- Explicit polynomial thresholds on binary inputs missed by every softmax
layer in a prescribed finite support of readout monomials. -/
theorem readout_obstruction {H D d M : ℕ} (small : Count H d M < H*D)
    (exponent : Fin M → Fin d → ℕ) (deg : ∀ k, mass d M exponent k ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∃ (target : Polynomial ℝ) (b : MvPolynomial (Fin n) ℝ),
      target.natDegree = H*D ∧ b.totalDegree ≤ H*D ∧
      (∀ bits : Fin n → Bool, MvPolynomial.eval (booleanReals bits) b =
        target.eval (grid n (hammingWeight bits))) ∧
      (∀ k : Fin (n+1), target.eval (grid n k) ≠ 0) ∧
      ∀ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (w : Fin M → ℝ),
        (∀ h, 0 < r h) → ¬ (∀ k : Fin (n+1), 0 < target.eval (grid n k) *
        readout w exponent (fun i => heads r v0 v1 i (grid n k))) := by
  obtain ⟨n,hn,target,b,targetD,bD,vals,strict,miss⟩ :=
    boolean_obstruction small (coefficient H D d M exponent)
  refine ⟨n,hn,target,b,targetD,bD,vals,strict,?_⟩
  intro r v0 v1 w hr agree
  let ps := modelPolys r v0 v1
  let p := cleared (D:=D) ps w exponent
  let x := assignment H d M (coefficients H d M ps w)
  apply miss x p (cleared_degree ps (modelPolys_degree r v0 v1) w exponent deg)
    (model_coefficient_chart r v0 v1 w exponent)
  intro k
  have bounds := grid_bounds hn k
  change 0 < target.eval (grid n k) * (cleared (D:=D) (modelPolys r v0 v1) w exponent).eval _
  rw [model_cleared r v0 v1 w exponent deg _ hr bounds.1 bounds.2, mul_left_comm]
  exact mul_pos (pow_pos (commonDen_pos r _ hr bounds.1 bounds.2) D) (agree k)

private theorem positive_margin {I : Type*} [Fintype I] (y : I → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, y i ≠ 0 → δ < |y i| := by
  classical
  have go (s : Finset I) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, y i ≠ 0 → δ < |y i| := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,one_pos,by simp⟩
    | insert j s _ ih =>
      obtain ⟨δ,hd,small⟩ := ih
      by_cases zero : y j = 0
      · exact ⟨δ,hd,by simpa [zero] using small⟩
      · refine ⟨min δ (|y j|/2), lt_min hd (by positivity), ?_⟩
        intro i hi hne
        rcases Finset.mem_insert.mp hi with rfl | other
        · exact (min_le_right ..).trans_lt (by linarith [abs_pos.mpr zero])
        · exact (min_le_left ..).trans_lt (small i other hne)
  obtain ⟨δ,hd,h⟩ := go Finset.univ
  exact ⟨δ,hd,fun i => h i (Finset.mem_univ i)⟩

/-- Both possible choices for the Boolean sign of zero give the same
representations when the readout has an adjustable constant. -/
theorem strict_bias {I : Type*} [Fintype I] (f y : I → ℝ) (strict : ∀ i, f i ≠ 0)
    (positiveZero : Bool) (agreement : ∀ i, 0 < f i ↔
      (if positiveZero then 0 ≤ y i else 0 < y i)) :
    ∃ a : ℝ, ∀ i, 0 < f i * (y i + a) := by
  obtain ⟨δ,hδ,small⟩ := positive_margin y
  cases positiveZero with
  | true =>
    refine ⟨δ,fun i => ?_⟩
    have agree : 0 < f i ↔ 0 ≤ y i := agreement i
    by_cases pos : 0 < f i
    · exact mul_pos pos (add_pos_of_nonneg_of_pos (agree.mp pos) hδ)
    · have neg : y i < 0 := lt_of_not_ge (fun h => pos (agree.mpr h))
      have gap := small i neg.ne
      rw [abs_of_neg neg] at gap
      exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt pos) (strict i)) (by linarith)
  | false =>
    refine ⟨-δ,fun i => ?_⟩
    have agree : 0 < f i ↔ 0 < y i := agreement i
    by_cases pos : 0 < f i
    · have raw := agree.mp pos
      have gap := small i raw.ne'
      rw [abs_of_pos raw] at gap
      exact mul_pos pos (by linarith)
    · have nonpos : y i ≤ 0 := le_of_not_gt (fun h => pos (agree.mpr h))
      exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt pos) (strict i)) (by linarith)

end
end AttentionWindows
