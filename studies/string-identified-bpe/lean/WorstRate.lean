import DiamondResult
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Match natural-budget rates to the original infimum of best-tie ratios. -/

namespace SpellingWorstRate

open SpellingBPE DiamondLimit

/-- Integer scale convenient for all natural budgets. -/
def scale (k : ℕ) : ℕ := Nat.sqrt k + 1

theorem scale_pos (k : ℕ) : 0 < scale k := Nat.succ_pos _

theorem budget_le_scale_sq (k : ℕ) : k ≤ scale k * scale k :=
  (Nat.lt_succ_sqrt k).le

private theorem diameter_parameters {k : ℕ} (hk : 8 ≤ k) :
    ∃ m : ℕ, 2 ≤ m ∧ 2*m*m ≤ k ∧ k * scale k ≤ 24 * (m*m*m) := by
  let m := Nat.sqrt (k/2)
  have two : 2 ≤ m := Nat.le_sqrt.mpr (by omega)
  have small : m*m ≤ k/2 := Nat.sqrt_le _
  have above : k/2 < (m+1)*(m+1) := Nat.lt_succ_sqrt _
  have budget : 2*m*m ≤ k := by nlinarith [Nat.div_mul_le_self k 2]
  have up : k < 2*((m+1)*(m+1)) := by omega
  have mplus : m+1 ≤ 2*m := by omega
  have mplusSq := Nat.mul_le_mul mplus mplus
  have wide : k ≤ 8*(m*m) := by nlinarith
  have sk : Nat.sqrt k < 2*(m+1) := Nat.sqrt_lt.mpr (by nlinarith)
  have scaleBound : scale k ≤ 3*m := by unfold scale; omega
  refine ⟨m,two,budget,?_⟩
  calc
    k * scale k ≤ (8*(m*m)) * (3*m) := Nat.mul_le_mul wide scaleBound
    _ = 24*(m*m*m) := by ring

private theorem diamond_upper {k m : ℕ} (run : Run) (two : 2 ≤ m) (budget : 2*m*m ≤ k)
    (scaled : k * scale k ≤ 24*(m*m*m))
    (existsRun : ∃ v, run k (DiamondFamily.input m k) v)
    (all : ∀ v, run k (DiamondFamily.input m k) v →
      (DiamondFamily.input m k).length-v.length = k*(m+1)) :
    (ratios run k).Nonempty ∧ worst run k * (scale k : ℝ) ≤ 24 := by
  let w := DiamondFamily.input m k
  have cmp : m*m*m*(m+1) ≤ optimum w k := DiamondGuarantee.comparator_lower m k budget
  have cmpPos : 0 < m*m*m*(m+1) := by positivity
  have optPos := cmpPos.trans_le cmp
  obtain ⟨v,hv,attains⟩ := best_attained run w k existsRun
  have bestValue : best run w k = k*(m+1) := attains.symm.trans (all v hv)
  have bound : best run w k * scale k ≤ 24*optimum w k := by
    rw [bestValue]
    calc
      (k * (m+1)) * scale k = (k * scale k) * (m+1) := by ring
      _ ≤ (24*(m*m*m)) * (m+1) := Nat.mul_le_mul_right _ scaled
      _ ≤ 24*optimum w k := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 24 cmp
  let a : ℝ := (best run w k : ℝ)/optimum w k
  have inside : a ∈ ratios run k :=
    ⟨w,DiamondResult.input_allowed m k two,optPos,existsRun,rfl⟩
  have lower : BddBelow (ratios run k) := ⟨0,fun _ h => ratio_nonneg run k h⟩
  refine ⟨⟨a,inside⟩,?_⟩
  have witnessed : worst run k ≤ a := csInf_le lower inside
  have castPos : (0 : ℝ) < optimum w k := by exact_mod_cast optPos
  have castBound : (best run w k : ℝ) * (scale k : ℝ) ≤ 24 * (optimum w k : ℝ) := by
    exact_mod_cast bound
  calc
    worst run k * (scale k : ℝ) ≤ a * (scale k : ℝ) :=
      mul_le_mul_of_nonneg_right witnessed (Nat.cast_nonneg _)
    _ = ((best run w k : ℝ) * (scale k : ℝ)) / (optimum w k : ℝ) := by
      unfold a
      ring
    _ ≤ 24 := (div_le_iff₀ castPos).mpr castBound

/-- The full-replacement candidate ranking, with ties chosen in its favour. -/
theorem replacement_diamond {k : ℕ} (hk : 8 ≤ k) :
    (ratios Greedy k).Nonempty ∧ worst Greedy k * (scale k : ℝ) ≤ 24 := by
  obtain ⟨m,two,budget,scaled⟩ := diameter_parameters hk
  have pos : 1 ≤ m := by omega
  exact diamond_upper Greedy two budget scaled (DiamondGuarantee.has_greedy m k pos)
    (DiamondGuarantee.all_ties m k pos)

/-- The overlapping-occurrence ranking, with ties chosen in its favour. -/
theorem overlapping_diamond {k : ℕ} (hk : 8 ≤ k) :
    (ratios RawDiamond.RawGreedy k).Nonempty ∧ worst RawDiamond.RawGreedy k * (scale k : ℝ) ≤ 24 := by
  obtain ⟨m,two,budget,scaled⟩ := diameter_parameters hk
  have pos : 1 ≤ m := by omega
  exact diamond_upper RawDiamond.RawGreedy two budget scaled (RawDiamond.rawGreedy_exists m k pos)
    (fun v h => DiamondGuarantee.all_ties m k pos v
      ((RawDiamond.rawGreedy_iff_greedy_input m k pos v).mp h))

/-- A uniform bound for actual runs passes to the original infimum over
inputs, with the best tie outcome used for each input. -/
theorem lower_of_run_bound (run : Run) {k coefficient : ℕ} (positive : 0 < coefficient)
    (nonempty : (ratios run k).Nonempty)
    (bound : ∀ w v : Word Letters, allowed w → 0 < optimum w k → run k w v →
      optimum w k ≤ coefficient * (w.length-v.length)) :
    1/(coefficient : ℝ) ≤ worst run k := by
  unfold worst
  apply le_csInf nonempty
  intro x hx
  obtain ⟨w,good,optPos,existsRun,rfl⟩ := hx
  obtain ⟨v,hv,attains⟩ := best_attained run w k existsRun
  have h := bound w v good optPos hv
  rw [attains] at h
  have coeffPos : (0 : ℝ) < coefficient := by exact_mod_cast positive
  have realOptPos : (0 : ℝ) < optimum w k := by exact_mod_cast optPos
  apply (div_le_div_iff₀ coeffPos realOptPos).mpr
  have castBound : (optimum w k : ℝ) ≤ (coefficient : ℝ) * (best run w k : ℝ) := by exact_mod_cast h
  simpa only [one_mul,mul_comm (best run w k : ℝ)] using castBound

theorem lower_57_of_runs (run : Run) {k s : ℕ} (positive : 0 < s)
    (nonempty : (ratios run k).Nonempty)
    (bound : ∀ w v : Word Letters, allowed w → 0 < optimum w k → run k w v →
      optimum w k ≤ 57*s*(w.length-v.length)) :
    1/(57*(s : ℝ)) ≤ worst run k := by
  have h := lower_of_run_bound run (show 0 < 57*s by positivity) nonempty bound
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

theorem sqrt_lt_scale (k : ℕ) : Real.sqrt (k : ℝ) < (scale k : ℝ) := by
  have positive : (0 : ℝ) < scale k := by exact_mod_cast scale_pos k
  apply (Real.sqrt_lt' positive).mpr
  exact_mod_cast (Nat.lt_succ_sqrt' k)

theorem scale_le_two_sqrt {k : ℕ} (hk : 0 < k) : (scale k : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
  have floored : (Nat.sqrt k : ℝ) ≤ Real.sqrt (k : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (Nat.sqrt_le' k)
  have one : 1 ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hk)
  simp only [scale,Nat.cast_add,Nat.cast_one]
  linarith

/-- Equivalent real square-root scale with explicit constants. -/
theorem sqrt_bounds (run : Run) {k : ℕ} (hk : 0 < k)
    (lower : 1/(57*(scale k : ℝ)) ≤ worst run k)
    (upper : worst run k * (scale k : ℝ) ≤ 24) :
    (1 : ℝ)/114 ≤ worst run k * Real.sqrt (k : ℝ) ∧ worst run k * Real.sqrt (k : ℝ) ≤ 24 := by
  have nonnegative : 0 ≤ worst run k := Real.sInf_nonneg (fun _ h => ratio_nonneg run k h)
  have scaleP : (0 : ℝ) < scale k := by exact_mod_cast scale_pos k
  have before := (div_le_iff₀ (show 0 < 57 * (scale k : ℝ) by positivity)).mp lower
  have comparison := mul_le_mul_of_nonneg_left (scale_le_two_sqrt hk) nonnegative
  constructor
  · nlinarith only [before, comparison]
  · exact (mul_le_mul_of_nonneg_left (sqrt_lt_scale k).le nonnegative).trans upper

end SpellingWorstRate

#print axioms SpellingWorstRate.replacement_diamond
#print axioms SpellingWorstRate.overlapping_diamond
#print axioms SpellingWorstRate.lower_57_of_runs
#print axioms SpellingWorstRate.sqrt_bounds
