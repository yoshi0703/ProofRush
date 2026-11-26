import Common
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity

namespace DiamondBudget

/-- One construction at every sufficiently large integer budget, without
assuming monotonicity of the optimal greedy ratio in the budget. -/
theorem all_budgets (t : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ m : ℕ, 2 ≤ m ∧ 2*m*m ≤ k ∧
      t*(k*(m+1)) ≤ (m*m*m)*(m+1) := by
  let l := 8*t+2
  refine ⟨2*(l*l),?_⟩
  intro k large
  let m := Nat.sqrt (k/2)
  have small : m*m ≤ k/2 := Nat.sqrt_le _
  have up : k/2 < (m+1)*(m+1) := Nat.lt_succ_sqrt _
  have hm : l ≤ m := by
    by_contra! neg
    have h := Nat.mul_le_mul (show m+1 ≤ l by omega) (show m+1 ≤ l by omega)
    omega
  have two : 2 ≤ m := by dsimp [l] at hm; omega
  have budget : 2*m*m ≤ k := by nlinarith [Nat.div_mul_le_self k 2]
  have upper : k ≤ 8*(m*m) := by
    have b := Nat.mul_le_mul (show m+1 ≤ 2*m by omega) (show m+1 ≤ 2*m by omega)
    have c : k < 2*((m+1)*(m+1)) := by omega
    nlinarith
  refine ⟨m,two,budget,?_⟩
  calc
    t*(k*(m+1)) = (t*k)*(m+1) := by ring
    _ ≤ ((8*t)*(m*m))*(m+1) := by
      apply Nat.mul_le_mul_right
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left t upper
    _ ≤ (m*m*m)*(m+1) := by
      apply Nat.mul_le_mul_right
      have more : 8*t ≤ m := by dsimp [l] at hm; omega
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (m*m) more

theorem epsilon {g o t : ℕ} (positive : 0 < o) (tpos : 0 < t)
    (bound : t*g ≤ o) {e : ℚ} (large : 1/e < t) (epos : 0 < e) :
    (g:ℚ)/o < e := by
  have tposQ : 0 < (t:ℚ) := by exact_mod_cast tpos
  have den : 0 < (o:ℚ) := by exact_mod_cast positive
  have times : (t:ℚ)*g ≤ o := by exact_mod_cast bound
  have h := (div_lt_iff₀ epos).mp large
  have gt : (1:ℚ)/t < e := (div_lt_iff₀ tposQ).mpr (by linarith [mul_comm (t:ℚ) e])
  apply lt_of_le_of_lt _ gt
  apply (div_le_div_iff₀ den tposQ).mpr
  simpa [mul_comm] using times

end DiamondBudget
