import Ratio
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Archimedean.Basic


/-! Uniform all-budget arithmetic for the comb upper construction. This
is a conditional numerical lemma; construction and greedy/comparator semantic
properties must be supplied separately. It asserts no 1/6 lower bound. -/
namespace CombLimit

/-- Choose one seed count L for ε, then the same bound holds for all sufficiently
large budgets k. The comparator denominator is its exact formula. -/
theorem all_budgets (ε : ℚ) (hε : 0 < ε) :
    ∃ (L K : Nat), 4 ≤ L ∧ ∀ k : Nat, K ≤ k →
      1 ≤ L ∧ L ≤ k ∧
      ((k : ℚ) * ((L : ℚ)+3)) /
          (6*((L : ℚ)*(k : ℚ) - (L : ℚ)*((L : ℚ)-1)/2)) ≤ 1/6+ε := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (4 : ℚ) (2/ε))
  have hfour : (4 : ℚ) < L := (le_max_left _ _).trans_lt hL
  have hlarge : (2 : ℚ)/ε < L := (le_max_right _ _).trans_lt hL
  have hLnat : 4 ≤ L := by exact_mod_cast (le_of_lt hfour)
  have hLone : (1 : ℚ) ≤ L := by linarith
  have he : (2 : ℚ) ≤ ε * L := by
    have := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  refine ⟨L,L*(L+1),hLnat,?_⟩
  intro k hk
  have hkL : L ≤ k := by nlinarith
  have hkq : (L : ℚ)*((L : ℚ)+1) ≤ k := by exact_mod_cast hk
  refine ⟨by omega,hkL,?_⟩
  have hU : 6*(L:ℚ)*((k:ℚ)-L) ≤ 6*((L:ℚ)*k-(L:ℚ)*(L-1)/2) := by
    nlinarith [sq_nonneg (L : ℚ)]
  exact CombRatio.ratio_near_sixth k L ((L : ℚ)+3)
    (6*((L : ℚ)*(k : ℚ)-(L : ℚ)*((L : ℚ)-1)/2)) ε hLone hkq le_rfl hU he

end CombLimit
