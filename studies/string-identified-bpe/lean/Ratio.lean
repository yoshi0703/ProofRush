import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Conditional arithmetic for the comb construction. The geometric input
count and the comparator utility are hypotheses; this module does not claim
an input encoding or a BPE approximation theorem. -/
namespace CombRatio

theorem ratio_bound (k L M U : ℚ) (hL : 1 ≤ L)
    (hk : L*(L+1) ≤ k) (hM : M ≤ L+3)
    (hU : 6*L*(k-L) ≤ U) :
    k*M/U ≤ ((L+3)*(L+1))/(6*L*L) := by
  have hk0 : 0 ≤ k := by nlinarith
  have hgap : 0 < k-L := by nlinarith
  have hu0 : 0 < U := by nlinarith
  have hden : 0 < 6*L*L := by positivity
  apply (div_le_div_iff₀ hu0 hden).2
  have h1 : k*M*(6*L*L) ≤ k*(L+3)*(6*L*L) := by gcongr
  have hab : k*L ≤ (L+1)*(k-L) := by nlinarith
  have hm : 0 ≤ 6*L*(L+3) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hab hm
  have h3 := mul_le_mul_of_nonneg_left hU (show 0 ≤ (L+3)*(L+1) by positivity)
  nlinarith

/-- The conditional bound can be made arbitrarily close to 1/6. -/
theorem bound_near_sixth (L ε : ℚ) (hL : 1 ≤ L) (he : 2 ≤ ε*L) :
    ((L+3)*(L+1))/(6*L*L) ≤ 1/6+ε := by
  have hd : 0 < 6*L*L := by positivity
  apply (div_le_iff₀ hd).2
  have h := mul_nonneg (show 0 ≤ ε*L-2 by linarith) (show 0 ≤ 6*L by positivity)
  nlinarith

theorem ratio_near_sixth (k L M U ε : ℚ) (hL : 1 ≤ L)
    (hk : L*(L+1) ≤ k) (hM : M ≤ L+3)
    (hU : 6*L*(k-L) ≤ U) (he : 2 ≤ ε*L) :
    k*M/U ≤ 1/6+ε :=
  (ratio_bound k L M U hL hk hM hU).trans (bound_near_sixth L ε hL he)

/-- In the first strict finite witness the ratio is below the source bound. -/
theorem four_witness : (28:ℚ)/60 < 15/32 := by norm_num

end CombRatio
