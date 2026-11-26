import SpellingBPE
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Counted-stage arithmetic and structural counting for literal-spelling BPE.
The replay-based bound on the number of short pair types is stated in README.md. -/
namespace BoundedInitial

open SpellingBPE
open scoped BigOperators

variable {α : Type} [DecidableEq α]

def rawCount (p : Pair α) (w : Word α) : Nat :=
  (candidates w).count p

theorem gain_cons_cons (p : Pair α) (x y : Token α) (rest : Word α)
    (hit : (x,y) = p) : gain p (x::y::rest) = gain p rest + 1 := by
  have length := full_nonincrease p rest
  simp [gain, full, hit]
  omega

theorem gain_skip (p : Pair α) (x y : Token α) (rest : Word α)
    (miss : (x,y) ≠ p) : gain p (x::y::rest) = gain p (y::rest) := by
  simp [gain, full, miss]

theorem raw_le_twice_gain (p : Pair α) (w : Word α) : rawCount p w ≤ 2 * gain p w := by
  induction w using List.twoStepInduction with
  | nil => simp [rawCount, candidates]
  | singleton x => simp [rawCount, candidates]
  | cons_cons x y xs h ih =>
    by_cases hit : (x,y) = p
    · rw [gain_cons_cons p x y xs hit]
      cases xs with
      | nil => simp [rawCount, candidates, hit, gain, full]
      | cons z zs =>
        unfold rawCount at *
        simp only [candidates, List.count_cons, hit, beq_self_eq_true, ite_true]
        split <;> omega
    · rw [gain_skip p x y xs hit]
      have beqMiss : ((x,y) == p) = false := beq_eq_false_iff_ne.mpr hit
      simpa only [rawCount,candidates,List.count_cons,beqMiss,Bool.false_eq_true,ite_false,add_zero] using ih y

omit [DecidableEq α] in
def boundaryExcess : List Nat → Nat
  | [] | [_] => 0
  | x::y::tail => (x-1) + (y-1) + boundaryExcess (y::tail)

omit [DecidableEq α] in
def longBoundaries (M : Nat) : List Nat → Nat
  | [] | [_] => 0
  | x::y::tail => (if M < x+y then 1 else 0) + longBoundaries M (y::tail)

omit [DecidableEq α] in
def blockExcess (sizes : List Nat) :=
  (sizes.map (· - 1)).sum

omit [DecidableEq α] in
theorem endpoint_charge (x : Nat) (tail : List Nat) :
    boundaryExcess (x::tail) + (x-1) ≤ 2 * blockExcess (x::tail) := by
  induction tail generalizing x with
  | nil => simp [blockExcess, boundaryExcess]; omega
  | cons y tail ih =>
    have next := ih y
    simp [boundaryExcess, blockExcess] at *
    omega

omit [DecidableEq α] in
theorem long_charge (M : Nat) (sizes : List Nat) :
    (M-1) * longBoundaries M sizes ≤ boundaryExcess sizes := by
  induction sizes using List.twoStepInduction with
  | nil => simp [boundaryExcess,longBoundaries]
  | singleton x => simp [boundaryExcess,longBoundaries]
  | cons_cons x y xs _ ih =>
    have next := ih y
    simp only [boundaryExcess, longBoundaries, Nat.mul_add] at *
    split
    · rename_i long
      omega
    · omega

omit [DecidableEq α] in
theorem long_charge_total (M : Nat) (sizes : List Nat) :
    (M-1) * longBoundaries M sizes ≤ 2 * blockExcess sizes := by
  apply le_trans (long_charge M sizes)
  cases sizes with
  | nil => simp [blockExcess,boundaryExcess]
  | cons x xs => have h := endpoint_charge x xs; omega

omit [DecidableEq α] in
theorem average_bound (k M types P G : Nat)
    (saved gain : Fin k → Nat)
    (monotone : ∀ i, saved i ≤ G)
    (sumGain : ∑ i, gain i = G)
    (stateBound : ∀ i, (M-1)*P ≤ (M+1)*saved i + 2*types*(M-1)*gain i) :
    k*(M-1)*P ≤ (k*(M+1)+2*types*(M-1))*G := by
  have bound (i : Fin k) : (M-1)*P ≤ (M+1)*G + 2*types*(M-1)*gain i :=
    (stateBound i).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (monotone i)) _)
  have main := Finset.sum_le_sum (s := Finset.univ) (fun i _ => bound i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum (a := 2*types*(M-1)), sumGain] at main
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at main
  calc
    _ = k * ((M-1)*P) := by ac_rfl
    _ ≤ k*((M+1)*G) + 2*types*(M-1)*G := main
    _ = _ := by ring

#print axioms raw_le_twice_gain
#print axioms long_charge_total
#print axioms average_bound

end BoundedInitial
