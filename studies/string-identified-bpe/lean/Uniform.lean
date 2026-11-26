import SingleWord
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity

namespace BoundedInitial

open SpellingBPE
variable {α : Type} [DecidableEq α]

theorem shortTypeBound_mono {a A M : Nat} (bound : a ≤ A) :
    shortTypeBound a M ≤ shortTypeBound A M := by
  unfold shortTypeBound
  generalize List.range (M-1) = sizes
  induction sizes with
  | nil => exact Nat.le_refl _
  | cons n ns ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (Nat.pow_le_pow_left bound _) ih

theorem uniform_integer (A d : Nat) :
    ∃ K : Nat, ∀ k ≥ K, ∀ (raw : Bool) (w v : Word α) (rules : List (Pair α))
      (atoms : List (Token α)), atoms.length ≤ A →
      (∀ a ∈ w, a ∈ atoms) →
      CountedRun raw w rules v → (rules.length = k ∨ v.length ≤ 1) →
      d * optimum w k ≤ (d+1) * (w.length-v.length) := by
  let M := 4*d+1
  let N := shortTypeBound A M
  refine ⟨max 1 (4*d*N), ?_⟩
  intro k hk raw w v rules atoms size inside h finished
  have positive : 0 < 4*k := by
    have kPos : 1 ≤ k := (Nat.le_max_left ..).trans hk
    omega
  have left : M-1 = 4*d := by omega
  have right : M+1 = 4*d+2 := by omega
  have enough : 4*d*N ≤ k := (Nat.le_max_right ..).trans hk
  have growth := shortTypeBound_mono (M := M) size
  have coefficient : k*(M+1)+2*shortTypeBound atoms.length M*(M-1) ≤ 4*k*(d+1) := by
    have term : 2*shortTypeBound atoms.length M*(M-1) ≤ 2*k := by
      rw [left,show 2*shortTypeBound atoms.length M*(4*d) = 2*(4*d*shortTypeBound atoms.length M) by ring]
      exact Nat.mul_le_mul_left 2 ((Nat.mul_le_mul_left _ growth).trans enough)
    rw [right]
    calc
      _ ≤ k*(4*d+2)+2*k := Nat.add_le_add_left term _
      _ = _ := by ring
  have hmain := bounded_initial_budget h atoms M k inside finished
  have combined := hmain.trans (Nat.mul_le_mul_right _ coefficient)
  rw [left,show k*(4*d)*optimum w k = (4*k)*(d*optimum w k) by ring,
    show (4*k*(d+1))*(w.length-v.length) = (4*k)*((d+1)*(w.length-v.length)) by ring] at combined
  exact Nat.le_of_mul_le_mul_left combined positive

/-- Uniform convergence for bounded initial spelling count, under either greedy
ranking. The alternative on the actual step count allows true exhaustion. -/
theorem uniform_approximation (A : Nat) (ε : ℝ) (eps_pos : 0 < ε) :
    ∃ K : Nat, ∀ k ≥ K, ∀ (raw : Bool) (w v : Word α) (rules : List (Pair α))
      (atoms : List (Token α)), atoms.length ≤ A →
      (∀ a ∈ w, a ∈ atoms) →
      CountedRun raw w rules v → (rules.length = k ∨ v.length ≤ 1) →
      (1-ε) * (optimum w k : ℝ) ≤ (w.length-v.length : Nat) := by
  obtain ⟨d,hd⟩ := exists_nat_gt (1/ε)
  obtain ⟨K,integer⟩ := uniform_integer (α := α) A d
  refine ⟨K,?_⟩
  intro k hk raw w v rules atoms size inside h finished
  have integral := integer k hk raw w v rules atoms size inside h finished
  have real_bound : (d : ℝ) * (optimum w k : ℝ) ≤
      ((d : ℝ)+1) * ((w.length-v.length : Nat) : ℝ) := by exact_mod_cast integral
  have e_times := (div_lt_iff₀ eps_pos).mp hd
  have coef : (1-ε) * ((d : ℝ)+1) ≤ (d : ℝ) := by linarith
  have scaled := (mul_le_mul_of_nonneg_right coef (Nat.cast_nonneg (optimum w k))).trans real_bound
  refine le_of_mul_le_mul_left ?_ (by positivity : 0 < (d : ℝ)+1)
  calc
    _ = (1-ε) * ((d : ℝ)+1) * (optimum w k : ℝ) := by ring
    _ ≤ _ := scaled

#print axioms uniform_integer
#print axioms uniform_approximation

end BoundedInitial
