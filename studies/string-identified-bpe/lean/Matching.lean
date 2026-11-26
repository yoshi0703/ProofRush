import RawDiamond
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! A contraction bound for mass in a fixed family of adjacent-pair labels.
The run relations and the merge semantics are the public string-identified BPE
ones. A label is a pair of literal spellings, even if tokens become aliased. -/

namespace SpellingMatching

open SpellingBPE RawDiamond
open scoped BigOperators

variable {α : Type} [DecidableEq α]

/-- Count all current occurrences of an allowed adjacent pair. -/
def mass (labels : Finset (Pair α)) (w : Word α) : ℕ :=
  ((candidates w).filter (· ∈ labels)).length

/-- The mass contribution from adjoining `x` to the start of `w`. -/
def boundary (labels : Finset (Pair α)) (x : Token α) : Word α → ℕ
  | [] => 0
  | y :: _ => if (x, y) ∈ labels then 1 else 0

@[simp] theorem mass_nil (labels : Finset (Pair α)) : mass labels [] = 0 := rfl

theorem mass_cons (labels : Finset (Pair α)) (x : Token α) (w : Word α) :
    mass labels (x :: w) = mass labels w + boundary labels x w := by
  cases w with
  | nil => rfl
  | cons y ys =>
    by_cases h : (x, y) ∈ labels <;> simp [mass, candidates, boundary, h]

theorem boundary_le_one (labels : Finset (Pair α)) (x : Token α) (w : Word α) :
    boundary labels x w ≤ 1 := by
  cases w with
  | nil => exact Nat.zero_le _
  | cons y ys => by_cases h : (x, y) ∈ labels <;> simp [boundary, h]

theorem mass_le_cons (labels : Finset (Pair α)) (x : Token α) (w : Word α) :
    mass labels w ≤ mass labels (x :: w) := by
  rw [mass_cons]
  exact Nat.le_add_right ..

theorem mass_cons_le (labels : Finset (Pair α)) (x : Token α) (w : Word α) :
    mass labels (x :: w) ≤ mass labels w + 1 := by
  rw [mass_cons]
  exact Nat.add_le_add_left (boundary_le_one labels x w) _

private theorem filter_eq_sum_count {β : Type} [DecidableEq β] [BEq β] [LawfulBEq β]
    (labels : Finset β) (l : List β) :
    (l.filter (· ∈ labels)).length = ∑ q ∈ labels, l.count q := by
  induction l with
  | nil => simp
  | cons x tail ih =>
    have count_cons (q : β) : (x :: tail).count q = tail.count q + if q = x then 1 else 0 := by
      by_cases h : q = x
      · subst q
        simp
      · rw [List.count_cons_of_ne (Ne.symm h), ite_eq_right h, Nat.add_zero]
    simp_rw [count_cons, Finset.sum_add_distrib]
    have ones : (∑ q ∈ labels, if q = x then (1 : ℕ) else 0) = if x ∈ labels then 1 else 0 := by
      simp
    rw [ones, ← ih]
    by_cases h : x ∈ labels <;> simp [h]

theorem mass_eq_sum_raw (labels : Finset (Pair α)) (w : Word α) :
    mass labels w = ∑ p ∈ labels, rawCount p w :=
  filter_eq_sum_count labels (candidates w)

private theorem gain_cons_cons (p : Pair α) (x y : Token α) (w : Word α) :
    gain p (x :: y :: w) = if (x, y) = p then gain p w + 1 else gain p (y :: w) := by
  by_cases h : (x, y) = p
  · have short := full_nonincrease p w
    simp only [gain, full, h, ite_true, List.length_cons]
    omega
  · simp [gain, full, h]

/-- In a full left-to-right scan, each replacement accounts for at most
its own raw adjacency and the one it skips to the right. -/
theorem raw_le_two_gain (p : Pair α) (w : Word α) : rawCount p w ≤ 2 * gain p w := by
  induction w using List.twoStepInduction with
  | nil => simp [rawCount, candidates, gain, full]
  | singleton x => simp [rawCount, candidates, gain, full]
  | cons_cons x y w two one =>
    rw [gain_cons_cons]
    by_cases h : (x, y) = p
    · have first : rawCount p (x :: y :: w) = rawCount p (y :: w) + 1 := by
        simp [rawCount, candidates, h]
      have next : rawCount p (y :: w) ≤ rawCount p w + 1 := by
        cases w with
        | nil => simp [rawCount, candidates]
        | cons z zs =>
          by_cases h' : (y, z) = p <;> simp [rawCount, candidates, h']
      simp only [h, ite_true]
      omega
    · have first : rawCount p (x :: y :: w) = rawCount p (y :: w) := by
        simp [rawCount, candidates, h]
      simpa [h, first] using one y

private def inContext (previous : Option (Token α)) (w : Word α) : Word α :=
  match previous with
  | none => w
  | some x => x :: w

private theorem mass_context_le (labels : Finset (Pair α))
    (previous : Option (Token α)) (w : Word α) : mass labels w ≤ mass labels (inContext previous w) := by
  cases previous with
  | none => exact le_rfl
  | some x => exact mass_le_cons labels x w

private theorem mass_context_le_add_one (labels : Finset (Pair α))
    (previous : Option (Token α)) (w : Word α) :
    mass labels (inContext previous w) ≤ mass labels w + 1 := by
  cases previous with
  | none => exact Nat.le_add_right ..
  | some x => exact mass_cons_le labels x w

private theorem mass_full_context (labels : Finset (Pair α))
    (p : Pair α) (w : Word α) (previous : Option (Token α)) :
    mass labels (inContext previous w) ≤ mass labels (inContext previous (full p w)) + 3 * gain p w := by
  induction w using List.twoStepInduction generalizing previous with
  | nil => simp [full, gain]
  | singleton x => simp [full, gain]
  | cons_cons x y w two one =>
    rw [gain_cons_cons]
    by_cases h : (x, y) = p
    · simp only [full, ite_eq_left h]
      have left := mass_context_le_add_one labels previous (x :: y :: w)
      have removeX := mass_cons_le labels x (y :: w)
      have removeY := mass_cons_le labels y w
      have putBack := mass_le_cons labels (x ++ y) w
      have suffix := two (some (x ++ y))
      have after := mass_context_le labels previous ((x ++ y) :: full p w)
      change mass labels ((x ++ y) :: w) ≤
        mass labels ((x ++ y) :: full p w) + 3 * gain p w at suffix
      omega
    · simp only [full, ite_eq_right h]
      have suffix := one y (some x)
      change mass labels (x :: y :: w) ≤
        mass labels (x :: full p (y :: w)) + 3 * gain p (y :: w) at suffix
      cases previous with
      | none => exact suffix
      | some z =>
        change mass labels (z :: x :: y :: w) ≤
          mass labels (z :: x :: full p (y :: w)) + 3 * gain p (y :: w)
        rw [mass_cons labels z (x :: y :: w), mass_cons labels z (x :: full p (y :: w))]
        simp only [boundary]
        omega

/-- A replacement can remove at most its centre and two outside adjacencies. -/
theorem mass_full_loss (labels : Finset (Pair α)) (p : Pair α) (w : Word α) :
    mass labels w ≤ mass labels (full p w) + 3 * gain p w :=
  mass_full_context labels p w none

private theorem mass_le_of_raw_bound (labels : Finset (Pair α)) (w : Word α) (m : ℕ)
    (bound : ∀ q ∈ labels, rawCount q w ≤ m) : mass labels w ≤ labels.card * m := by
  rw [mass_eq_sum_raw]
  calc
    _ ≤ ∑ _q ∈ labels, m := Finset.sum_le_sum bound
    _ = _ := by simp

private inductive Controlled (labels : Finset (Pair α)) : ℕ → Word α → Word α → Prop
  | nil (w) : Controlled labels 0 w w
  | cons {k w v p} : mass labels w ≤ 2 * labels.card * gain p w →
      Controlled labels k (full p w) v → Controlled labels (k+1) w v

private theorem controlled_nonincrease {labels : Finset (Pair α)} {k : ℕ} {w v : Word α}
    (steps : Controlled labels k w v) : v.length ≤ w.length := by
  induction steps with
  | nil => exact le_rfl
  | @cons k w v p step steps ih => exact ih.trans (full_nonincrease p w)

private theorem controlled_bound {labels : Finset (Pair α)} {k : ℕ} {w v : Word α}
    (steps : Controlled labels k w v) :
    k * mass labels w ≤ (3*k + 2*labels.card) * (w.length-v.length) := by
  induction steps with
  | nil => simp
  | @cons k w v p step steps ih =>
    have suffixSize := controlled_nonincrease steps
    have stepSize := full_nonincrease p w
    have splitGain : gain p w + ((full p w).length-v.length) = w.length-v.length := by
      unfold gain
      omega
    have loss := Nat.mul_le_mul_left k (mass_full_loss labels p w)
    rw [Nat.mul_add] at loss
    calc
      (k+1) * mass labels w = k * mass labels w + mass labels w := Nat.succ_mul ..
      _ ≤ k * mass labels (full p w) + k * (3 * gain p w) + 2 * labels.card * gain p w := by
        omega
      _ = k * mass labels (full p w) + (3*k + 2*labels.card) * gain p w := by ring
      _ ≤ (3*k + 2*labels.card) * ((full p w).length-v.length) +
          (3*k + 2*labels.card) * gain p w := Nat.add_le_add_right ih _
      _ = (3*k + 2*labels.card) * (w.length-v.length) := by
        rw [← Nat.mul_add, Nat.add_comm ((full p w).length-v.length), splitGain]
      _ ≤ (3*(k+1) + 2*labels.card) * (w.length-v.length) := by
        exact Nat.mul_le_mul_right _ (by omega)

private theorem controlled_greedy (labels : Finset (Pair α)) {k : ℕ} {w v : Word α}
    (h : Greedy k w v) : Controlled labels k w v := by
  induction h with
  | nil w => exact .nil w
  | @cons k w v p maximal steps ih =>
    apply Controlled.cons _ ih
    have h := mass_le_of_raw_bound labels w (2 * gain p w) fun q _ =>
      (raw_le_two_gain q w).trans (Nat.mul_le_mul_left 2 (maximal.2 q))
    simpa only [Nat.mul_comm 2 labels.card, Nat.mul_assoc] using h

private theorem controlled_raw_greedy (labels : Finset (Pair α)) {k : ℕ} {w v : Word α}
    (h : RawGreedy k w v) : Controlled labels k w v := by
  induction h with
  | nil w => exact .nil w
  | @cons k w v p maximal steps ih =>
    apply Controlled.cons _ ih
    have h := mass_le_of_raw_bound labels w (2 * gain p w) fun q _ =>
      (maximal.2 q).trans (raw_le_two_gain p w)
    simpa only [Nat.mul_comm 2 labels.card, Nat.mul_assoc] using h

/-- For the public replacement-count greedy run. -/
theorem greedy_mass_bound (labels : Finset (Pair α)) {k : ℕ} {w v : Word α}
    (h : Greedy k w v) : k * mass labels w ≤ (3*k + 2*labels.card) * (w.length-v.length) :=
  controlled_bound (controlled_greedy labels h)

/-- For the public overlapping-count greedy run. -/
theorem raw_greedy_mass_bound (labels : Finset (Pair α)) {k : ℕ} {w v : Word α}
    (h : RawGreedy k w v) : k * mass labels w ≤ (3*k + 2*labels.card) * (w.length-v.length) :=
  controlled_bound (controlled_raw_greedy labels h)

end SpellingMatching

#print axioms SpellingMatching.mass_full_loss
#print axioms SpellingMatching.greedy_mass_bound
#print axioms SpellingMatching.raw_greedy_mass_bound
