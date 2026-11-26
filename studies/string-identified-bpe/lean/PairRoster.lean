import SpellingBPE

/-! Generic adjacent-pair lemmas for the literal leftmost BPE scan. -/
namespace CombIncidence

open SpellingBPE

section Candidates
variable {α : Type}

theorem candidates_snoc (word : Word α) (x : Token α) :
    candidates (word ++ [x]) =
      candidates word ++ word.getLast?.toList.map (fun y => (y,x)) := by
  induction word using List.twoStepInduction with
  | nil => rfl
  | singleton y => rfl
  | cons_cons y z tail _ ih =>
    simp only [List.cons_append, candidates, List.getLast?_cons_cons, List.cons.injEq, true_and]
    exact ih z

theorem candidates_cons (word : Word α) (x : Token α) :
    candidates (x :: word) =
      word.head?.toList.map (fun y => (x,y)) ++ candidates word := by
  cases word <;> rfl

end Candidates

theorem gain_eq_zero_of_absent {α : Type} [DecidableEq α] {q : Pair α} {w : Word α}
    (absent : q ∉ candidates w) : gain q w = 0 := by
  simp [gain, no_occurrence w absent]

/-- The literal full leftmost scan can use a pair only once when its
adjacent-pair roster has no duplicate. -/
theorem gain_le_one_of_nodup {α : Type} [DecidableEq α] (q : Pair α) (w : Word α)
    (unique : (candidates w).Nodup) : gain q w ≤ 1 := by
  induction w using List.twoStepInduction with
  | nil => simp [gain, full]
  | singleton x => simp [gain, full]
  | cons_cons x y tail _ ih =>
    have headTail : (x,y) ∉ candidates (y::tail) ∧ (candidates (y::tail)).Nodup :=
      List.nodup_cons.mp unique
    by_cases hit : (x,y) = q
    · subst q
      have absent : (x,y) ∉ candidates tail := by
        intro mem
        apply headTail.1
        rw [candidates_cons tail y]
        exact List.mem_append_right _ mem
      have unchanged := no_occurrence tail absent
      simp only [gain, full, ite_true, unchanged, List.length_cons]
      omega
    · unfold gain
      simp only [full, ite_eq_right hit, List.length_cons, Nat.succ_sub_succ_eq_sub]
      exact ih y headTail.2

end CombIncidence
