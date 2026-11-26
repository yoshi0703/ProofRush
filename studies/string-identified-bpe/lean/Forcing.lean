import Separators

/-! Actual single-word maximizing runs, including every tie order. -/
namespace SingleForcing
open SpellingBPE SpellingDecoy SpellingSeparators
variable {α : Type} [DecidableEq α]

theorem score (core : Table α) (M : ℕ) (ps used : List (Pair α)) (unique : ps.Nodup)
    (p : Pair α) : value (augmented core M ps used) p =
      value core p + if p ∈ ps ∧ p ∉ used then M else 0 := by
  rw [augmented,value_append,extras_score _ _ _ _ unique]

theorem fresh_score (core : Table α) (M : ℕ) (ps used : List (Pair α)) (unique : ps.Nodup)
    (isolated : ∀ p ∈ ps, ∀ row ∈ core, p ∉ candidates row.2)
    {p : Pair α} (fresh : p ∈ ps ∧ p ∉ used) :
    gain (liftPair p) (single (augmented core M ps used)) = M := by
  rw [gain_single,score _ _ _ _ unique,ite_eq_left fresh,(core_fixed (isolated _ fresh.1)).2,
    Nat.zero_add]

theorem single_cap (core : Table α) (M : ℕ) (big : 1 ≤ M) (ps used : List (Pair α))
    (unique : ps.Nodup) (bounded : ∀ q, value core q < M)
    (isolated : ∀ p ∈ ps, ∀ row ∈ core, p ∉ candidates row.2)
    (q : Pair (α ⊕ ℕ)) : gain q (single (augmented core M ps used)) ≤ M := by
  by_contra! high
  obtain ⟨p,rfl⟩ := high_is_lift _ q (big.trans_lt high)
  by_cases fresh : p ∈ ps ∧ p ∉ used
  · exact (Nat.not_lt_of_ge (Nat.le_of_eq (fresh_score core M ps used unique isolated fresh))) high
  · rw [gain_single,score _ _ _ _ unique,ite_eq_right fresh,Nat.add_zero] at high
    exact (Nat.not_lt_of_ge (bounded p).le) high

theorem greedy_exists (core : Table α) (M : ℕ) (big : 1 < M) (ps : List (Pair α))
    (unique : ps.Nodup) (bounded : ∀ q, value core q < M)
    (isolated : ∀ p ∈ ps, ∀ row ∈ core, p ∉ candidates row.2)
    (k : ℕ) (used : List (Pair α)) (room : used.length+k ≤ ps.length) :
    ∃ v, Greedy k (single (augmented core M ps used)) v := by
  induction k generalizing used with
  | zero => exact ⟨_,.nil _⟩
  | succ k ih =>
    obtain ⟨p,hp,free⟩ := has_unused unique (show used.length < ps.length by omega)
    have picked := fresh_score core M ps used unique isolated ⟨hp,free⟩
    have maximal : Maximal (single (augmented core M ps used)) (liftPair p) := by
      constructor
      · omega
      · intro q
        rw [picked]
        exact single_cap core M big.le ps used unique bounded isolated q
    obtain ⟨v,tail⟩ := ih (p::used) (by simp only [List.length_cons]; omega)
    refine ⟨v,.cons maximal ?_⟩
    rw [full_single,step_augmented core M ps used p (isolated p hp)]
    exact tail

theorem greedy_length {w v : Word α} {k : ℕ} (run : Greedy k w v) : v.length ≤ w.length := by
  induction run with
  | nil => rfl
  | @cons _ w _ p _ _ ih => exact ih.trans (full_nonincrease p w)

theorem all_greedy (core : Table α) (M : ℕ) (big : 1 < M) (ps : List (Pair α))
    (unique : ps.Nodup) (bounded : ∀ q, value core q < M)
    (isolated : ∀ p ∈ ps, ∀ row ∈ core, p ∉ candidates row.2)
    (k : ℕ) (used : List (Pair α)) (room : used.length+k ≤ ps.length)
    (v : Word (α ⊕ ℕ)) (run : Greedy k (single (augmented core M ps used)) v) :
    (single (augmented core M ps used)).length - v.length = k*M := by
  induction k generalizing used with
  | zero => cases run; simp
  | succ k ih =>
    obtain ⟨fresh,hp,notUsed⟩ := has_unused unique (show used.length < ps.length by omega)
    cases run with
    | @cons _ _ _ q maximal tail =>
      have comparison := maximal.2 (liftPair fresh)
      rw [fresh_score core M ps used unique isolated ⟨hp,notUsed⟩] at comparison
      obtain ⟨p,rfl⟩ := high_is_lift _ q (big.trans_le comparison)
      have selected : p ∈ ps ∧ p ∉ used := by
        by_contra h
        rw [gain_single,score _ _ _ _ unique,ite_eq_right h,Nat.add_zero] at comparison
        exact (Nat.not_lt_of_ge comparison) (bounded p)
      have g := fresh_score core M ps used unique isolated selected
      have st := (full_single (augmented core M ps used) p).trans
        (congrArg single (step_augmented core M ps used p (isolated p selected.1)))
      have le := full_nonincrease (liftPair p) (single (augmented core M ps used))
      have short := greedy_length tail
      rw [st] at tail le short
      have rem := ih (p::used) (by simp only [List.length_cons]; omega) tail
      rw [gain,st] at g
      rw [Nat.succ_mul]
      omega

end SingleForcing
