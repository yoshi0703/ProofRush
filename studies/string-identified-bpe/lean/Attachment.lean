import CombComparator
import PairRoster

/-! A pair in a comb row is the initial loop or comes from a single
attachment at one of its two endpoints. True denotes right attachment. -/
namespace CombIncidence

open SpellingBPE CombComparator

theorem wrap_snoc (side : Nat → Bool) (start : Nat) (center : Word Nat) (depth : Nat) :
    wrap side start center (depth+1) =
      put (side (start+depth)) (level (start+depth)) (wrap side start center depth) := by
  induction depth generalizing start center with
  | zero => rfl
  | succ d ih =>
    change wrap side (start+1) (put (side start) (level start) center) (d+1) =
      put (side (start+(d+1))) (level (start+(d+1)))
        (wrap side (start+1) (put (side start) (level start) center) d)
    rw [ih, show start+1+d = start+(d+1) by omega]

theorem core_snoc (side : Nat → Bool) (seed depth : Nat) :
    core side seed (depth+1) =
      put (side (seed+depth+1)) (level (seed+depth+1)) (core side seed depth) := by
  unfold core
  rw [wrap_snoc, show seed+1+depth = seed+depth+1 by omega]

theorem core_ne_nil (side : Nat → Bool) (seed depth : Nat) : core side seed depth ≠ [] := by
  intro h
  have len := congrArg List.length h
  simp only [core_length, List.length_nil] at len
  omega

theorem core_token_level (side : Nat → Bool) (seed depth : Nat) {tile : Token Nat}
    (present : tile ∈ core side seed depth) :
    ∃ i, seed ≤ i ∧ i ≤ seed+depth ∧ tile = level i := by
  induction depth with
  | zero =>
    exact ⟨seed, by omega, by omega, by simpa [core, wrap] using present⟩
  | succ d ih =>
    rw [core_snoc] at present
    cases orientation : side (seed+d+1)
    · simp only [orientation, put, Bool.false_eq_true, ite_false, List.mem_cons] at present
      rcases present with fresh | prior
      · exact ⟨seed+d+1, by omega, le_rfl, fresh⟩
      · obtain ⟨i, lower, upper, eq⟩ := ih prior
        exact ⟨i, lower, by omega, eq⟩
    · simp only [orientation, put, ite_true, List.mem_append, List.mem_singleton] at present
      rcases present with prior | fresh
      · obtain ⟨i, lower, upper, eq⟩ := ih prior
        exact ⟨i, lower, by omega, eq⟩
      · exact ⟨seed+d+1, by omega, le_rfl, fresh⟩

theorem core_token_unary (side : Nat → Bool) (seed depth : Nat) {tile : Token Nat}
    (present : tile ∈ core side seed depth) : tile ≠ [] ∧ ∀ a ∈ tile, a = 0 := by
  obtain ⟨i, _, _, rfl⟩ := core_token_level side seed depth present
  constructor
  · intro eq
    have len := congrArg List.length eq
    have pos : 0 < 2^i := Nat.pow_pos (by decide)
    simp only [level, List.length_replicate, List.length_nil] at len
    omega
  · intro a ha
    exact (List.mem_replicate.mp ha).2

def endpoint (right : Bool) (row : Word Nat) : Option (Token Nat) :=
  if right then row.getLast? else row.head?

theorem endpoint_put (right newSide : Bool) (tile : Token Nat) (row : Word Nat) (hn : row ≠ []) :
    endpoint right (put newSide tile row) =
      if right = newSide then some tile else endpoint right row := by
  cases right <;> cases newSide
  · simp [endpoint, put]
  · change (row ++ [tile]).head? = row.head?
    exact List.head?_append_of_ne_nil row hn
  · simp [endpoint, put, List.getLast?_cons_of_ne_nil hn]
  · simp [endpoint, put]

/-- The endpoint records the latest insertion on this side, or the seed
if the side has received no later insertion. -/
theorem endpoint_history (side : Nat → Bool) (seed depth : Nat) (right : Bool) :
    ∃ i : Nat,
      endpoint right (core side seed depth) = some (level i) ∧
      seed ≤ i ∧ i ≤ seed+depth ∧
      (seed < i → side i = right) ∧
      ∀ j, i < j → j ≤ seed+depth → side j ≠ right := by
  induction depth with
  | zero =>
    refine ⟨seed, ?_, le_rfl, by omega, by omega, fun j lo hi => by omega⟩
    cases right <;> rfl
  | succ d ih =>
    let fresh := seed+d+1
    obtain ⟨i, atEnd, lower, upper, oriented, gap⟩ := ih
    rw [core_snoc, endpoint_put _ _ _ _ (core_ne_nil side seed d)]
    by_cases onSide : right = side fresh
    · change ∃ j, (if right = side fresh then some (level fresh) else _) = some (level j) ∧ _
      rw [ite_eq_left onSide]
      exact ⟨fresh, rfl, by dsimp [fresh]; omega, le_rfl, fun _ => onSide.symm,
        fun j lj uj => by dsimp [fresh] at lj; omega⟩
    · change ∃ j, (if right = side fresh then some (level fresh) else _) = some (level j) ∧ _
      rw [ite_eq_right onSide]
      refine ⟨i, atEnd, lower, by omega, oriented, ?_⟩
      intro j below above
      by_cases prior : j ≤ seed+d
      · exact gap j below prior
      · have eq : j = fresh := by dsimp [fresh]; omega
        rw [eq]
        exact Ne.symm onSide

def orientedPair (right : Bool) (i j : Nat) : Pair Nat :=
  if right then (level i, level j) else (level j, level i)

def Attached (side : Nat → Bool) (seed : Nat) (right : Bool) (i j : Nat) : Prop :=
  seed ≤ i ∧ i < j ∧ side j = right ∧ (seed < i → side i = right) ∧
    ∀ u, i < u → u < j → side u ≠ right

theorem candidate_attachment (side : Nat → Bool) (seed depth : Nat) {q : Pair Nat}
    (present : q ∈ candidates (core side seed depth)) :
    q = pair seed ∨ ∃ (right : Bool) (i j : Nat),
      j ≤ seed+depth ∧ q = orientedPair right i j ∧ Attached side seed right i j := by
  induction depth with
  | zero =>
    left
    simpa [core, wrap, candidates, pair] using present
  | succ d ih =>
    let fresh := seed+d+1
    rw [core_snoc] at present
    change q ∈ candidates (put (side fresh) (level fresh) (core side seed d)) at present
    by_cases goesRight : side fresh = true
    · obtain ⟨i, atEnd, lower, upper, earlierSide, gap⟩ := endpoint_history side seed d true
      have endEq : (core side seed d).getLast? = some (level i) := by simpa [endpoint] using atEnd
      simp only [goesRight, put, ite_true, candidates_snoc, endEq, Option.toList_some, List.map_cons,
        List.map_nil, List.mem_append, List.mem_singleton] at present
      rcases present with old | added
      · rcases ih old with loop | ⟨b,a,c,hi,he,h⟩
        · exact Or.inl loop
        · exact Or.inr ⟨b,a,c,by omega,he,h⟩
      · right
        refine ⟨true,i,fresh,le_rfl, ?_, lower, ?_, goesRight, earlierSide, ?_⟩
        · simpa only [orientedPair, ite_true] using added
        · dsimp [fresh]; omega
        · intro u lo hi
          exact gap u lo (by dsimp [fresh] at hi; omega)
    · have goesLeft : side fresh = false := Bool.eq_false_iff.mpr goesRight
      obtain ⟨i, atEnd, lower, upper, earlierSide, gap⟩ := endpoint_history side seed d false
      have endEq : (core side seed d).head? = some (level i) := by simpa [endpoint] using atEnd
      simp only [goesLeft, put, Bool.false_eq_true, ite_false, candidates_cons, endEq, Option.toList_some, List.map_cons,
        List.map_nil, List.mem_append, List.mem_singleton] at present
      rcases present with added | old
      · right
        refine ⟨false,i,fresh,le_rfl, ?_, lower, ?_, goesLeft, earlierSide, ?_⟩
        · simpa only [orientedPair, Bool.false_eq_true, ite_false] using added
        · dsimp [fresh]; omega
        · intro u lo hi
          exact gap u lo (by dsimp [fresh] at hi; omega)
      · rcases ih old with loop | ⟨b,a,c,hi,he,h⟩
        · exact Or.inl loop
        · exact Or.inr ⟨b,a,c,by omega,he,h⟩

theorem level_injective : Function.Injective level := by
  intro i j same
  by_contra! different
  rcases lt_or_gt_of_ne different with lt | gt
  · exact level_ne_of_lt lt same.symm
  · exact level_ne_of_lt gt same

theorem candidate_oriented_attachment (side : Nat → Bool) (seed depth : Nat)
    {right : Bool} {i j : Nat} (earlier : i < j)
    (present : orientedPair right i j ∈ candidates (core side seed depth)) :
    j ≤ seed+depth ∧ Attached side seed right i j := by
  rcases candidate_attachment side seed depth present with loop | ⟨r,a,b,upper,eq,attached⟩
  · exfalso
    have both : level i = level seed ∧ level j = level seed := by
      cases right <;> simp_all [orientedPair, pair, and_comm]
    exact (Nat.ne_of_lt earlier)
      ((level_injective both.1).trans (level_injective both.2).symm)
  · have ab := attached.2.1
    cases right <;> cases r <;> simp only [orientedPair, Bool.false_eq_true,
      ite_false, ite_true, Prod.mk.injEq, level_injective.eq_iff] at eq
    · obtain ⟨rfl,rfl⟩ := eq
      exact ⟨upper, attached⟩
    · omega
    · omega
    · obtain ⟨rfl,rfl⟩ := eq
      exact ⟨upper, attached⟩

theorem candidate_loop_seed (side : Nat → Bool) (seed depth : Nat) {x : Token Nat}
    (present : (x,x) ∈ candidates (core side seed depth)) : x = level seed := by
  rcases candidate_attachment side seed depth present with loop | ⟨direction,i,j,_,equal,attached⟩
  · exact congrArg Prod.fst loop
  · have distinct := level_ne_of_lt attached.2.1
    cases direction <;> simp only [orientedPair, Bool.false_eq_true, ite_true,
      ite_false, Prod.mk.injEq] at equal
    · exact False.elim (distinct (equal.1.symm.trans equal.2))
    · exact False.elim (distinct (equal.2.symm.trans equal.1))

#print axioms candidate_oriented_attachment
#print axioms candidate_loop_seed

end CombIncidence
