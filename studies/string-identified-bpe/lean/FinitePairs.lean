import Isolation

/-! A finite cover of every short ordered pair of visible spellings, uniform
over rows and constructed from the actual previously executed literal rules. -/
namespace BoundedInitial

open SpellingBPE
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
def wordsOfSize (atoms : List (Token α)) : Nat → List (Word α)
  | 0 => [[]]
  | n+1 => atoms.flatMap fun a => (wordsOfSize atoms n).map (List.cons a)

omit [DecidableEq α] in
theorem mem_wordsOfSize {atoms : List (Token α)} (w : Word α)
    (all : ∀ a ∈ w, a ∈ atoms) : w ∈ wordsOfSize atoms w.length := by
  induction w with
  | nil => simp [wordsOfSize]
  | cons a tail ih =>
    exact List.mem_flatMap.mpr ⟨a,all a (by simp),
      List.mem_map.mpr ⟨tail,ih (fun b hb => all b (by simp [hb])),rfl⟩⟩

omit [DecidableEq α] in
theorem length_wordsOfSize (atoms : List (Token α)) (n : Nat) :
    (wordsOfSize atoms n).length = atoms.length ^ n := by
  induction n with
  | zero => simp [wordsOfSize]
  | succ n ih =>
    simp [wordsOfSize, List.length_flatMap, ih, List.map_const', Nat.pow_succ, Nat.mul_comm]

omit [DecidableEq α] in
def shortWords (atoms : List (Token α)) (M : Nat) : List (Word α) :=
  (List.range (M-1)).flatMap fun n => wordsOfSize atoms (n+2)

omit [DecidableEq α] in
def shortTypeBound (A M : Nat) : Nat :=
  ((List.range (M-1)).map fun n => A ^ (n+2)).sum

omit [DecidableEq α] in
theorem length_shortWords (atoms : List (Token α)) (M : Nat) :
    (shortWords atoms M).length = shortTypeBound atoms.length M := by
  simp [shortWords,shortTypeBound,List.length_flatMap,length_wordsOfSize]

omit [DecidableEq α] in
theorem mem_shortWords {atoms : List (Token α)} (M : Nat) (w : Word α)
    (lo : 2 ≤ w.length) (hi : w.length ≤ M) (all : ∀ a ∈ w, a ∈ atoms) :
    w ∈ shortWords atoms M := by
  have eq : w.length - 2 + 2 = w.length := by omega
  refine List.mem_flatMap.mpr ⟨w.length-2, List.mem_range.mpr (by omega),?_⟩
  rw [eq]
  exact mem_wordsOfSize w all

def pairAfter (rules : List (Pair α)) (w : Word α) : Option (Pair α) :=
  match play w rules with
  | [x,y] => some (x,y)
  | _ => none

def shortPairs (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat) : List (Pair α) :=
  (shortWords atoms M).filterMap (pairAfter rules)

theorem shortPairs_length (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat) :
    (shortPairs rules atoms M).length ≤ shortTypeBound atoms.length M := by
  rw [← length_shortWords]
  exact List.length_filterMap_le ..

theorem traceStep_flatten (p : Pair α) (blocks : Blocks α) :
    (traceStep p blocks).flatten = blocks.flatten := by
  rw [traceStep,← List.flatten_flatten,groups_flatten]

theorem traceRun_flatten (rules : List (Pair α)) (w : Word α) :
    (traceRun rules w).flatten = w := by
  induction rules using List.reverseRecOn with
  | nil =>
    change (w.map (fun x => [x])).flatten = w
    induction w with
    | nil => rfl
    | cons x tail ih => simp [ih]
  | append_singleton ps p ih =>
    simpa [traceRun,List.foldl_append,traceStep_flatten] using ih

theorem pair_mem_shortPairs (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat)
    (w : Word α) (l r : Blocks α) (left right : Word α)
    (all : ∀ a ∈ w, a ∈ atoms)
    (factor : traceRun rules w = l ++ [left,right] ++ r)
    (lo : 2 ≤ left.length + right.length) (hi : left.length + right.length ≤ M) :
    (left.flatten,right.flatten) ∈ shortPairs rules atoms M := by
  have flat : w = l.flatten ++ (left ++ right) ++ r.flatten := by
    have eq := congrArg List.flatten factor
    simpa [traceRun_flatten,List.append_assoc] using eq
  apply List.mem_filterMap.mpr
  refine ⟨left ++ right, ?_, ?_⟩
  · apply mem_shortWords M _ (by simpa using lo) (by simpa using hi)
    intro token ht
    exact all token (by rw [flat]; exact List.mem_append_left _ (List.mem_append_right _ ht))
  · rw [pairAfter,pair_replay rules w l r left right factor]

#print axioms shortPairs_length
#print axioms pair_mem_shortPairs

end BoundedInitial
