import Attachment
import Phases

/-! The initial BPE gain of each pair in one comb row is at most one.
The phase lemmas bound how often a fixed oriented pair can occur. -/
namespace CombIncidence

open SpellingBPE CombComparator SpellingDecoy

theorem candidate_levels (side : Nat → Bool) (seed depth : Nat) {q : Pair Nat}
    (present : q ∈ candidates (core side seed depth)) :
    ∃ a b : Nat, a ≤ seed+depth ∧ b ≤ seed+depth ∧ q = (level a, level b) := by
  rcases candidate_attachment side seed depth present with loop | ⟨right,i,j,upper,eq,entry⟩
  · exact ⟨seed,seed,by omega,by omega,loop⟩
  · have smaller := entry.2.1
    cases right
    · exact ⟨j,i,upper,by omega,eq⟩
    · exact ⟨i,j,by omega,upper,eq⟩

theorem last_fresh_absent (side : Nat → Bool) (seed depth : Nat) (x : Token Nat) :
    (x, level (seed+depth+1)) ∉ candidates (core side seed depth) := by
  intro present
  obtain ⟨a,b,_,upper,eq⟩ := candidate_levels side seed depth present
  exact level_ne_of_lt (by omega : b < seed+depth+1) (congrArg Prod.snd eq)

theorem first_fresh_absent (side : Nat → Bool) (seed depth : Nat) (x : Token Nat) :
    (level (seed+depth+1), x) ∉ candidates (core side seed depth) := by
  intro present
  obtain ⟨a,b,upper,_,eq⟩ := candidate_levels side seed depth present
  exact level_ne_of_lt (by omega : a < seed+depth+1) (congrArg Prod.fst eq)

theorem core_candidates_nodup (side : Nat → Bool) (seed depth : Nat) :
    (candidates (core side seed depth)).Nodup := by
  induction depth with
  | zero => simp [core, wrap, candidates]
  | succ d ih =>
    rw [core_snoc]
    cases orientation : side (seed+d+1)
    · obtain ⟨i,h,_,_,_,_⟩ := endpoint_history side seed d false
      have atHead : (core side seed d).head? = some (level i) := by simpa [endpoint] using h
      simpa only [orientation, put, Bool.false_eq_true, ite_false, candidates_cons, atHead,
        Option.toList_some, List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
        using And.intro (first_fresh_absent side seed d (level i)) ih
    · obtain ⟨i,h,_,_,_,_⟩ := endpoint_history side seed d true
      have atLast : (core side seed d).getLast? = some (level i) := by simpa [endpoint] using h
      simp only [put, ite_true, candidates_snoc, atLast, Option.toList_some, List.map_cons, List.map_nil]
      rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons]
      exact ⟨last_fresh_absent side seed d (level i),ih⟩

theorem core_gain_le_one (side : Nat → Bool) (seed depth : Nat) (q : Pair Nat) :
    gain q (core side seed depth) ≤ 1 :=
  gain_le_one_of_nodup q _ (core_candidates_nodup side seed depth)

theorem seed_gain_one (side : Nat → Bool) (seed depth : Nat) :
    gain (pair seed) (core side seed depth) = 1 := by
  have result : full (pair seed) (core side seed depth) =
      wrap side (seed+1) [level (seed+1)] depth := by
    unfold core
    rw [full_wrap side (Nat.lt_succ_self seed)]
    have base := full_core_base side seed
    change full (pair seed) [level seed, level seed] = [level (seed+1)] at base
    rw [base]
  rw [gain, core_length, result, wrap_length]
  simp only [List.length_singleton]
  omega

def sixSchedules : List (Nat → Bool) := (List.finRange 6).map CombPhases.side

def sixCore (k seeds : Nat) : Table Nat := coreTable sixSchedules k seeds

theorem sixSchedules_length : sixSchedules.length = 6 := by simp [sixSchedules]

theorem sixCore_comparator_twice {k seeds : Nat} (enough : seeds ≤ k) :
    2 * utility (sixCore k seeds) (rules 0 k) = 6 * (seeds * (2*k+1-seeds)) := by
  simpa only [sixCore, sixSchedules_length] using twice_doubling_table sixSchedules enough

theorem sixCore_token_unary {k seeds : Nat} {row : Nat × Word Nat} {tile : Token Nat}
    (member : row ∈ sixCore k seeds) (present : tile ∈ row.2) :
    tile ≠ [] ∧ ∀ a ∈ tile, a = 0 := by
  obtain ⟨seed, _, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨side, _, rfl⟩ := List.mem_map.mp selected
  exact core_token_unary side seed (k-seed-1) present

def phaseSum (k : Nat) (q : Pair Nat) (seed : Nat) : Nat :=
  ((List.finRange 6).map fun phase => gain q (core (CombPhases.side phase) seed (k-seed-1))).sum

theorem phaseSum_seed (k seed : Nat) : phaseSum k (pair seed) seed = 6 := by
  simp [phaseSum, seed_gain_one]

theorem sixCore_value (k seeds : Nat) (q : Pair Nat) :
    value (sixCore k seeds) q = ((List.range seeds).map (phaseSum k q)).sum := by
  have expand (xs : List Nat) :
      value (xs.flatMap fun s => sixSchedules.map fun side => (1, core side s (k-s-1))) q =
        (xs.map (phaseSum k q)).sum := by
    induction xs with
    | nil => simp [value]
    | cons s tail ih =>
      rw [List.flatMap_cons, value_append, ih]
      simp [value, sixSchedules, List.map_map, phaseSum, Function.comp_def]
  exact expand (List.range seeds)

#print axioms core_candidates_nodup
#print axioms core_gain_le_one
#print axioms sixCore_value

end CombIncidence
