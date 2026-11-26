import Attachment
import Phases

/-! Explicit unary core and disjoint private decoy rows. The uniform core
incidence bound is a separate hypothesis, discharged by IncidenceAggregate. -/
namespace CombCoreTable
open SpellingBPE SpellingDecoy CombComparator CombIncidence

noncomputable section

def schedules : List (Nat → Bool) := (List.finRange 6).map fun p => CombPhases.side p

def coreRows (k L : Nat) : Table Nat := coreTable schedules k L

def privatePair (j : Nat) : Pair Nat := ([2*j+1],[2*j+2])
def privatePairs (k : Nat) : List (Pair Nat) := (List.range k).map privatePair

def multiplicity (L : Nat) : Nat := max 6 (L+2)+1

def table (k L : Nat) : Table Nat := augmented (coreRows k L) (multiplicity L) (privatePairs k) []

theorem schedules_length : schedules.length = 6 := by decide

theorem private_injective : Function.Injective privatePair := by
  intro i j h
  have hl := congrArg Prod.fst h
  simp [privatePair] at hl
  omega

theorem private_nodup (k : Nat) : (privatePairs k).Nodup := by
  exact List.Nodup.map private_injective List.nodup_range

theorem private_length (k : Nat) : (privatePairs k).length = k := by simp [privatePairs]

theorem private_left_ne_level (j i : Nat) : (privatePair j).1 ≠ level i := by
  intro h
  have hm : 2*j+1 ∈ level i := by rw [← h]; simp [privatePair]
  simp only [level, List.mem_replicate] at hm
  omega

theorem private_absent_core (j : Nat) (side : Nat → Bool) (seed depth : Nat) :
    privatePair j ∉ candidates (core side seed depth) := by
  intro present
  rcases candidate_attachment side seed depth present with loop | ⟨direction,i,l,_,eq,_⟩
  · exact private_left_ne_level j seed (congrArg Prod.fst loop)
  · have h := congrArg Prod.fst eq
    cases direction <;> simp only [orientedPair, Bool.false_eq_true, ite_false, ite_true] at h
    · exact private_left_ne_level j l h
    · exact private_left_ne_level j i h

theorem private_isolated (k L : Nat) (q : Pair Nat) (hq : q ∈ privatePairs k)
    (row : Nat × Word Nat) (hr : row ∈ coreRows k L) : q ∉ candidates row.2 := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hq
  simp only [coreRows, coreTable, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨seed,_,side,_,rfl⟩ := hr
  exact private_absent_core j side seed (k-seed-1)

/-- Once the independently proved core-score bound is supplied, every legal
full-length greedy tie history has exactly k times the decoy weight. -/
theorem every_greedy_utility (k L : Nat)
    (bound : ∀ q : Pair Nat, value (coreRows k L) q < multiplicity L)
    (choices : List (Pair Nat)) (hcount : choices.length = k)
    (legalHistory : legal (table k L) choices) :
    utility (table k L) choices = k * multiplicity L := by
  have h := force (coreRows k L) (multiplicity L) (privatePairs k)
    (private_nodup k) bound (private_isolated k L) [] choices (by simp [hcount,private_length]) legalHistory
  simpa [table,hcount] using h

/-- The explicit private order is a legal positive greedy history. -/
theorem some_greedy (k L : Nat)
    (bound : ∀ q : Pair Nat, value (coreRows k L) q < multiplicity L) :
    legal (table k L) (privatePairs k) := by
  apply pick_list (coreRows k L) (multiplicity L) (privatePairs k)
    (private_nodup k) bound (private_isolated k L) [] (privatePairs k)
  · intro q hq
    simp [hq]
  · exact private_nodup k

/-- Full doubling is a valid comparator and achieves at least the core saving,
regardless of the extra rows' contributions. -/
theorem comparator_lower (k L : Nat) (hL : L ≤ k) :
    6 * (L * (2*k+1-L)) ≤ 2 * utility (table k L) (rules 0 k) := by
  have h := twice_doubling_augmented_lower schedules
    ((privatePairs k).map (fun p => extra (multiplicity L) p [])) hL
  simpa [table, augmented, coreRows, schedules_length] using h

end
end CombCoreTable
