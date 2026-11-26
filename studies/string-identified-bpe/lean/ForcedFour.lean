import DecoyRows
import SpellingBPE

/-! A family of weighted corpora for which every legal four-step greedy
history violates the source bound. Each of the four core rows has weight n.
Four separate private two-token rows each have weight n+1. -/
namespace SpellingForced
open SpellingBPE SpellingDecoy

def unary (n : ℕ) : Token ℕ := List.replicate n 0

def coreRows : List (Word ℕ) :=
  [[8,4,2,1,1],[8,2,2,4],[4,4,8],[8,8]].map (List.map unary)

def privatePairs : List (Pair ℕ) := ([1,2,3,4] : List ℕ).map fun i => ([i],[i])
def doubling : List (Pair ℕ) := ([1,2,4,8] : List ℕ).map fun i => (unary i,unary i)

def corpus (n : ℕ) := augmented (uniform n coreRows) (n+1) privatePairs []

set_option maxRecDepth 8000
set_option maxHeartbeats 0

theorem no_repeat : privatePairs.Nodup := by decide +kernel

theorem core_distinct : ∀ p ∈ coreRows.flatMap candidates,
    value (uniform 1 coreRows) p ≤ 1 := by decide +kernel

theorem private_unseen : ∀ p ∈ privatePairs, ∀ w ∈ coreRows, p ∉ candidates w := by decide +kernel

theorem unseen (n : ℕ) : ∀ p ∈ privatePairs, ∀ row ∈ uniform n coreRows, p ∉ candidates row.2 := by
  intro p hp row hrow
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hrow
  exact private_unseen p hp w hw

theorem core_bound (n : ℕ) (p : Pair ℕ) : value (uniform n coreRows) p < n+1 := by
  rw [uniform_value]
  by_cases hp : p ∈ coreRows.flatMap candidates
  · have h := Nat.mul_le_mul_left n (core_distinct p hp)
    omega
  · have h : value (uniform 1 coreRows) p = 0 := by
      apply (core_fixed (core := uniform 1 coreRows) (p := p) ?_).2
      intro row hw hpair
      obtain ⟨w,hrow,rfl⟩ := List.mem_map.mp hw
      exact hp (List.mem_flatMap.mpr ⟨w,hrow,hpair⟩)
    simp [h]

theorem available_greedy (n : ℕ) : legal (corpus n) privatePairs :=
  pick_list _ _ _ no_repeat (core_bound n) (unseen n) [] privatePairs
    (fun _ hp => ⟨hp,by simp⟩) no_repeat

theorem all_ties (n : ℕ) (choices : List (Pair ℕ)) (lengthFour : choices.length = 4)
    (hg : legal (corpus n) choices) : utility (corpus n) choices = 4*(n+1) := by
  have h := force _ _ _ no_repeat (core_bound n) (unseen n) [] choices
    (by change 0 + choices.length ≤ 4; omega) hg
  change utility (augmented (uniform n coreRows) (n+1) privatePairs []) choices = _
  rw [lengthFour] at h
  exact h

theorem comparator (n : ℕ) : 10*n ≤ utility (corpus n) doubling := by
  have h : utility (uniform 1 coreRows) doubling = 10 := by decide +kernel
  change _ ≤ utility (uniform n coreRows ++ _) doubling
  rw [utility_append,uniform_utility n, h]
  omega

/-- Every tie order violates the finite-budget constant 15/32, for every
integer scaling n≥6. An actual legal history is supplied by available_greedy. -/
theorem forced_failure (n : ℕ) (large : 6 ≤ n) (choices : List (Pair ℕ))
    (lengthFour : choices.length = 4) (hg : legal (corpus n) choices) :
    32 * utility (corpus n) choices < 15 * utility (corpus n) doubling := by
  rw [all_ties n choices lengthFour hg]
  have h := comparator n
  omega

#print axioms available_greedy
#print axioms forced_failure
end SpellingForced
