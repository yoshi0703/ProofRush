import Uniform
import RawDiamond

namespace BoundedInitial

open SpellingBPE
variable {α : Type} [DecidableEq α]

theorem counted_of_raw_greedy {w v : Word α} {k : Nat}
    (run : RawDiamond.RawGreedy k w v) :
    ∃ rules : List (Pair α), rules.length = k ∧ CountedRun true w rules v := by
  induction run with
  | nil => exact ⟨[],rfl,.nil _⟩
  | @cons k w v p maximal _ ih =>
    obtain ⟨rules,length,history⟩ := ih
    exact ⟨p::rules, by simp [length],.next maximal.2 history⟩

theorem bounded_initial_raw_greedy {w v : Word α} {k : Nat}
    (run : RawDiamond.RawGreedy k w v) (atoms : List (Token α)) (M : Nat)
    (all : ∀ a ∈ w, a ∈ atoms) :
    k * (M-1) * optimum w k ≤
      (k*(M+1)+2*shortTypeBound atoms.length M*(M-1))*(w.length-v.length) := by
  obtain ⟨rules,length,counted⟩ := counted_of_raw_greedy run
  exact bounded_initial_budget counted atoms M k all (Or.inl length)

theorem bounded_initial_replacement_greedy {w v : Word α} {k : Nat}
    (run : Greedy k w v) (atoms : List (Token α)) (M : Nat)
    (all : ∀ a ∈ w, a ∈ atoms) :
    k * (M-1) * optimum w k ≤
      (k*(M+1)+2*shortTypeBound atoms.length M*(M-1))*(w.length-v.length) := by
  obtain ⟨rules,length,counted⟩ := counted_of_greedy run
  exact bounded_initial_budget counted atoms M k all (Or.inl length)

/-- For a given alphabet-size cap and accuracy, one budget works
uniformly for all words, spelling systems, and choices under either
of the existing source-model greedy relations. -/
theorem uniform_source_approximation (A : Nat) (ε : ℝ) (eps_pos : 0 < ε) :
    ∃ K : Nat, ∀ k ≥ K, ∀ (w v : Word α) (atoms : List (Token α)),
      atoms.length ≤ A → (∀ a ∈ w, a ∈ atoms) →
      (Greedy k w v ∨ RawDiamond.RawGreedy k w v) →
      (1-ε)*(optimum w k : ℝ) ≤ (w.length-v.length : Nat) := by
  obtain ⟨K, approximate⟩ := uniform_approximation (α := α) A ε eps_pos
  refine ⟨K,?_⟩
  intro k hk w v atoms size all run
  rcases run with replacement | overlap
  · obtain ⟨rules,len,counted⟩ := counted_of_greedy replacement
    exact approximate k hk false w v rules atoms size all counted (Or.inl len)
  · obtain ⟨rules,len,counted⟩ := counted_of_raw_greedy overlap
    exact approximate k hk true w v rules atoms size all counted (Or.inl len)

#print axioms uniform_source_approximation
#print axioms counted_of_raw_greedy
#print axioms bounded_initial_raw_greedy
#print axioms bounded_initial_replacement_greedy

end BoundedInitial
