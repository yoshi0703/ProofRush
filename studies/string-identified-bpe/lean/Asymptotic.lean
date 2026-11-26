import DiamondFamily
import DiamondBudget
import DiamondCount
import Witness
import Forcing

/-! A single actual sequence of tokens at every sufficiently large budget. -/
namespace DiamondGuarantee
open SpellingBPE SpellingDecoy SpellingSeparators Diamond DiamondComparator DiamondFamily

private theorem first_mem {α : Type} {w : Word α} {q : Pair α}
    (h : q ∈ candidates w) : q.1 ∈ w := by
  induction w using List.twoStepInduction with
  | nil => simp [candidates] at h
  | singleton x => simp [candidates] at h
  | cons_cons x y tail _ ih =>
    simp only [candidates,List.mem_cons] at h
    rcases h with rfl | rest
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih y rest)

theorem private_isolated (m k : ℕ) : ∀ p ∈ privatePairs k, ∀ r ∈ coreTable m, p ∉ candidates r.2 := by
  intro p hp r hr hit
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  simp only [coreTable,List.mem_flatMap,List.mem_map] at hr
  obtain ⟨s,_,x,_,y,_,rfl⟩ := hr
  obtain ⟨n,_,eq⟩ := List.mem_map.mp (first_mem hit)
  have inside : i+1 ∈ spell n := by rw [eq]; simp [privatePair]
  simp [spell,List.mem_replicate] at inside

theorem all_ties (m k : ℕ) (hm : 1 ≤ m) (v : Word (ℕ ⊕ ℕ)) (run : Greedy k (input m k) v) :
    (input m k).length-v.length = k*(m+1) :=
  SingleForcing.all_greedy (coreTable m) (m+1) (by omega) (privatePairs k) (private_nodup k)
    (fun q => Nat.lt_succ_of_le (DiamondCount.value_coreTable_le m q)) (private_isolated m k)
    k [] (by simp [private_length]) v run

theorem has_greedy (m k : ℕ) (hm : 1 ≤ m) : ∃ v, Greedy k (input m k) v :=
  SingleForcing.greedy_exists (coreTable m) (m+1) (by omega) (privatePairs k) (private_nodup k)
    (fun q => Nat.lt_succ_of_le (DiamondCount.value_coreTable_le m q)) (private_isolated m k)
    k [] (by simp [private_length])

theorem partial_feasible {α : Type} [DecidableEq α] {w v : Word α} {ps : List (Pair α)}
    (run : PartialPlay w ps v) : Feasible ps.length w v := by
  induction ps generalizing w with
  | nil => change w=v at run; subst v; exact .nil _
  | cons p tail ih =>
    obtain ⟨mid,step,rest⟩ := run
    exact .cons step (ih rest)

theorem comparator_lower (m k : ℕ) (budget : 2*m*m ≤ k) :
    m*m*m*(m+1) ≤ optimum (input m k) k := by
  have path := partial_feasible (DiamondWitness.serialized_augmented_run m (extras m k))
  have len : ((comparator m).map liftPair).length ≤ k := by simpa [comparator_length] using budget
  have bound := feasible_le_optimum len path
  have saved := DiamondWitness.serialized_exact_saving m (extras m k)
  unfold input
  omega

/-- For every positive rational tolerance, every sufficiently large budget admits
one input with positive optimum and at least one complete greedy run. Every tie
order has utility below the tolerance times the original partial-merge optimum. -/
theorem arbitrarily_small (ε : ℚ) (positive : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∃ m : ℕ, 2 ≤ m ∧ 0 < optimum (input m k) k ∧
      (∃ v, Greedy k (input m k) v) ∧
      ∀ v, Greedy k (input m k) v →
        (((input m k).length - v.length : ℕ) : ℚ) / optimum (input m k) k < ε := by
  obtain ⟨t, ht⟩ := exists_nat_gt (1/ε)
  have tp : 0 < t := by
    have : (0:ℚ) < t := (div_pos one_pos positive).trans ht
    exact_mod_cast this
  obtain ⟨K,large⟩ := DiamondBudget.all_budgets t
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨m,two,budget,bound⟩ := large k hk
  have opt := comparator_lower m k budget
  have mp : 0 < m := by omega
  have corePos : 0 < m*m*m*(m+1) := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos mp mp) mp) (Nat.succ_pos _)
  have opos : 0 < optimum (input m k) k := corePos.trans_le opt
  refine ⟨m,two,opos,has_greedy m k (by omega),?_⟩
  intro v run
  apply DiamondBudget.epsilon opos tp _ ht positive
  rw [all_ties m k (by omega) v run]
  exact bound.trans opt

end DiamondGuarantee
