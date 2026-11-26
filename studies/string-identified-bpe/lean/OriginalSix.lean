import CoreTable
import IncidenceAggregate
import Forcing
import Mathlib.Tactic.Linarith
import Limit

/-! Original six-phase comb, with replacement-count greedy on the exact single
serialized word. This module builds on the independently checked core cap. -/
namespace OriginalSix
open SpellingBPE SpellingDecoy SpellingSeparators SingleForcing
open CombComparator CombCoreTable CombIncidence CombIncidenceAggregate
noncomputable section

def input (k L : Nat) : Word (Nat ⊕ Nat) := single (table k L)

theorem core_cap (k L : Nat) (q : Pair Nat) : value (coreRows k L) q < multiplicity L := by
  have h := sixCore_uniform_bound k L q
  change value (coreRows k L) q ≤ max 6 (L+2) at h
  unfold multiplicity
  omega

theorem weight_gt_one (L : Nat) : 1 < multiplicity L := by
  unfold multiplicity
  have h := le_max_left 6 (L+2)
  omega

theorem weight_of_large (L : Nat) (hL : 4 ≤ L) : multiplicity L = L+3 := by
  unfold multiplicity
  rw [max_eq_right (by omega)]

theorem greedy_exists (k L : Nat) : ∃ v, Greedy k (input k L) v := by
  apply SingleForcing.greedy_exists (coreRows k L) (multiplicity L) (weight_gt_one L)
    (privatePairs k) (private_nodup k) (core_cap k L) (private_isolated k L) k []
  simp [private_length]

theorem all_ties (k L : Nat) (v : Word (Nat ⊕ Nat)) (run : Greedy k (input k L) v) :
    (input k L).length-v.length = k*multiplicity L := by
  exact SingleForcing.all_greedy (coreRows k L) (multiplicity L) (weight_gt_one L)
    (privatePairs k) (private_nodup k) (core_cap k L) (private_isolated k L) k []
      (by simp [private_length]) v run

def liftedRules (k : Nat) : List (Pair (Nat ⊕ Nat)) := (rules 0 k).map liftPair

theorem liftedRules_length (k : Nat) : (liftedRules k).length = k := by simp [liftedRules,rules_length]

theorem play_nonincrease {α : Type} [DecidableEq α] (w : Word α) (script : List (Pair α)) :
    (play w script).length ≤ w.length := by
  induction script generalizing w with
  | nil => simp [play]
  | cons p ps ih => exact (ih (full p w)).trans (full_nonincrease p w)

theorem play_single_utility (t : Table Nat) (script : List (Pair Nat)) :
    (single t).length - (play (single t) (script.map liftPair)).length = utility t script := by
  induction script generalizing t with
  | nil => simp [play,utility]
  | cons p ps ih =>
    have tail := ih (step t p)
    have h := full_nonincrease (liftPair p) (single t)
    rw [full_single] at h
    have htail := play_nonincrease (single (step t p)) (ps.map liftPair)
    simp only [List.map_cons, play, full_single, utility, ← gain_single, gain] at tail ⊢
    omega

theorem comparator_optimum (k L : Nat) (hL : L ≤ k) :
    6*(L*(2*k+1-L)) ≤ 2*optimum (input k L) k := by
  have cmp := comparator_lower k L hL
  have feasible := plays_feasible (input k L) (liftedRules k)
  have opt := feasible_le_optimum (show (liftedRules k).length ≤ k by simp [liftedRules_length]) feasible
  have utilityEq := play_single_utility (table k L) (rules 0 k)
  change (input k L).length - (play (input k L) (liftedRules k)).length = _ at utilityEq
  omega

theorem six_phase_ratio (k L : Nat) (hL : 4 ≤ L) (hLk : L ≤ k)
    (v : Word (Nat ⊕ Nat)) (run : Greedy k (input k L) v) :
    3*L*(2*k+1-L)*((input k L).length-v.length) ≤
      k*(L+3)*optimum (input k L) k := by
  have g := all_ties k L v run
  rw [weight_of_large L hL] at g
  have c := comparator_optimum k L hLk
  rw [g]
  have lower : 3*L*(2*k+1-L) ≤ optimum (input k L) k := by nlinarith
  have h := Nat.mul_le_mul_left (k*(L+3)) lower
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- For every positive rational tolerance, one seed count works for every
sufficiently large budget and every greedy tie history on this exact family. -/
theorem asymptotic_upper (ε : ℚ) (hε : 0 < ε) :
    ∃ L K : Nat, 4 ≤ L ∧ ∀ k : Nat, K ≤ k →
      ∃ v : Word (Nat ⊕ Nat), Greedy k (input k L) v ∧
      ∀ v : Word (Nat ⊕ Nat), Greedy k (input k L) v →
        (((input k L).length-v.length : Nat) : ℚ) ≤
          (1/6+ε) * (optimum (input k L) k : ℚ) := by
  obtain ⟨L,K,hL,uniform⟩ := CombLimit.all_budgets ε hε
  refine ⟨L,K,hL,?_⟩
  intro k hk
  obtain ⟨_,hLk,hbound⟩ := uniform k hk
  obtain ⟨v,run⟩ := greedy_exists k L
  refine ⟨v,run,?_⟩
  intro v run
  have gt := all_ties k L v run
  rw [weight_of_large L hL] at gt
  let U : ℚ := 6*((L : ℚ)*(k : ℚ) - (L : ℚ)*((L : ℚ)-1)/2)
  have hLq : (4:ℚ) ≤ L := by exact_mod_cast hL
  have hkq : (L:ℚ) ≤ k := by exact_mod_cast hLk
  have Upos : 0<U := by dsimp [U]; nlinarith
  have rationalBound : (k:ℚ)*((L:ℚ)+3) ≤ (1/6+ε)*U :=
    (div_le_iff₀ Upos).mp hbound
  have optNat := comparator_optimum k L hLk
  have subCast : ((2*k+1-L : Nat) : ℚ) = 2*(k:ℚ)+1-L := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have optQ : U ≤ (optimum (input k L) k : ℚ) := by
    have h : ((6*(L*(2*k+1-L)) : Nat) : ℚ) ≤ ((2*optimum (input k L) k : Nat) : ℚ) :=
      Nat.cast_le.mpr optNat
    push_cast at h
    rw [subCast] at h
    dsimp [U]
    nlinarith
  have positive : 0 ≤ 1/6+ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left optQ positive
  have hgt : (((input k L).length-v.length : Nat) : ℚ) = (k:ℚ)*((L:ℚ)+3) := by
    rw [gt]
    push_cast
    ring
  rw [hgt]
  exact rationalBound.trans hmul

theorem level_nonempty (j : Nat) : level j ≠ [] := by
  intro h
  have lengths := congrArg List.length h
  simp [level] at lengths

theorem core_nonempty (side : Nat → Bool) (seed depth : Nat) :
    ∀ token ∈ core side seed depth, token ≠ [] := by
  induction depth with
  | zero => simp [core, wrap, level_nonempty]
  | succ n ih =>
    rw [CombIncidence.core_snoc]
    cases hs : side (seed+n+1) <;> simp only [put, Bool.false_eq_true, ite_false,
      ite_true, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    · intro token ht
      rcases ht with rfl | ht
      · exact level_nonempty _
      · exact ih token ht
    · intro token ht
      rcases ht with ht | rfl
      · exact ih token ht
      · exact level_nonempty _

theorem table_nonempty (k L : Nat) :
    ∀ row ∈ table k L, ∀ token ∈ row.2, token ≠ [] := by
  intro row hr token ht
  change row ∈ coreRows k L ++ (privatePairs k).map (fun p => extra (multiplicity L) p []) at hr
  rcases List.mem_append.mp hr with hc | he
  · simp only [coreRows, coreTable, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨seed,_,side,_,rfl⟩ := hc
    exact core_nonempty side seed _ token ht
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    simp [extra, privatePair] at ht
    rcases ht with rfl | rfl <;> simp

theorem weighted_nonempty (t : Table Nat)
    (h : ∀ row ∈ t, ∀ token ∈ row.2, token ≠ []) :
    ∀ w ∈ weightedRows t, ∀ token ∈ w, token ≠ [] := by
  induction t with
  | nil => simp [weightedRows]
  | cons row rest ih =>
    rcases row with ⟨n,w⟩
    intro v hv token ht
    simp only [weightedRows, List.mem_append, List.mem_replicate] at hv
    rcases hv with ⟨_,rfl⟩ | hv
    · exact h (n,v) (by simp) token ht
    · exact ih (fun row hr => h row (by simp [hr])) v hv token ht

theorem blocks_nonempty (ws : List (Word Nat))
    (h : ∀ w ∈ ws, ∀ token ∈ w, token ≠ []) (start : Nat) :
    ∀ token ∈ blocks start ws, token ≠ [] := by
  induction ws generalizing start with
  | nil => simp [blocks]
  | cons w ws ih =>
    intro token ht
    simp only [blocks, List.mem_append, liftWord, List.mem_map, List.mem_cons] at ht
    rcases ht with ⟨v,hv,rfl⟩ | eq | tail
    · have hn := h w (by simp) v hv
      simpa [embed] using hn
    · subst token
      simp [marker]
    · exact ih (fun row hr => h row (by simp [hr])) (start+1) token tail

theorem input_nonempty (k L : Nat) : ∀ token ∈ input k L, token ≠ [] := by
  apply blocks_nonempty
  exact weighted_nonempty _ (table_nonempty k L)

theorem core_loop_factor (side : Nat → Bool) (seed depth : Nat) :
    Factor [level seed,level seed] (core side seed depth) := by
  induction depth with
  | zero => exact ⟨[],[],by simp [core, wrap]⟩
  | succ n ih =>
    obtain ⟨left,right,split⟩ := ih
    rw [CombIncidence.core_snoc]
    cases hs : side (seed+n+1)
    · refine ⟨level (seed+n+1)::left,right,?_⟩
      simp [put, split]
    · refine ⟨left,right ++ [level (seed+n+1)],?_⟩
      simp [put, split, List.append_assoc]

theorem lift_factor_blocks (u row : Word Nat) (ws : List (Word Nat))
    (start : Nat) (hrow : row ∈ ws) (hfactor : Factor u row) :
    Factor (liftWord u) (blocks start ws) := by
  induction ws generalizing start with
  | nil => simp at hrow
  | cons w ws ih =>
    simp only [List.mem_cons] at hrow
    rcases hrow with eq | later
    · subst w
      obtain ⟨left,right,split⟩ := hfactor
      refine ⟨liftWord left, liftWord right ++ marker start :: blocks (start+1) ws, ?_⟩
      simp [blocks, split, liftWord, List.map_append, List.append_assoc]
    · obtain ⟨left,right,split⟩ := ih (start+1) later
      refine ⟨liftWord w ++ marker start :: left, right, ?_⟩
      simp [blocks, split, List.append_assoc]

theorem liftWord_flatten (w : Word Nat) :
    (liftWord w).flatten = (w.flatten).map Sum.inl := by
  unfold liftWord embed
  exact List.map_flatten.symm

theorem core_row_mem (k L s : Nat) (hs : s<L) :
    (1, core (CombPhases.side 0) s (k-s-1)) ∈ coreRows k L := by
  simp only [coreRows, coreTable, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨s,hs,CombPhases.side 0,?_,rfl⟩
  simp [schedules]

theorem weighted_core_mem (k L s : Nat) (hs : s<L) :
    core (CombPhases.side 0) s (k-s-1) ∈ weightedRows (table k L) := by
  have hm := core_row_mem k L s hs
  have inTable : (1,core (CombPhases.side 0) s (k-s-1)) ∈ table k L := by
    change (1,_) ∈ coreRows k L ++ _
    exact List.mem_append_left _ hm
  generalize ht : table k L = t at inTable ⊢
  clear ht
  induction t with
  | nil => simp at inTable
  | cons row rest ih =>
    simp only [List.mem_cons] at inTable
    rcases inTable with eq | tail
    · subst row
      simp [weightedRows]
    · rcases row with ⟨weight,word⟩
      simp only [weightedRows, List.mem_append]
      exact Or.inr (ih tail)

/-- The same original comb word has literal equal-spelling factors with
different tokenizations, so it is not uniquely decodable. -/
theorem input_not_unique (k L : Nat) (hL : 2 ≤ L) : ¬UniqueDecoding (input k L) := by
  intro unique
  let side := CombPhases.side 0
  let u : Word Nat := [level 0,level 0]
  let v : Word Nat := [level 1]
  have row0 := weighted_core_mem k L 0 (by omega)
  have row1 := weighted_core_mem k L 1 (by omega)
  have hu : Factor (liftWord u) (input k L) := by
    exact lift_factor_blocks u (core side 0 (k-0-1)) _ 0 row0 (core_loop_factor side 0 _)
  have hv : Factor (liftWord v) (input k L) := by
    have loop := core_loop_factor side 1 (k-1-1)
    obtain ⟨a,b,eq⟩ := loop
    have factor : Factor v (core side 1 (k-1-1)) := by
      refine ⟨a,level 1::b,?_⟩
      simpa [v,List.append_assoc] using eq
    exact lift_factor_blocks v (core side 1 (k-1-1)) _ 0 row1 factor
  have same : u.flatten = v.flatten := by
    change level 0 ++ (level 0 ++ []) = level 1 ++ []
    simp only [List.append_nil]
    exact level_double 0
  have eq := unique (liftWord u) (liftWord v) hu hv (by rw [liftWord_flatten,liftWord_flatten,same])
  have lengths := congrArg List.length eq
  simp [liftWord,u,v] at lengths

end
end OriginalSix
