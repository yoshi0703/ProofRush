import DiamondComparator
import Separators
import InitialDomain

/-! Synchronize rowwise partial scripts through the exact unique-marker
serialization `SpellingSeparators.single`. -/
namespace DiamondWitness
open SpellingBPE SpellingDecoy SpellingSeparators Diamond DiamondComparator
noncomputable section

theorem partial_lift {α : Type} [DecidableEq α] {p : Pair α} {w v : Word α}
    (h : Partial p w v) : Partial (liftPair p) (liftWord w) (liftWord v) := by
  induction h with
  | nil => exact .nil
  | keep x _ ih => exact .keep (embed x) ih
  | replace _ ih => simpa [liftWord, liftPair] using Partial.replace ih

theorem play_lift {α : Type} [DecidableEq α] {w v : Word α} {script : List (Pair α)}
    (h : PartialPlay w script v) :
    PartialPlay (liftWord w) (script.map liftPair) (liftWord v) := by
  induction script generalizing w with
  | nil => simp only [PartialPlay, List.map_nil] at h ⊢; subst w; rfl
  | cons p ps ih =>
    obtain ⟨u,hu,rest⟩ := h
    exact ⟨liftWord u, partial_lift hu, ih rest⟩

theorem play_blocks {α : Type} [DecidableEq α] (ws vs : List (Word α))
    (script : List (Pair α)) (start : Nat)
    (h : List.Forall₂ (fun w v => PartialPlay w script v) ws vs) :
    PartialPlay (blocks start ws) (script.map liftPair) (blocks start vs) := by
  induction h generalizing start with
  | nil => exact play_skip [] _
  | @cons w v ws vs one rest ih =>
    change PartialPlay (liftWord w ++ marker start :: blocks (start+1) ws) _
      (liftWord v ++ marker start :: blocks (start+1) vs)
    have tail := play_cat (play_skip [marker (α:=α) start] (script.map liftPair)) (ih (start+1))
    simpa using play_cat (play_lift one) tail

theorem coreTable_map (m : Nat) :
    coreTable m = (rows m).map (fun w => (1,w)) := by
  simp [coreTable,rows,List.map_flatMap,List.map_map, Function.comp_def]

theorem weighted_uniform (ws : List (Word Nat)) :
    weightedRows (ws.map (fun w => (1,w))) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [weightedRows,ih]

theorem forall_rows (m : Nat) :
    List.Forall₂ (fun w v => PartialPlay w (comparator m) v)
      (rows m) ((rows m).map fun _ => [spell (hub m m)]) := by
  have helper (ws : List (Word Nat)) (h : ∀ w ∈ ws, PartialPlay w (comparator m) [spell (hub m m)]) :
      List.Forall₂ (fun w v => PartialPlay w (comparator m) v)
        ws (ws.map fun _ => [spell (hub m m)]) := by
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons]
      exact .cons (h w (by simp)) (ih (fun v hv => h v (by simp [hv])))
  exact helper (rows m) (fun _ h => every_row_runs m h)

/-- Exact marker representation of the m³-row comparator. -/
theorem serialized_core_run (m : Nat) :
    PartialPlay (single (coreTable m)) ((comparator m).map liftPair)
      (blocks 0 ((rows m).map fun _ => [spell (hub m m)])) := by
  rw [single, coreTable_map, weighted_uniform]
  exact play_blocks (rows m) _ (comparator m) 0 (forall_rows m)

theorem weighted_append {α : Type} (a b : Table α) :
    weightedRows (a++b) = weightedRows a ++ weightedRows b := by
  induction a with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨n,w⟩
    simp [weightedRows,ih, List.append_assoc]

theorem blocks_append {α : Type} (a b : List (Word α)) (start : Nat) :
    blocks start (a++b) = blocks start a ++ blocks (start+a.length) b := by
  induction a generalizing start with
  | nil => simp [blocks]
  | cons w ws ih =>
    simp only [List.cons_append, blocks, ih, List.length_cons]
    simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The same rowwise comparator leaves all extra rows (including decoys)
unchanged, with the exact same marker indices as `single`. -/
theorem serialized_augmented_run (m : Nat) (extras : Table Nat) :
    PartialPlay (single (coreTable m ++ extras)) ((comparator m).map liftPair)
      (blocks 0 ((rows m).map fun _ => [spell (hub m m)]) ++
        blocks (rows m).length (weightedRows extras)) := by
  simp only [single, weighted_append, coreTable_map, weighted_uniform, blocks_append, Nat.zero_add]
  have h := serialized_core_run m
  rw [single, coreTable_map, weighted_uniform] at h
  exact play_cat h (play_skip _ _)

theorem blocks_length {α : Type} (ws : List (Word α)) (start : Nat) :
    (blocks start ws).length = ws.flatten.length + ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [blocks, List.length_append, liftWord, List.length_map, List.length_cons,
      List.flatten_cons, ih]
    omega

theorem output_core_length (m : Nat) :
    (((rows m).map fun _ => [spell (hub m m)]).flatten).length = m*m*m := by
  simp [rows_length]

/-- The serialized comparator saves exactly m³(m+1) tokens, including
unchanged extra rows and every unique marker. -/
theorem serialized_exact_saving (m : Nat) (extras : Table Nat) :
    (single (coreTable m ++ extras)).length =
      (blocks 0 ((rows m).map fun _ => [spell (hub m m)]) ++
        blocks (rows m).length (weightedRows extras)).length + m*m*m*(m+1) := by
  simp only [single, weighted_append, coreTable_map, weighted_uniform, blocks_append, Nat.zero_add,
    List.length_append, blocks_length, List.length_map, core_total_length, rows_length,
    output_core_length]
  omega

theorem lift_factor_blocks {α : Type} (u row : Word α) (ws : List (Word α))
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

theorem liftWord_flatten {α : Type} (w : Word α) :
    (liftWord w).flatten = (w.flatten).map Sum.inl := by
  unfold liftWord embed
  exact List.map_flatten.symm

theorem liftWord_injective {α : Type} : Function.Injective (liftWord (α:=α)) := by
  exact List.map_injective_iff.mpr embed_inj

theorem seed_triple_factor (m s x y : Nat) (hs : s<m) :
    Factor [spell (U m s (variant s x y)),spell (hub m s),
      spell (V m s (variant s x y))] (row m s x y) := by
  obtain ⟨left,right,context⟩ := wrap_context m x y (s+1) (m-(s+1))
  refine ⟨left.map spell,right.map spell,?_⟩
  unfold row rowLengths
  have hlen : m-s = (m-(s+1))+1 := by omega
  rw [hlen, wrap_first, context]
  simp

theorem seed_hub_factor (m s x y : Nat) :
    Factor [spell (hub m s)] (row m s x y) := by
  obtain ⟨left,right,context⟩ := wrap_context m x y s (m-s)
  refine ⟨left.map spell,right.map spell,?_⟩
  unfold row rowLengths
  rw [context]
  simp

theorem zero_row_mem (m : Nat) (hm : 0<m) : row m 0 0 0 ∈ rows m := by
  simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨0,hm,0,hm,0,hm,rfl⟩

theorem one_row_mem (m : Nat) (hm : 1<m) : row m 1 0 0 ∈ rows m := by
  simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨1,hm,0,by omega,0,by omega,rfl⟩

/-- The actual serialized augmented input has two different contiguous token
factorizations with identical spelling, witnessed inside two distinct core rows. -/
theorem serialized_not_unique (m : Nat) (hm : 1<m) (extras : Table Nat) :
    ¬ UniqueDecoding (single (coreTable m ++ extras)) := by
  intro unique
  let u : Word Nat := [spell (U m 0 0),spell (hub m 0),spell (V m 0 0)]
  let v : Word Nat := [spell (hub m 1)]
  have hrows0 : row m 0 0 0 ∈ weightedRows (coreTable m ++ extras) := by
    simp [weighted_append, coreTable_map, weighted_uniform, zero_row_mem m (by omega)]
  have hrows1 : row m 1 0 0 ∈ weightedRows (coreTable m ++ extras) := by
    simp [weighted_append, coreTable_map, weighted_uniform, one_row_mem m hm]
  have hu : Factor (liftWord u) (single (coreTable m ++ extras)) := by
    apply lift_factor_blocks u (row m 0 0 0) _ 0 hrows0
    simpa [u, variant] using seed_triple_factor m 0 0 0 (by omega)
  have hv : Factor (liftWord v) (single (coreTable m ++ extras)) := by
    apply lift_factor_blocks v (row m 1 0 0) _ 0 hrows1
    exact seed_hub_factor m 1 0 0
  have same : u.flatten = v.flatten := by
    change spell (U m 0 0) ++ (spell (hub m 0) ++ (spell (V m 0 0) ++ [])) = spell (hub m 1) ++ []
    simp only [List.append_nil]
    rw [← List.append_assoc, spelling_join, Nat.add_comm (U m 0 0) (hub m 0)]
    simpa using completion (m:=m) (j:=0) (i:=0) (by omega) (by omega)
  have equal := unique (liftWord u) (liftWord v) hu hv (by
    rw [liftWord_flatten, liftWord_flatten, same])
  have len := congrArg List.length equal
  simp [liftWord, u, v] at len

theorem blocks_tokens_nonempty {α : Type} (ws : List (Word α))
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

theorem weighted_rows_nonempty (t : Table Nat)
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

theorem serialized_nonempty (m : Nat) (extras : Table Nat)
    (he : ∀ row ∈ extras, ∀ token ∈ row.2, token ≠ []) :
    ∀ token ∈ single (coreTable m ++ extras), token ≠ [] := by
  apply blocks_tokens_nonempty
  apply weighted_rows_nonempty
  intro r hr token ht
  rcases List.mem_append.mp hr with hc | hx
  · exact (DiamondCount.coreTable_token_domain hc ht).1
  · exact he r hx token ht

end
end DiamondWitness
