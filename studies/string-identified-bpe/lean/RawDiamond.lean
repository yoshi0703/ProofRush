import DiamondCount
import InitialDomain
import Forcing
import DiamondFamily

/-! For a token stream with no run of three equal tokens, raw adjacent
counts equal the counts from the full leftmost replacement scan. The
diamond states remain in this class while any private pairs are consumed. -/
namespace RawDiamond

open Diamond DiamondCount DiamondFamily SpellingBPE SpellingDecoy SpellingSeparators

def rawCount {A : Type} [DecidableEq A] (p : Pair A) (w : Word A) : Nat :=
  (candidates w).count p

def TripleFree {A : Type} : Word A → Prop
  | x :: y :: z :: tail => ¬(x=y ∧ y=z) ∧ TripleFree (y::z::tail)
  | _ => True

theorem tripleFree_tail {A : Type} {x : Token A} {w : Word A}
    (free : TripleFree (x::w)) : TripleFree w := by
  cases w with
  | nil => trivial
  | cons a t =>
    cases t with
    | nil => trivial
    | cons b ts => exact free.2

theorem tripleFree_of_nodup {A : Type} {w : Word A} (unique : w.Nodup) : TripleFree w := by
  induction w with
  | nil => trivial
  | cons a rest ih =>
    obtain ⟨notIn, restUnique⟩ := List.nodup_cons.mp unique
    cases rest with
    | nil => trivial
    | cons b tail =>
      cases tail with
      | nil => trivial
      | cons c ts =>
        exact ⟨fun h => notIn (by simp [h.1]), ih restUnique⟩

theorem raw_eq_gain {A : Type} [DecidableEq A] (p : Pair A) (w : Word A)
    (free : TripleFree w) : rawCount p w = gain p w := by
  induction w using List.twoStepInduction with
  | nil => simp [rawCount, candidates, gain, full]
  | singleton x => simp [rawCount, candidates, gain, full]
  | cons_cons x y rest two one =>
    have freeTail := tripleFree_tail free
    by_cases hit : (x,y) = p
    · subst p
      have skip : rawCount (x,y) (y::rest) = rawCount (x,y) rest := by
        cases rest with
        | nil => rfl
        | cons z zs =>
          have diff : (y,z) ≠ (x,y) := by
            intro same
            have a := congrArg Prod.fst same
            have b := congrArg Prod.snd same
            exact free.1 ⟨a.symm,b.symm⟩
          simp [rawCount, candidates, diff]
      have next := two (tripleFree_tail freeTail)
      have shorter := full_nonincrease (x,y) rest
      have front : rawCount (x,y) (x::y::rest) = rawCount (x,y) (y::rest) + 1 := by
        simp only [rawCount, candidates, List.count_cons, beq_self_eq_true, ite_true]
      rw [front, skip, next]
      simp only [gain, full, ite_true, List.length_cons]
      omega
    · have next := one y freeTail
      have front : rawCount p (x::y::rest) = rawCount p (y::rest) := by
        simp [rawCount, candidates, hit]
      rw [front, next]
      simp [gain, full, hit]

theorem tripleFree_map {A C : Type} {f : Token A → Token C} (inj : Function.Injective f)
    {w : Word A} (free : TripleFree w) : TripleFree (w.map f) := by
  induction w using List.twoStepInduction with
  | nil => trivial
  | singleton x => trivial
  | cons_cons x y rest _ ih =>
    have old := ih y (tripleFree_tail free)
    cases rest with
    | nil => trivial
    | cons z zs => exact ⟨fun h => free.1 ⟨inj h.1, inj h.2⟩, old⟩

theorem tripleFree_marker_join {A : Type} (mark : Token A) (body rest : Word A)
    (bodyFree : TripleFree body) (restFree : TripleFree rest)
    (before : mark ∉ body) (after : mark ∉ rest) : TripleFree (body ++ mark::rest) := by
  have markerRest : TripleFree (mark::rest) := by
    cases rest with
    | nil => trivial
    | cons x xs =>
      cases xs with
      | nil => trivial
      | cons y ys =>
        refine ⟨fun h => after (h.1.symm ▸ List.mem_cons_self ..), restFree⟩
  induction body using List.twoStepInduction with
  | nil => exact markerRest
  | singleton x =>
    cases rest with
    | nil => trivial
    | cons y ys =>
      refine ⟨fun h => before (List.mem_singleton.mpr h.1.symm), markerRest⟩
  | cons_cons x y tail _ next =>
    have suffix : TripleFree ((y::tail) ++ mark::rest) :=
      next y (tripleFree_tail bodyFree) (fun h => before (List.mem_cons_of_mem _ h))
    cases tail with
    | nil =>
      refine ⟨fun h => before (List.mem_cons_of_mem _ (List.mem_singleton.mpr h.2.symm)), suffix⟩
    | cons z zs => exact ⟨bodyFree.1,suffix⟩

theorem tripleFree_blocks {A : Type} (ws : List (Word A)) (start : Nat)
    (free : ∀ w ∈ ws, TripleFree w) : TripleFree (blocks start ws) := by
  induction ws generalizing start with
  | nil => trivial
  | cons head tail ih =>
    change TripleFree (liftWord head ++ marker start :: blocks (start+1) tail)
    apply tripleFree_marker_join
    · exact tripleFree_map embed_inj (free head (by simp))
    · exact ih (start+1) (fun w hw => free w (List.mem_cons_of_mem _ hw))
    · intro h
      obtain ⟨t,_,eq⟩ := List.mem_map.mp h
      exact embed_mark t start eq
    · exact marker_absent tail (Nat.lt_succ_self start)

theorem tripleFree_single {A : Type} (table : Table A)
    (free : ∀ r ∈ table, TripleFree r.2) : TripleFree (single table) := by
  have each (w : Word A) (listed : w ∈ weightedRows table) : TripleFree w := by
    induction table with
    | nil => simp [weightedRows] at listed
    | cons r tail ih =>
      rcases r with ⟨n,row⟩
      simp only [weightedRows, List.mem_append] at listed
      rcases listed with copy | later
      · exact ((List.mem_replicate.mp copy).2).symm ▸ free (n,row) (by simp)
      · exact ih (fun r hr => free r (List.mem_cons_of_mem _ hr)) later
  exact tripleFree_blocks (weightedRows table) 0 each

theorem coreTable_tripleFree (m : Nat) : ∀ r ∈ coreTable m, TripleFree r.2 := by
  intro r listed
  simp only [coreTable,List.mem_flatMap,List.mem_map,List.mem_range] at listed
  obtain ⟨s,hs,x,hx,y,hy,rfl⟩ := listed
  exact tripleFree_of_nodup (stage_nodup hx hy (by omega : s+(m-s)≤m))

theorem augmented_single_tripleFree {A : Type} [DecidableEq A]
    (core : Table A) (m : Nat) (ps spent : List (Pair A))
    (free : ∀ r ∈ core, TripleFree r.2) :
    TripleFree (single (augmented core m ps spent)) := by
  apply tripleFree_single
  intro r listed
  rcases List.mem_append.mp listed with inside | bonus
  · exact free r inside
  · obtain ⟨q,_,rfl⟩ := List.mem_map.mp bonus
    by_cases mem : q ∈ spent <;> simp [extra, mem, TripleFree]

def RawMaximal {A : Type} [DecidableEq A] (w : Word A) (p : Pair A) : Prop :=
  0 < rawCount p w ∧ ∀ q : Pair A, rawCount q w ≤ rawCount p w

theorem rawMaximal_iff_maximal {A : Type} [DecidableEq A]
    {w : Word A} {p : Pair A} (free : TripleFree w) : RawMaximal w p ↔ SpellingBPE.Maximal w p := by
  simp only [RawMaximal, SpellingBPE.Maximal, raw_eq_gain _ _ free]

theorem rawMaximal_iff_forced_state (m : Nat) (ps spent : List (Pair Nat)) (q : Pair (Nat ⊕ Nat)) :
    RawMaximal (single (augmented (coreTable m) (m+1) ps spent)) q ↔
      SpellingBPE.Maximal (single (augmented (coreTable m) (m+1) ps spent)) q :=
  rawMaximal_iff_maximal (augmented_single_tripleFree _ _ _ _ (coreTable_tripleFree m))

def rawValue {A : Type} [DecidableEq A] (table : Table A) (p : Pair A) : Nat :=
  (table.map fun r => r.1 * rawCount p r.2).sum

theorem coreTable_raw_le (m : Nat) (q : Pair Nat) : rawValue (coreTable m) q ≤ m := by
  have scores : rawValue (coreTable m) q = value (coreTable m) q := by
    unfold rawValue value
    congr 1
    exact List.map_congr_left (fun r hr => by rw [raw_eq_gain _ _ (coreTable_tripleFree m r hr)])
  rw [scores]
  exact value_coreTable_le m q

theorem private_core_absent (m j : Nat) {r : Nat × Word Nat} (hr : r ∈ coreTable m) :
    privatePair j ∉ candidates r.2 := by
  intro present
  have left : [j+1] ∈ r.2 := candidate_first_mem present
  have impossible := (coreTable_token_domain hr left).2 (j+1) (by simp)
  omega

theorem private_isolated (m k : Nat) :
    ∀ p ∈ privatePairs k, ∀ r ∈ coreTable m, p ∉ candidates r.2 := by
  intro p hp r hr
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
  exact private_core_absent m j hr

inductive RawGreedy {A : Type} [DecidableEq A] : Nat → Word A → Word A → Prop
  | nil (w) : RawGreedy 0 w w
  | cons {k w v p} : RawMaximal w p → RawGreedy k (full p w) v → RawGreedy (k+1) w v

def forcedState (m k : Nat) (used : List (Pair Nat)) : Word (Nat ⊕ Nat) :=
  single (augmented (coreTable m) (m+1) (privatePairs k) used)

theorem state_initial (m k : Nat) : forcedState m k [] = input m k := rfl

theorem greedy_step_private (m k : Nat) (positive : 1 ≤ m) (used : List (Pair Nat))
    (room : used.length < k) {p : Pair (Nat ⊕ Nat)}
    (max : SpellingBPE.Maximal (forcedState m k used) p) :
    ∃ rule ∈ privatePairs k, rule ∉ used ∧ p = liftPair rule ∧
      full p (forcedState m k used) = forcedState m k (rule::used) := by
  unfold forcedState at max ⊢
  obtain ⟨fresh, present, freshUnused⟩ := has_unused (private_nodup k)
    (by simpa [private_length] using room)
  have gainFresh := SingleForcing.fresh_score (coreTable m) (m+1) (privatePairs k) used
    (private_nodup k) (private_isolated m k) ⟨present, freshUnused⟩
  have lower := max.2 (liftPair fresh)
  rw [gainFresh] at lower
  obtain ⟨rule, rfl⟩ := high_is_lift
    (augmented (coreTable m) (m+1) (privatePairs k) used) p
    ((by omega : 1 < m+1).trans_le lower)
  have chosen : rule ∈ privatePairs k ∧ rule ∉ used := by
    by_contra absent
    rw [gain_single, SingleForcing.score _ _ _ _ (private_nodup k), ite_eq_right absent,
      Nat.add_zero] at lower
    have upper := value_coreTable_le m rule
    omega
  refine ⟨rule, chosen.1, chosen.2, rfl, ?_⟩
  rw [full_single, step_augmented _ _ _ _ _ (private_isolated m k rule chosen.1)]

/-- Run-level equivalence on the same physical stream, with the same
leftmost replacements and all tie choices allowed in both rankings. -/
theorem rawGreedy_iff_greedy_state (m k steps : Nat) (positive : 1 ≤ m)
    (used : List (Pair Nat)) (room : used.length+steps ≤ k) (v : Word (Nat ⊕ Nat)) :
    RawGreedy steps (forcedState m k used) v ↔ Greedy steps (forcedState m k used) v := by
  induction steps generalizing used v with
  | zero =>
    constructor
    · intro run; cases run; exact .nil _
    · intro run; cases run; exact .nil _
  | succ n ih =>
    have available : used.length < k := by omega
    constructor
    · intro run
      cases run with
      | @cons _ _ _ q isRaw tail =>
        have max := (rawMaximal_iff_forced_state m (privatePairs k) used q).mp isRaw
        obtain ⟨rule, _, _, _, state⟩ := greedy_step_private m k positive used available max
        refine .cons max ?_
        rw [state] at tail ⊢
        exact (ih (rule::used) (by simp only [List.length_cons]; omega) v).mp tail
    · intro run
      cases run with
      | @cons _ _ _ q max tail =>
        have isRaw := (rawMaximal_iff_forced_state m (privatePairs k) used q).mpr max
        obtain ⟨rule, _, _, _, state⟩ := greedy_step_private m k positive used available max
        refine .cons isRaw ?_
        rw [state] at tail ⊢
        exact (ih (rule::used) (by simp only [List.length_cons]; omega) v).mpr tail

theorem rawGreedy_iff_greedy_input (m k : Nat) (positive : 1 ≤ m) (v : Word (Nat ⊕ Nat)) :
    RawGreedy k (input m k) v ↔ Greedy k (input m k) v := by
  simpa only [state_initial] using rawGreedy_iff_greedy_state m k k positive [] (by simp) v

theorem rawGreedy_exists (m k : Nat) (positive : 1 ≤ m) :
    ∃ v, RawGreedy k (input m k) v := by
  obtain ⟨v, run⟩ := SingleForcing.greedy_exists (coreTable m) (m+1) (by omega)
    (privatePairs k) (private_nodup k) (fun q => Nat.lt_succ_of_le (value_coreTable_le m q))
    (private_isolated m k) k [] (by simp [private_length])
  exact ⟨v, (rawGreedy_iff_greedy_input m k positive v).mpr run⟩

theorem rawGreedy_all_ties (m k : Nat) (positive : 1 ≤ m) (v : Word (Nat ⊕ Nat))
    (run : RawGreedy k (input m k) v) : (input m k).length - v.length = k*(m+1) :=
  SingleForcing.all_greedy (coreTable m) (m+1) (by omega) (privatePairs k) (private_nodup k)
    (fun q => Nat.lt_succ_of_le (value_coreTable_le m q)) (private_isolated m k)
    k [] (by simp [private_length]) v ((rawGreedy_iff_greedy_input m k positive v).mp run)

#print axioms coreTable_raw_le
#print axioms rawMaximal_iff_forced_state
#print axioms private_core_absent
#print axioms rawGreedy_iff_greedy_input
#print axioms rawGreedy_exists
#print axioms rawGreedy_all_ties

end RawDiamond
