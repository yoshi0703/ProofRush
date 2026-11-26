import SpellingBPE

/-! Recovering short current pair types from their original atom subwords. -/
namespace BoundedInitial

open SpellingBPE
variable {α β : Type} [DecidableEq α]

/-- The one- or two-token groups chosen by the actual left-to-right scan. -/
def groups (label : β → Token α) (p : Pair α) : List β → List (List β)
  | [] => []
  | [x] => [[x]]
  | x::y::t => if (label x,label y) = p then [x,y] :: groups label p t else [x] :: groups label p (y::t)

theorem groups_flatten (label : β → Token α) (p : Pair α) (w : List β) : (groups label p w).flatten = w := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y t h ih => by_cases hit : (label x,label y) = p <;> simp [groups,hit,h,ih]

theorem groups_map (label : β → Token α) (p : Pair α) (w : List β) :
    (groups label p w).map (fun g => (g.map label).flatten) = full p (w.map label) := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton x => simp [groups,full]
  | cons_cons x y t h ih => by_cases hit : (label x,label y) = p <;> simp [groups,full,hit,h,ih]

theorem groups_nonempty (label : β → Token α) (p : Pair α) (w : List β) :
    ∀ g ∈ groups label p w, g ≠ [] := by
  induction w using List.twoStepInduction with
  | nil => simp [groups]
  | singleton x => simp [groups]
  | cons_cons x y t h ih =>
    by_cases hit : (label x,label y) = p
    · simpa [groups, hit] using h
    · simpa [groups, hit] using ih y

theorem groups_split (label : β → Token α) (p : Pair α) (w : List β) (a b : List (List β))
    (split : groups label p w = a ++ b) :
    groups label p a.flatten = a ∧ groups label p b.flatten = b := by
  induction w using List.twoStepInduction generalizing a b with
  | nil =>
    have both : a = [] ∧ b = [] := List.append_eq_nil_iff.mp split.symm
    obtain ⟨rfl,rfl⟩ := both
    simp [groups]
  | singleton x =>
    cases a with
    | nil => obtain rfl : b = [[x]] := split.symm; simp [groups]
    | cons z a =>
      have h : [x] = z ∧ [] = a ++ b := List.cons.inj split
      obtain ⟨rfl,tail⟩ := h
      obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp tail.symm
      simp [groups]
  | cons_cons x y t h ih =>
    cases a with
    | nil =>
      have hb : b = groups label p (x::y::t) := split.symm
      rw [hb,groups_flatten]
      exact ⟨rfl,rfl⟩
    | cons hd a =>
      by_cases hit : (label x,label y) = p
      · have equality : [x,y] :: groups label p t = hd :: (a ++ b) := by
          simpa only [groups,hit,ite_true,List.cons_append] using split
        obtain ⟨rfl,tail⟩ := List.cons.inj equality
        obtain ⟨prefixEq,suffixEq⟩ := h a b tail
        simp [groups,hit,prefixEq,suffixEq]
      · have equality : [x] :: groups label p (y::t) = hd :: (a ++ b) := by
          simpa only [groups,hit,ite_false,List.cons_append] using split
        obtain ⟨rfl,tail⟩ := List.cons.inj equality
        obtain ⟨prefixEq,suffixEq⟩ := ih y a b tail
        refine ⟨?_,suffixEq⟩
        change groups label p (x :: a.flatten) = [x] :: a
        cases a with
        | nil => rfl
        | cons first rest =>
          have firstMem : first ∈ groups label p (y::t) := by simp [tail]
          have firstNonempty := groups_nonempty label p (y::t) first firstMem
          obtain ⟨head,more,rfl⟩ := List.exists_cons_of_ne_nil firstNonempty
          have flatter := congrArg List.flatten tail
          rw [groups_flatten,List.flatten_append] at flatter
          have headEq : y = head := (List.cons.inj flatter).1
          subst head
          change groups label p (x::y::(more ++ rest.flatten)) = _
          rw [groups,ite_eq_right hit]
          exact congrArg (List.cons [x]) prefixEq

/-- If a prefix, middle and suffix are unions of complete groups of the global
full scan, restricting to the middle gives exactly the standalone scan. -/
theorem groups_isolate (label : β → Token α) (p : Pair α) (w : List β) (a mid b : List (List β))
    (split : groups label p w = a ++ mid ++ b) :
    groups label p mid.flatten = mid := by
  rw [List.append_assoc] at split
  have last := (groups_split label p w a (mid++b) split).2
  exact (groups_split label p (mid++b).flatten mid b last).1

#print axioms groups_isolate

abbrev Blocks (α : Type) := List (Word α)

def initialBlocks (w : Word α) : Blocks α := w.map fun a => [a]

def traceStep (p : Pair α) (blocks : Blocks α) : Blocks α :=
  (groups List.flatten p blocks).map List.flatten

theorem traceStep_visible (p : Pair α) (blocks : Blocks α) :
    (traceStep p blocks).map List.flatten = full p (blocks.map List.flatten) := by
  unfold traceStep
  rw [List.map_map]
  simpa only [Function.comp_def, List.flatten_flatten] using
    groups_map (label := (List.flatten : Word α → Token α)) p blocks

theorem traceStep_factor (p : Pair α) (blocks l mid r : Blocks α)
    (factor : traceStep p blocks = l ++ mid ++ r) :
    ∃ L W R : Blocks α, blocks = L ++ W ++ R ∧ W.flatten = mid.flatten ∧ traceStep p W = mid := by
  rw [List.append_assoc] at factor
  unfold traceStep at factor
  obtain ⟨a, tail, parts, _, rest⟩ := List.map_eq_append_iff.mp factor
  obtain ⟨b, c, tailParts, middle, _⟩ := List.map_eq_append_iff.mp rest
  have split : groups List.flatten p blocks = a ++ b ++ c := by
    rw [parts, tailParts, List.append_assoc]
  refine ⟨a.flatten,b.flatten,c.flatten,?_,?_,?_⟩
  · have flat := congrArg List.flatten split
    simpa only [groups_flatten,List.flatten_append] using flat
  · rw [← middle, List.flatten_flatten]
  · rw [traceStep, groups_isolate _ _ _ _ _ _ split]
    exact middle

def traceRun (rules : List (Pair α)) (w : Word α) : Blocks α :=
  rules.foldl (fun blocks p => traceStep p blocks) (initialBlocks w)

theorem traceRun_visible (rules : List (Pair α)) (w : Word α) :
    (traceRun rules w).map List.flatten = play w rules := by
  have loop (ps : List (Pair α)) (bs : Blocks α) :
      (ps.foldl (fun blocks p => traceStep p blocks) bs).map List.flatten =
        play (bs.map List.flatten) ps := by
    induction ps generalizing bs with
    | nil => rfl
    | cons p tail ih =>
      simp only [List.foldl_cons, play, ih, traceStep_visible]
  rw [traceRun, loop]
  simp [initialBlocks,Function.comp_def]

omit [DecidableEq α] in
theorem restore_initial (w : Word α) (mid : Blocks α)
    (subset : ∀ b ∈ mid, b ∈ initialBlocks w) :
    initialBlocks mid.flatten = mid := by
  induction mid with
  | nil => rfl
  | cons b bs ih =>
    have Hb : b ∈ initialBlocks w := subset _ (by simp)
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp Hb
    simpa only [initialBlocks, List.flatten_cons, List.singleton_append, List.map_cons] using
      congrArg (List.cons [x]) (ih (fun c hc => subset c (List.mem_cons_of_mem _ hc)))

/-- Any surviving adjacent-block interval can be replayed starting from its
actual original initial atom subword. No uniqueness of literal atomization
is assumed. -/
theorem traceRun_factor (rules : List (Pair α)) (w : Word α) (l mid r : Blocks α)
    (factor : traceRun rules w = l ++ mid ++ r) : traceRun rules mid.flatten = mid := by
  induction rules using List.reverseRecOn generalizing l mid r with
  | nil =>
    change initialBlocks w = l ++ mid ++ r at factor
    apply restore_initial w mid
    intro b hb
    rw [factor, List.mem_append]
    exact Or.inl (List.mem_append_right _ hb)
  | append_singleton ps p ih =>
    have lastStep (v : Word α) : traceRun (ps ++ [p]) v = traceStep p (traceRun ps v) := by
      simp [traceRun,List.foldl_append]
    rw [lastStep] at factor ⊢
    obtain ⟨L,W,R,earlier,flat,step⟩ := traceStep_factor p (traceRun ps w) l mid r factor
    rw [← flat, ih L W R earlier, step]

theorem pair_replay (rules : List (Pair α)) (w : Word α)
    (l r : Blocks α) (left right : Word α)
    (factor : traceRun rules w = l ++ [left,right] ++ r) :
    play (left ++ right) rules = [left.flatten,right.flatten] := by
  have found := traceRun_factor rules w l [left,right] r factor
  simpa [traceRun_visible] using congrArg (List.map List.flatten) found

#print axioms traceRun_factor
#print axioms pair_replay

end BoundedInitial
