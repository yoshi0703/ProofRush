import ForestEdges
import ForestChronology

/-! Selected short-gap edges are original adjacent pairs in shortLabels. -/
namespace BPEForest
open MergeTree SpellingBPE SpellingMatching
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem firstSide_valid {rules : List (Pair α)} {bound : Nat} {t : MergeTree α}
    (valid : t.Valid rules bound) (side : Bool) {a : Attachment α}
    (h : firstSide side (extract t).1 = some a) :
    a.1 = side ∧ a.2.1 < bound ∧ a.2.2 = operand rules side a.2.1 := by
  have hm : a ∈ (extract t).1 := List.mem_of_find?_eq_some h
  have hp : (a.1 == side) = true := by
    exact List.find?_some (p := fun q : Attachment α => q.1 == side) h
  have hs : a.1 = side := by simpa using hp
  have ne : (extract t).1 ≠ [] := List.ne_nil_of_mem hm
  have hc : (extract t).1 ∈ close (extract t) := by
    simp [close, List.isEmpty_iff, ne]
  have hv := (extracted_valid valid hc).2 a hm
  exact ⟨hs,hv.1,by simpa [hs] using hv.2⟩

theorem left_short_boundary (rules : List (Pair α)) (s i : Nat) (a : List α)
    (t : MergeTree α) (hi : i < rules.length) (valid : t.Valid rules i)
    (lookup : rules[i]? = some (a,t.spell))
    (chosen : shortAhead s false i (extract t).1 = true) :
    jointMass (shortLabels rules s) [a] t.leaves = 1 := by
  simp only [shortAhead,sameSide,List.head?_filter] at chosen
  change (match firstSide _ (extract t).1 with
    | none => false | some z => decide (i-z.2.1 ≤ s)) = true at chosen
  cases hs : firstSide false (extract t).1 with
  | none => simp [hs] at chosen
  | some older =>
    have info := firstSide_valid valid false hs
    have endpoint := first_left_endpoint t older hs
    have gap : i-older.2.1 ≤ s := by
      simpa [hs] using chosen
    have newer : a = operand rules false i := by simp [operand,lookup]
    have mem := short_pair_mem rules s false hi info.2.1 gap
    have mem' : (a,older.2.2) ∈ shortLabels rules s := by
      simpa [orderedPair, ← newer, ← info.2.2] using mem
    exact jointMass_of_endpoints _ _ _ a older.2.2 rfl endpoint mem'

theorem right_short_boundary (rules : List (Pair α)) (s i : Nat) (a : List α)
    (t : MergeTree α) (hi : i < rules.length) (valid : t.Valid rules i)
    (lookup : rules[i]? = some (t.spell,a))
    (chosen : shortAhead s true i (extract t).1 = true) :
    jointMass (shortLabels rules s) t.leaves [a] = 1 := by
  simp only [shortAhead,sameSide,List.head?_filter] at chosen
  change (match firstSide _ (extract t).1 with
    | none => false | some z => decide (i-z.2.1 ≤ s)) = true at chosen
  cases hs : firstSide true (extract t).1 with
  | none => simp [hs] at chosen
  | some older =>
    have info := firstSide_valid valid true hs
    have endpoint := first_right_endpoint t older hs
    have gap : i-older.2.1 ≤ s := by
      simpa [hs] using chosen
    have newer : a = operand rules true i := by simp [operand,lookup]
    have mem := short_pair_mem rules s true hi info.2.1 gap
    have mem' : (older.2.2,a) ∈ shortLabels rules s := by
      simpa [orderedPair, ← newer, ← info.2.2] using mem
    exact jointMass_of_endpoints _ _ _ older.2.2 a endpoint rfl mem'

theorem short_selected_good (rules : List (Pair α)) (s : Nat) (t : MergeTree α)
    {bound : Nat} (hb : bound ≤ rules.length) (valid : t.Valid rules bound) :
    SelectedGood (shortLabels rules s) (shortAt s) t := by
  induction t generalizing bound with
  | leaf a => trivial
  | node i l r ihl ihr =>
    obtain ⟨hi,lookup,vl,vr⟩ := valid
    have hlen : i < rules.length := hi.trans_le hb
    refine ⟨?_, ihl hlen.le vl, ihr hlen.le vr⟩
    intro selected
    cases l with
    | leaf a =>
      cases r with
      | leaf b => simp [shortAt] at selected
      | node j x y =>
        change jointMass (shortLabels rules s) [a] (MergeTree.node j x y).leaves = 1
        exact left_short_boundary rules s i a _ hlen vr (by simpa [spell] using lookup) selected
    | node j x y =>
      cases r with
      | leaf a =>
        change jointMass (shortLabels rules s) (MergeTree.node j x y).leaves [a] = 1
        exact right_short_boundary rules s i a _ hlen vl (by simpa [spell] using lookup) selected
      | node u x y => simp [shortAt] at selected

theorem forest_short_count_le_mass (rules : List (Pair α)) (s : Nat)
    (trees : List (MergeTree α))
    (valid : ∀ t∈trees, t.Valid rules rules.length) :
    (trees.map (selectedCount (shortAt s))).sum ≤
      mass (shortLabels rules s) (trees.flatMap leaves) := by
  apply forest_selectedCount_le_mass
  intro t ht
  exact short_selected_good rules s t (Nat.le_refl _) (valid t ht)

end BPEForest

#print axioms BPEForest.forest_short_count_le_mass
