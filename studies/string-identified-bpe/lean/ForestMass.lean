import Matching
import ForestTypes
import Mathlib.Data.Finset.Card

/-! Counting allowed adjacent-pair labels across concatenated words and
charging each comparator cherry to a distinct adjacency in its leaves. -/

namespace SpellingMatching

open SpellingBPE

variable {α : Type} [DecidableEq α]

/-- The only adjacent pair crossing the boundary between two words. -/
def jointMass (labels : Finset (Pair α)) (u v : Word α) : ℕ :=
  match u.getLast? with
  | none => 0
  | some x => boundary labels x v

theorem mass_append (labels : Finset (Pair α)) (u v : Word α) :
    mass labels (u ++ v) = mass labels u + mass labels v + jointMass labels u v := by
  induction u with
  | nil => simp [jointMass]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp [jointMass, mass_cons, boundary]
    | cons y ys =>
      rw [List.cons_append, mass_cons labels x, ih, mass_cons labels x (y :: ys)]
      simp only [jointMass, List.getLast?_cons_cons, List.cons_append, boundary]
      omega

theorem sum_mass_le_append (labels : Finset (Pair α)) (u v : Word α) :
    mass labels u + mass labels v ≤ mass labels (u ++ v) := by
  rw [mass_append]
  exact Nat.le_add_right ..

theorem mass_mono {labels larger : Finset (Pair α)} (subset : labels ⊆ larger) (w : Word α) :
    mass labels w ≤ mass larger w := by
  induction w using List.twoStepInduction with
  | nil => simp
  | singleton x => simp [mass_cons, boundary]
  | cons_cons x y w _ ih =>
    rw [mass_cons labels x, mass_cons larger x]
    refine Nat.add_le_add (ih y) ?_
    by_cases h : (x, y) ∈ labels
    · simp [boundary, h, subset h]
    · simp [boundary, h]

theorem sum_mass_le_flatMap {β : Type} (labels : Finset (Pair α)) (f : β → Word α) (xs : List β) :
    (xs.map fun x => mass labels (f x)).sum ≤ mass labels (xs.flatMap f) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact (Nat.add_le_add_left ih _).trans (sum_mass_le_append labels (f x) (xs.flatMap f))

end SpellingMatching

namespace BPEForest

open SpellingBPE SpellingMatching

variable {α : Type} [DecidableEq α]

namespace MergeTree

private theorem cherry_border (rules : List (Pair α)) (i : ℕ) (l r : MergeTree α)
    (look : rules[i]? = some (l.spell, r.spell)) :
    (if l.isLeaf && r.isLeaf then 1 else 0) ≤ jointMass rules.toFinset l.leaves r.leaves := by
  cases l with
  | node stage l r => simp [isLeaf]
  | leaf a =>
    cases r with
    | node stage l r => simp [isLeaf]
    | leaf b =>
      have hmem : (a,b) ∈ rules := List.mem_of_getElem? (by simpa only [spell] using look)
      simp [jointMass, boundary, leaves, isLeaf, hmem]

/-- Every comparator cherry contributes one distinct adjacency on the
original leaves, and its label is one of the comparator rules. -/
theorem cherries_le_mass (rules : List (Pair α)) (t : MergeTree α) {bound : ℕ}
    (valid : t.Valid rules bound) : t.cherries ≤ mass rules.toFinset t.leaves := by
  induction t generalizing bound with
  | leaf a => simp [cherries, leaves, mass_cons, boundary]
  | node i l r left right =>
    obtain ⟨_, look, validL, validR⟩ := valid
    have c := cherry_border rules i l r look
    have hl := left validL
    have hr := right validR
    rw [cherries, leaves, mass_append]
    omega

end MergeTree

theorem forest_cherries_le_mass (rules : List (Pair α)) (trees : List (MergeTree α)) {bound : ℕ}
    (valid : ∀ t ∈ trees, t.Valid rules bound) :
    (trees.map MergeTree.cherries).sum ≤ mass rules.toFinset (trees.flatMap MergeTree.leaves) := by
  induction trees with
  | nil => simp
  | cons t trees ih =>
    have head := t.cherries_le_mass rules (valid t (by simp))
    have tail := ih fun u hu => valid u (by simp [hu])
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact (Nat.add_le_add head tail).trans (sum_mass_le_append _ _ _)

theorem cherry_labels_card_le (rules : List (Pair α)) : rules.toFinset.card ≤ rules.length :=
  List.toFinset_card_le rules

end BPEForest

#print axioms SpellingMatching.mass_append
#print axioms BPEForest.forest_cherries_le_mass
