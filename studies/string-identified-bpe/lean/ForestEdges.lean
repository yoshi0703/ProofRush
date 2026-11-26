import ForestPaths
import ForestMass

/-! Independent boundary accounting. Every internal node divides its original
    leaf interval in two. Its boundary is a distinct original adjacency, so
    any selected collection of such boundaries is bounded by the mass of
    original adjacencies bearing labels in the chosen set. -/
namespace BPEForest
open MergeTree SpellingBPE SpellingMatching
variable {α : Type} [DecidableEq α]

def selectedBoundaries (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) : MergeTree α → Nat
  | .leaf _ => 0
  | .node i l r => selectedBoundaries labels select l + selectedBoundaries labels select r +
      (if select i l r then jointMass labels l.leaves r.leaves else 0)

theorem selectedBoundaries_le_mass (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) (t : MergeTree α) :
    selectedBoundaries labels select t ≤ mass labels t.leaves := by
  induction t with
  | leaf a => simp [selectedBoundaries, leaves, mass_cons, boundary]
  | node i l r ihl ihr =>
    rw [selectedBoundaries, leaves, mass_append]
    split <;> omega

theorem forest_selectedBoundaries_le_mass (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) (trees : List (MergeTree α)) :
    (trees.map (selectedBoundaries labels select)).sum ≤ mass labels (trees.flatMap leaves) := by
  induction trees with
  | nil => simp
  | cons t trees ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons]
    exact (Nat.add_le_add (selectedBoundaries_le_mass labels select t) ih).trans
      (sum_mass_le_append labels _ _)

/-- Number of selected nodes, independent of the label set. -/
def selectedCount (select : Nat → MergeTree α → MergeTree α → Bool) : MergeTree α → Nat
  | .leaf _ => 0
  | .node i l r => selectedCount select l + selectedCount select r +
      (if select i l r then 1 else 0)

def SelectedGood (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) : MergeTree α → Prop
  | .leaf _ => True
  | .node i l r => (select i l r = true → jointMass labels l.leaves r.leaves = 1) ∧
      SelectedGood labels select l ∧ SelectedGood labels select r

theorem selectedCount_eq_boundaries (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) (t : MergeTree α)
    (good : SelectedGood labels select t) :
    selectedCount select t = selectedBoundaries labels select t := by
  induction t with
  | leaf _ => rfl
  | node i l r ihl ihr =>
    obtain ⟨here, hl, hr⟩ := good
    simp only [selectedCount, selectedBoundaries, ihl hl, ihr hr]
    split <;> simp_all

theorem forest_selectedCount_le_mass (labels : Finset (Pair α))
    (select : Nat → MergeTree α → MergeTree α → Bool) (trees : List (MergeTree α))
    (good : ∀ t ∈ trees, SelectedGood labels select t) :
    (trees.map (selectedCount select)).sum ≤ mass labels (trees.flatMap leaves) := by
  have eq : trees.map (selectedCount select) = trees.map (selectedBoundaries labels select) := by
    apply List.map_congr_left
    intro t ht
    exact selectedCount_eq_boundaries labels select t (good t ht)
  rw [eq]
  exact forest_selectedBoundaries_le_mass labels select trees

end BPEForest

namespace BPEForest
open MergeTree

def firstSide (side : Bool) (xs : Chain α) : Option (Attachment α) :=
  xs.find? (fun a => a.1 == side)

theorem leaves_nonempty (t : MergeTree α) : t.leaves ≠ [] := by
  induction t with
  | leaf a => simp [leaves]
  | node n l r ihl ihr => simp [leaves, ihl]

theorem first_left_endpoint (t : MergeTree α) (a : Attachment α)
    (h : firstSide false (extract t).1 = some a) : t.leaves.head? = some a.2.2 := by
  induction t with
  | leaf x => simp [firstSide, extract] at h
  | node n l r ihl ihr =>
    cases l with
    | leaf x =>
      cases r with
      | leaf y => simp [firstSide, extract] at h
      | node j p q =>
        simp [firstSide, extract, extend] at h
        subst a
        simp [leaves]
    | node j p q =>
      cases r with
      | leaf x =>
        have hh : firstSide false (extract (.node j p q)).1 = some a := by
          simpa [firstSide, extract, extend] using h
        have hhead := ihl hh
        simpa [leaves, List.head?_append_of_ne_nil _ (leaves_nonempty _)] using hhead
      | node i x y => simp [firstSide, extract] at h

theorem first_right_endpoint (t : MergeTree α) (a : Attachment α)
    (h : firstSide true (extract t).1 = some a) : t.leaves.getLast? = some a.2.2 := by
  induction t with
  | leaf x => simp [firstSide, extract] at h
  | node n l r ihl ihr =>
    cases l with
    | leaf x =>
      cases r with
      | leaf y => simp [firstSide, extract] at h
      | node j p q =>
        have hh : firstSide true (extract (.node j p q)).1 = some a := by
          simpa [firstSide, extract, extend] using h
        have hlast := ihr hh
        change ([x] ++ (MergeTree.node j p q).leaves).getLast? = some a.2.2
        rw [List.getLast?_append_of_ne_nil _ (leaves_nonempty _)]
        exact hlast
    | node j p q =>
      cases r with
      | leaf x =>
        simp [firstSide, extract, extend] at h
        subst a
        simp [leaves]
      | node i x y => simp [firstSide, extract] at h

theorem jointMass_of_endpoints {α : Type} [DecidableEq α]
    (labels : Finset (SpellingBPE.Pair α)) (u v : SpellingBPE.Word α)
    (a b : List α) (last : u.getLast? = some a) (first : v.head? = some b)
    (mem : (a,b) ∈ labels) : SpellingMatching.jointMass labels u v = 1 := by
  cases v with
  | nil => simp at first
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at first
    subst x
    simp [SpellingMatching.jointMass, SpellingMatching.boundary, last, mem]

end BPEForest
