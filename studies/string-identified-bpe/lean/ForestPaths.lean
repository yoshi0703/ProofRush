import ForestCounts

/-! Executable extraction of maximal unary-node chains. The first component is
    the open chain containing the current root; the second contains closed
    chains. Each annotation is (side, stage, original leaf spelling). -/
namespace BPEForest

abbrev Attachment (α : Type) := Bool × Nat × List α
abbrev Chain (α : Type) := List (Attachment α)
abbrev Extraction (α : Type) := Chain α × List (Chain α)

def close {α : Type} (x : Extraction α) : List (Chain α) :=
  if x.1.isEmpty then x.2 else x.1 :: x.2

def extend {α : Type} (a : Attachment α) (x : Extraction α) : Extraction α :=
  (a :: x.1, x.2)

open MergeTree

def extract : MergeTree α → Extraction α
  | .leaf _ => ([], [])
  | .node t l r =>
    match l, r with
    | .leaf _, .leaf _ => ([], [])
    | .leaf a, .node u x y => extend (false, t, a) (extract (.node u x y))
    | .node u x y, .leaf a => extend (true, t, a) (extract (.node u x y))
    | .node u x y, .node v z w =>
        ([], close (extract (.node u x y)) ++ close (extract (.node v z w)))

def attachmentCount (x : Extraction α) : Nat :=
  x.1.length + (x.2.map List.length).sum

theorem attachmentCount_extend (a : Attachment α) (x : Extraction α) :
    attachmentCount (extend a x) = attachmentCount x + 1 := by
  simp [attachmentCount, extend, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem attachmentCount_close (x : Extraction α) :
    ((close x).map List.length).sum = attachmentCount x := by
  rcases x with ⟨xs, rest⟩
  cases xs <;> simp [close, attachmentCount]

theorem extract_counts_unary (t : MergeTree α) :
    attachmentCount (extract t) = t.unary := by
  induction t with
  | leaf a => rfl
  | node n l r ihl ihr =>
    cases l with
    | leaf a =>
      cases r with
      | leaf b => rfl
      | node u x y =>
        change attachmentCount (extend (false,n,a) (extract (.node u x y))) =
          1 + (MergeTree.node u x y).unary
        rw [attachmentCount_extend, ihr]
        omega
    | node u x y =>
      cases r with
      | leaf a =>
        change attachmentCount (extend (true,n,a) (extract (.node u x y))) =
          1 + (MergeTree.node u x y).unary
        rw [attachmentCount_extend, ihl]
        omega
      | node v z w =>
        have h : ((close (extract (.node u x y)) ++ close (extract (.node v z w))).map List.length).sum =
            (MergeTree.node u x y).unary + (MergeTree.node v z w).unary := by
          rw [List.map_append, List.sum_append, attachmentCount_close, attachmentCount_close, ihl, ihr]
        simpa only [extract, attachmentCount, unary, isLeaf, bne_self_eq_false, Bool.false_eq_true,
          ite_false, Nat.zero_add, List.length_nil] using h

def chainNumber (x : Extraction α) : Nat := (close x).length

theorem chainNumber_extend (a : Attachment α) (x : Extraction α) :
    chainNumber (extend a x) = chainNumber x + (if x.1.isEmpty then 1 else 0) := by
  rcases x with ⟨xs,rest⟩
  cases xs <;> simp [chainNumber, extend, close]

theorem open_empty_of_leaf (a : List α) : (extract (.leaf a)).1.isEmpty = true := rfl

theorem nonleaf_charge (t : MergeTree α) (_h : t.isLeaf = false) :
    1 ≤ (if (extract t).1.isEmpty then 2 else 1) := by
  split <;> omega

def rootCharge (t : MergeTree α) : Nat :=
  if t.isLeaf then 0 else if (extract t).1.isEmpty then 2 else 1

theorem chain_count_bound (t : MergeTree α) :
    chainNumber (extract t) + rootCharge t ≤ 2*t.cherries := by
  induction t with
  | leaf a => rfl
  | node n l r ihl ihr =>
    cases l with
    | leaf a =>
      cases r with
      | leaf b => simp [chainNumber, close, extract, rootCharge, isLeaf, cherries]
      | node u x y =>
        have hr : rootCharge (.node n (.leaf a) (.node u x y)) = 1 := rfl
        have hc : (MergeTree.node n (.leaf a) (.node u x y)).cherries =
            (MergeTree.node u x y).cherries := by simp [cherries, isLeaf]
        rw [hr, hc]
        change chainNumber (extend (false,n,a) (extract (.node u x y))) + 1 ≤ _
        rw [chainNumber_extend]
        change chainNumber (extract (.node u x y)) +
          (if (extract (.node u x y)).1.isEmpty then 2 else 1) ≤
          2 * (MergeTree.node u x y).cherries at ihr
        by_cases hh : (extract (.node u x y)).1.isEmpty = true <;> simp [hh] at ihr ⊢ <;> omega
    | node u x y =>
      cases r with
      | leaf a =>
        have hr : rootCharge (.node n (.node u x y) (.leaf a)) = 1 := rfl
        have hc : (MergeTree.node n (.node u x y) (.leaf a)).cherries =
            (MergeTree.node u x y).cherries := by simp [cherries, isLeaf]
        rw [hr, hc]
        change chainNumber (extend (true,n,a) (extract (.node u x y))) + 1 ≤ _
        rw [chainNumber_extend]
        change chainNumber (extract (.node u x y)) +
          (if (extract (.node u x y)).1.isEmpty then 2 else 1) ≤
          2 * (MergeTree.node u x y).cherries at ihl
        by_cases hh : (extract (.node u x y)).1.isEmpty = true <;> simp [hh] at ihl ⊢ <;> omega
      | node v z w =>
        have hr : rootCharge (.node n (.node u x y) (.node v z w)) = 2 := rfl
        have hc : (MergeTree.node n (.node u x y) (.node v z w)).cherries =
            (MergeTree.node u x y).cherries + (MergeTree.node v z w).cherries := by
          simp [cherries, isLeaf]
        rw [hr, hc]
        change (close (extract (.node u x y)) ++ close (extract (.node v z w))).length + 2 ≤ _
        rw [List.length_append]
        change chainNumber (extract (.node u x y)) +
          (if (extract (.node u x y)).1.isEmpty then 2 else 1) ≤
          2 * (MergeTree.node u x y).cherries at ihl
        change chainNumber (extract (.node v z w)) +
          (if (extract (.node v z w)).1.isEmpty then 2 else 1) ≤
          2 * (MergeTree.node v z w).cherries at ihr
        change chainNumber (extract (.node u x y)) + chainNumber (extract (.node v z w)) + 2 ≤ _
        split at ihl <;> split at ihr <;> omega

end BPEForest
