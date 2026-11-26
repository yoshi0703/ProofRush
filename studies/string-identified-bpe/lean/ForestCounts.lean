import ForestTypes

set_option linter.unusedTactic false

namespace BPEForest.MergeTree

theorem split_nodes (t : MergeTree α) : t.nodes = t.cherries + t.unary + t.binary := by
  induction t with
  | leaf a => rfl
  | node n l r ihl ihr =>
    cases l <;> cases r <;>
      simp_all [nodes, cherries, unary, binary, isLeaf] <;> omega

theorem binary_lt_cherries_of_node (t : MergeTree α) (h : t.isLeaf = false) :
    t.binary < t.cherries := by
  induction t with
  | leaf a => simp [isLeaf] at h
  | node n l r ihl ihr =>
    cases l <;> cases r <;>
      simp_all [cherries, binary, isLeaf]; omega

theorem binary_le_cherries (t : MergeTree α) : t.binary ≤ t.cherries := by
  cases t with
  | leaf a => simp [binary, cherries]
  | node n l r =>
    have h := binary_lt_cherries_of_node (MergeTree.node n l r) rfl
    omega

end BPEForest.MergeTree
