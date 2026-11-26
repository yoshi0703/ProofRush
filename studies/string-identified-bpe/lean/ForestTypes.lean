import SpellingBPE

/-! Occurrence trees for comparator executions. Leaves retain their original
  token occurrences; equal spellings do not identify occurrences. -/
namespace BPEForest

inductive MergeTree (α : Type) where
  | leaf : List α → MergeTree α
  | node : Nat → MergeTree α → MergeTree α → MergeTree α
  deriving DecidableEq

namespace MergeTree

def leaves : MergeTree α → List (List α)
  | .leaf a => [a]
  | .node _ l r => leaves l ++ leaves r

def spell : MergeTree α → List α
  | .leaf a => a
  | .node _ l r => spell l ++ spell r

def nodes : MergeTree α → Nat
  | .leaf _ => 0
  | .node _ l r => 1 + nodes l + nodes r

def isLeaf : MergeTree α → Bool
  | .leaf _ => true
  | .node _ _ _ => false

def cherries : MergeTree α → Nat
  | .leaf _ => 0
  | .node _ l r => (if l.isLeaf && r.isLeaf then 1 else 0) + cherries l + cherries r

def unary : MergeTree α → Nat
  | .leaf _ => 0
  | .node _ l r => (if l.isLeaf != r.isLeaf then 1 else 0) + unary l + unary r

def binary : MergeTree α → Nat
  | .leaf _ => 0
  | .node _ l r => (if !l.isLeaf && !r.isLeaf then 1 else 0) + binary l + binary r

/-- Every merge is assigned its chronological rule, and all descendant stages
    are strictly earlier than the containing stage. -/
def Valid (rules : List (SpellingBPE.Pair α)) : Nat → MergeTree α → Prop
  | _, .leaf _ => True
  | bound, .node t l r => t < bound ∧ rules[t]? = some (l.spell, r.spell) ∧
      Valid rules t l ∧ Valid rules t r

end MergeTree
end BPEForest
