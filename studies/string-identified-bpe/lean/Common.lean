import DecoyRows
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The diamond family. Token spellings are unary strings represented by
lengths; different parses with the same length have identical spelling. -/
namespace Diamond
open SpellingBPE SpellingDecoy

def U (m j i : Nat) : Nat := j*m+i+1
def B (m : Nat) : Nat := 2*m*m+1
def V (m j i : Nat) : Nat := B m-U m j i
def hub (m j : Nat) : Nat := (j+1)*B m
def variant (j x y : Nat) : Nat := if j%2=0 then x else y

def wrap (m x y start count : Nat) (center : List Nat) : List Nat :=
  (List.range count).foldl (fun w a =>
    let j := start+a
    U m j (variant j x y) :: w ++ [V m j (variant j x y)]) center

def rowLengths (m s x y : Nat) : List Nat := wrap m x y s (m-s) [hub m s]
def spell (n : Nat) : Token Nat := List.replicate n 0
def row (m s x y : Nat) : Word Nat := (rowLengths m s x y).map spell

def coreTable (m : Nat) : Table Nat :=
  (List.range m).flatMap fun s => (List.range m).flatMap fun x =>
    (List.range m).map fun y => (1,row m s x y)

def leftRule (m j i : Nat) : Pair Nat := (spell (U m j i), spell (hub m j))
def rightRule (m j i : Nat) : Pair Nat := (spell (hub m j+U m j i),spell (V m j i))
def layerRules (m j : Nat) : List (Pair Nat) :=
  (List.range m).flatMap fun i => [leftRule m j i,rightRule m j i]
def comparator (m : Nat) : List (Pair Nat) :=
  (List.range m).flatMap (layerRules m)

theorem U_pos (m j i : Nat) : 0 < U m j i := by simp [U]

theorem U_lt_B {m j i : Nat} (hj : j<m) (hi : i<m) : U m j i < B m := by
  unfold U B
  nlinarith

theorem V_pos {m j i : Nat} (hj : j<m) (hi : i<m) : 0 < V m j i := by
  unfold V
  have := U_lt_B hj hi
  omega

theorem V_lt_B {m j i : Nat} (hj : j<m) (hi : i<m) : V m j i < B m := by
  unfold V
  have a := U_lt_B hj hi
  have b := U_pos m j i
  omega

theorem pieces_sum {m j i : Nat} (hj : j<m) (hi : i<m) : U m j i + V m j i = B m := by
  unfold V
  have := U_lt_B hj hi
  omega

theorem spelling_join (a b : Nat) : spell a ++ spell b = spell (a+b) := by
  exact (List.replicate_add ..).symm

theorem completion {m j i : Nat} (hj : j<m) (hi : i<m) :
    spell (hub m j + U m j i) ++ spell (V m j i) = spell (hub m (j+1)) := by
  rw [spelling_join]
  congr 1
  rw [Nat.add_assoc, pieces_sum hj hi]
  simp [hub, Nat.add_mul]

theorem comparator_length (m : Nat) : (comparator m).length = 2*m*m := by
  simp [comparator, layerRules, List.length_flatMap]
  ring

end Diamond
