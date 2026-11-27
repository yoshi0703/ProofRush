import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Kászonyi's cyclic boxes (Definitions 4–6), in CRT coordinates for
105 = 3·5·7. The three step sizes are exactly 105/p. -/

namespace Kasonyi105

abbrev Point := Fin 3 × Fin 5 × Fin 7
abbrev Idx := Fin 105
abbrev Gap := Idx → ℕ

def shift (i : Idx) (s : ℕ) : Idx :=
  ⟨(i.val+s)%105, by omega⟩

def index (p : Point) : Idx :=
  ⟨(70*p.1.val+21*p.2.1.val+15*p.2.2.val)%105, by omega⟩

def coordinates (i : Idx) : Point :=
  (⟨i.val%3,by omega⟩,⟨i.val%5,by omega⟩,⟨i.val%7,by omega⟩)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem index_coordinates : ∀ i : Idx, index (coordinates i) = i := by decide

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem coordinates_index : ∀ p : Point, coordinates (index p) = p := by
  have h : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7), coordinates (index (x,y,z)) = (x,y,z) := by decide
  rintro ⟨x,y,z⟩
  exact h x y z

theorem index_injective : Function.Injective index := by
  intro i j h
  simpa only [coordinates_index] using congrArg coordinates h

def firstStep (x t : Fin 3) : Fin 3 := ⟨(x.val+2*t.val)%3, by omega⟩
def secondStep (y t : Fin 5) : Fin 5 := ⟨(y.val+t.val)%5, by omega⟩
def thirdStep (z t : Fin 7) : Fin 7 := ⟨(z.val+t.val)%7, by omega⟩

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem shift_index_three : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7) (t : Fin 3),
    shift (index (x,y,z)) (t.val*35) = index (firstStep x t,y,z) := by decide

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem shift_index_five : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7) (t : Fin 5),
    shift (index (x,y,z)) (t.val*21) = index (x,secondStep y t,z) := by decide

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem shift_index_seven : ∀ (x : Fin 3) (y : Fin 5) (z : Fin 7) (t : Fin 7),
    shift (index (x,y,z)) (t.val*15) = index (x,y,thirdStep z t) := by decide

theorem step_three_complete : ∀ x x' : Fin 3, x ≠ x' →
    ∃ t : Fin 3, t ≠ 0 ∧ firstStep x t = x' := by decide

theorem step_five_complete : ∀ y y' : Fin 5, y ≠ y' →
    ∃ t : Fin 5, t ≠ 0 ∧ secondStep y t = y' := by decide

theorem step_seven_complete : ∀ z z' : Fin 7, z ≠ z' →
    ∃ t : Fin 7, t ≠ 0 ∧ thirdStep z t = z' := by decide

def delta (s : ℕ) (f : Idx → ℤ) (i : Idx) : ℤ := f i - f (shift i s)

def intGap (e : Gap) (i : Idx) : ℤ := e i

def value (f : Idx → ℤ) (x : Fin 3) (y : Fin 5) (z : Fin 7) : ℤ := f (index (x,y,z))

def box (f : Idx → ℤ) (x x' : Fin 3) (y y' : Fin 5) (z z' : Fin 7) : ℤ :=
  value f x y z - value f x' y z - value f x y' z - value f x y z' +
  value f x' y' z + value f x' y z' + value f x y' z' - value f x' y' z'

theorem cyclic_delta_box (f : Idx → ℤ)
    (x : Fin 3) (y : Fin 5) (z : Fin 7) (t : Fin 3) (u : Fin 5) (v : Fin 7) :
    delta (t.val*35) (delta (u.val*21) (delta (v.val*15) f)) (index (x,y,z)) =
      box f x (firstStep x t) y (secondStep y u) z (thirdStep z v) := by
  simp only [box,value,delta,shift_index_three,shift_index_five,shift_index_seven]
  ring

/-- Every full three-axis box, for all admissible integer scales reduced
modulo their corresponding prime, has zero alternating difference. -/
def TopZero (f : Idx → ℤ) : Prop :=
  ∀ (t : Fin 3) (u : Fin 5) (v : Fin 7), t ≠ 0 → u ≠ 0 → v ≠ 0 →
    ∀ i : Idx, delta (t.val*35) (delta (u.val*21) (delta (v.val*15) f)) i = 0

theorem topZero_iff_all_boxes (f : Idx → ℤ) :
    TopZero f ↔ ∀ (x x' : Fin 3) (y y' : Fin 5) (z z' : Fin 7), box f x x' y y' z z' = 0 := by
  constructor
  · intro h x x' y y' z z'
    by_cases hx : x = x'
    · subst x'
      unfold box
      ring
    by_cases hy : y = y'
    · subst y'
      unfold box
      ring
    by_cases hz : z = z'
    · subst z'
      unfold box
      ring
    obtain ⟨t,ht,ht'⟩ := step_three_complete x x' hx
    obtain ⟨u,hu,hu'⟩ := step_five_complete y y' hy
    obtain ⟨v,hv,hv'⟩ := step_seven_complete z z' hz
    simpa only [cyclic_delta_box,ht',hu',hv'] using h t u v ht hu hv (index (x,y,z))
  · intro h t u v _ _ _ i
    rcases hcoord : coordinates i with ⟨x,y,z⟩
    rw [← index_coordinates i,hcoord]
    exact (cyclic_delta_box f x y z t u v).trans (h _ _ _ _ _ _)

/-- All three order-two prime pairs are active, for every scale. -/
def AllPairsActive (f : Idx → ℤ) : Prop :=
  (∀ (t : Fin 3) (u : Fin 5), t ≠ 0 → u ≠ 0 →
    ∃ i, delta (t.val*35) (delta (u.val*21) f) i ≠ 0) ∧
  (∀ (t : Fin 3) (v : Fin 7), t ≠ 0 → v ≠ 0 →
    ∃ i, delta (t.val*35) (delta (v.val*15) f) i ≠ 0) ∧
  (∀ (u : Fin 5) (v : Fin 7), u ≠ 0 → v ≠ 0 →
    ∃ i, delta (u.val*21) (delta (v.val*15) f) i ≠ 0)

/-- Nonperiodicity in all nonzero cyclic shifts, stronger than testing only
the three prime-quotient shifts 35, 21, and 15. -/
def CyclicPrimitive (e : Gap) : Prop :=
  ∀ s : Idx, s ≠ 0 → ∃ i : Idx, e i ≠ e (shift i s.val)

def Stratum : Set Gap :=
  {e | TopZero (intGap e) ∧ AllPairsActive (intGap e) ∧ CyclicPrimitive e}

end Kasonyi105
