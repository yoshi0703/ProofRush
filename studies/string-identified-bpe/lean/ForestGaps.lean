import ForestTypes
import Mathlib.Tactic.Linarith

/-! Long temporal gaps in each chronological attachment path. -/
namespace BPEForest

/-- Stages in a path are weakly increasing and lie between `lo` and `hi`. -/
inductive Chronological (hi : Nat) : Nat → List Nat → Prop
  | nil (lo) : lo ≤ hi → Chronological hi lo []
  | cons {lo x xs} : lo ≤ x → Chronological hi x xs → Chronological hi lo (x::xs)

/-- Count gaps greater than s, including the gap from lo to the first stage. -/
def longGaps (s lo : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => (if s < x-lo then 1 else 0) + longGaps s x xs

theorem Chronological.bound {hi lo : Nat} {xs : List Nat}
    (h : Chronological hi lo xs) : lo ≤ hi := by
  induction h with
  | nil lo hb => exact hb
  | cons hle rest ih => omega

/-- Long gaps have disjoint time intervals; their total cost is at most the
    available duration. No positive lower bound on `s` is needed. -/
theorem longGaps_bound {hi lo : Nat} {xs : List Nat}
    (h : Chronological hi lo xs) (s : Nat) :
    s * longGaps s lo xs ≤ hi-lo := by
  induction h with
  | nil lo hb => simp [longGaps]
  | @cons lo x xs hle rest ih =>
    have hx : x ≤ hi := rest.bound
    by_cases hh : s < x-lo
    · simp only [longGaps, ite_eq_left hh, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [longGaps, ite_eq_right hh, Nat.zero_add]
      omega

/-- The gaps between consecutive stages in a (possibly empty) path. -/
def longEdges (s : Nat) : List Nat → Nat
  | [] => 0
  | x::xs => longGaps s x xs

theorem longEdges_bound {k : Nat} {xs : List Nat}
    (h : Chronological k 0 xs) (s : Nat) :
    s * longEdges s xs ≤ k := by
  cases xs with
  | nil => simp [longEdges]
  | cons x xs =>
    cases h with
    | cons _ rest =>
      have hh := longGaps_bound rest s
      simp only [longEdges]
      omega

/-- Summing over paths gives the global charging bound without division. -/
theorem longEdges_sum_bound (k s : Nat) (paths : List (List Nat))
    (h : ∀ xs ∈ paths, Chronological k 0 xs) :
    s * (paths.map (longEdges s)).sum ≤ paths.length * k := by
  induction paths with
  | nil => simp
  | cons xs rest ih =>
    have hx := longEdges_bound (h xs (by simp)) s
    have hr := ih (by
      intro ys hy
      exact h ys (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add,
      Nat.succ_mul]
    omega

end BPEForest
