import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace TideZoneAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- One entry per subset of labeled days, retaining multiplicities. -/
def picks : List ℕ → List (ℕ × ℕ)
  | [] => [(0,0)]
  | v :: vs =>
    let tail := picks vs
    tail ++ tail.map fun p => (p.1 + 1, p.2 + v)

theorem number_of_picks (v : List ℕ) : (picks v).length = 2^v.length := by
  induction v with
  | nil => rfl
  | cons a rest ih => simp [picks,ih,pow_succ]; omega

/-- A pair records the successful and total equally likely samples of size k.
The tolerances compare the Horvitz--Thompson estimate to the finite-site total. -/
def rate (upper : ℕ) (lower : List ℕ) (k : ℕ) : ℕ × ℕ :=
  if k = 0 then (0,0) else
    let all := (picks lower).filter (fun p => p.1 == k)
    let whole := upper + lower.sum
    let good := all.countP (fun p =>
      let scaled := 5*(k*upper+lower.length*p.2)
      decide (4*k*whole ≤ scaled ∧ scaled ≤ 6*k*whole))
    (good, all.length)

def lowerA := [92,57,97,119,105,259,392,225,314,271]
def lowerB := [5,20,62,27,245,223,69,153,305]

def tableA : List (ℕ × ℕ) := (List.range 11).map (rate 3503 lowerA)
def tableB : List (ℕ × ℕ) := (List.range 10).map (rate 1952 lowerB)

theorem exact_a : tableA =
    [(0,0),(7,10),(38,45),(115,120),(209,210),(252,252),
      (210,210),(120,120),(45,45),(10,10),(1,1)] := by decide +kernel

theorem exact_b : tableB =
    [(0,0),(3,9),(22,36),(65,84),(112,126),(121,126),
      (84,84),(36,36),(9,9),(1,1)] := by decide +kernel

/-- At least 95% joint success under independent choices at the two sites. -/
def goodJoint (na nb : ℕ) : Prop :=
  let a := tableA[na]?.getD (0,0)
  let b := tableB[nb]?.getD (0,0)
  0 < a.2*b.2 ∧ 19*(a.2*b.2) ≤ 20*(a.1*b.1)

/-- The two allocations listed are exactly those with budget up to nine that
meet the threshold among all physically feasible positive sample sizes. -/
theorem threshold_nine : ∀ a : Fin 11, ∀ b : Fin 10,
    (a.val + b.val ≤ 9 ∧ goodJoint a b) ↔
       (a.val = 3 ∧ b.val = 6) ∨ (a.val = 4 ∧ b.val = 5) := by
  unfold goodJoint
  rw [exact_a,exact_b]
  decide +kernel

/-- The extreme observed shares force a sharp worst relative reconstruction
error even when any real multiplier is allowed. The two inequalities follow
from absolute error ≤ e at the respective observations. -/
theorem multiplier_floor (c e : ℝ)
    (lo : 1 - c * (108/413) ≤ e) (hi : c * (216/221) - 1 ≤ e) :
    605/1047 ≤ e := by linarith

theorem multiplier_attains :
    let c : ℚ := 91273/56538
    (1 - c*(108/413) = 605/1047) ∧ (c*(216/221)-1 = 605/1047) := by
  norm_num

/-- In the Italian seasonal comparison, even the two-decimal density intervals
(without using the Clean Coast Index) force the opposite inland direction. -/
theorem spina_direction (autumn winter : ℤ)
    (ha : 0 ≤ autumn ∧ autumn ≤ 2) (hw : 117 ≤ winter ∧ winter ≤ 121) :
    (727 : ℤ) - 653 = 74 ∧
    -47 ≤ (727-winter)-(653-autumn) ∧ (727-winter)-(653-autumn) ≤ -41 := by
  omega

end TideZoneAudit
