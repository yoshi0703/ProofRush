import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-! Full replacement-count greedy and arbitrary partial merges for words of
tokens identified by their literal spelling. Underlying letters have type α.
The result of joining X and Y is their concatenation even when a token of that
spelling already exists. Every initial spelling in the theorem is nonempty. -/
namespace SpellingBPE
variable {α : Type} [DecidableEq α]
abbrev Token (α : Type) := List α
abbrev Word (α : Type) := List (Token α)
abbrev Pair (α : Type) := Token α × Token α

def full (p : Pair α) : Word α → Word α
  | [] => []
  | [x] => [x]
  | x::y::t => if (x,y) = p then (x++y) :: full p t else x :: full p (y::t)

def candidates : Word α → List (Pair α)
  | [] => []
  | [_] => []
  | x::y::t => (x,y) :: candidates (y::t)

def gain (p : Pair α) (w : Word α) := w.length - (full p w).length

theorem full_nonincrease (p : Pair α) (w : Word α) : (full p w).length ≤ w.length := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs h₁ h₂ =>
    simp only [full]
    split <;> simp only [List.length_cons] at * <;> have h := h₂ y <;> omega

theorem no_occurrence {p : Pair α} (w : Word α) (absent : p ∉ candidates w) : full p w = w := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y xs _ ih =>
    have h : (x,y) ≠ p := fun eq => absent (by rw [← eq]; exact List.mem_cons_self ..)
    have rest : p ∉ candidates (y::xs) := fun hw => absent (List.mem_cons_of_mem _ hw)
    simp only [full, ite_eq_right h, ih y rest]

/-- Maximality among every pair of spellings, with positive gain. If no
pair remains, a run can be stopped. Our refutation uses four positive steps. -/
def Maximal (w : Word α) (p : Pair α) := 0 < gain p w ∧ ∀ q : Pair α, gain q w ≤ gain p w

def maxCheck (w : Word α) (p : Pair α) : Bool :=
  decide (0 < gain p w) && (candidates w).all (fun q => decide (gain q w ≤ gain p w))

theorem maximal_of_check {w : Word α} {p : Pair α} (h : maxCheck w p = true) : Maximal w p := by
  obtain ⟨pos,dom⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true pos,?_⟩
  intro q
  by_cases occurs : q ∈ candidates w
  · exact of_decide_eq_true (List.all_eq_true.mp dom q occurs)
  · simp [gain,no_occurrence w occurs]

inductive Partial (p : Pair α) : Word α → Word α → Prop
  | nil : Partial p [] []
  | keep (x) {w v} : Partial p w v → Partial p (x::w) (x::v)
  | replace {w v} : Partial p w v → Partial p (p.1::p.2::w) ((p.1++p.2)::v)

theorem full_partial (p : Pair α) (w : Word α) : Partial p w (full p w) := by
  induction w using List.twoStepInduction with
  | nil => exact .nil
  | singleton x => exact .keep x .nil
  | cons_cons x y xs h ih =>
    by_cases eq : (x,y) = p
    · subst p
      simpa [full] using Partial.replace (p := (x,y)) h
    · simpa [full,eq] using Partial.keep x (ih y)

inductive Feasible : ℕ → Word α → Word α → Prop
  | nil (w) : Feasible 0 w w
  | cons {k w u v p} : Partial p w u → Feasible k u v → Feasible (k+1) w v

inductive Greedy : ℕ → Word α → Word α → Prop
  | nil (w) : Greedy 0 w w
  | cons {k w v p} : Maximal w p → Greedy k (full p w) v → Greedy (k+1) w v

def play (w : Word α) : List (Pair α) → Word α
  | [] => w
  | p::ps => play (full p w) ps

def legalCheck (w : Word α) : List (Pair α) → Bool
  | [] => true
  | p::ps => maxCheck w p && legalCheck (full p w) ps

theorem greedy_checked (w : Word α) (ps : List (Pair α)) (h : legalCheck w ps = true) :
    Greedy ps.length w (play w ps) := by
  induction ps generalizing w with
  | nil => exact .nil w
  | cons p ps ih =>
    obtain ⟨hh,ht⟩ := Bool.and_eq_true_iff.mp h
    exact .cons (maximal_of_check hh) (ih _ ht)

theorem plays_feasible (w : Word α) (ps : List (Pair α)) : Feasible ps.length w (play w ps) := by
  induction ps generalizing w with
  | nil => exact .nil w
  | cons p ps ih => exact .cons (full_partial p w) (ih _)

/-- Maximum attainable shortening using at most k partial rules. It is
unchanged by allowing an empty selection in a declared partial rule. -/
noncomputable def optimum (w : Word α) (k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun c => ∃ j ≤ k, ∃ v, Feasible j w v ∧ w.length-v.length=c) w.length

omit [DecidableEq α] in
theorem feasible_le_optimum {k j : ℕ} {w v : Word α} (hjk : j ≤ k) (h : Feasible j w v) :
    w.length-v.length ≤ optimum w k := by
  classical
  unfold optimum
  exact Nat.le_findGreatest (Nat.sub_le ..) ⟨j,hjk,v,h,rfl⟩

omit [DecidableEq α] in
theorem optimum_attained (w : Word α) (k : ℕ) :
    ∃ j ≤ k, ∃ v, Feasible j w v ∧ w.length-v.length=optimum w k := by
  classical
  have witness : ∃ j ≤ k, ∃ v, Feasible j w v ∧ w.length-v.length=0 :=
    ⟨0,Nat.zero_le _,w,.nil w,Nat.sub_self _⟩
  unfold optimum
  exact Nat.findGreatest_spec (P := fun c => ∃ j ≤ k, ∃ v, Feasible j w v ∧ w.length-v.length=c) (Nat.zero_le w.length) witness

/-- The lower-bound clause of Theorem 13 with the hypothesis of unique
decodability removed, on single finite strings. Clearing the denominator
2 k^k gives exactly the source's constant for budgets k ≥ 2. -/
def Extension (α : Type) [DecidableEq α] : Prop :=
  ∀ (w : Word α) (k : ℕ) (v : Word α), 2 ≤ k → (∀ x ∈ w, x ≠ []) → Greedy k w v →
    (k^k - (k-2)^k)*optimum w k ≤ 2*k^k*(w.length - v.length)

def Factor (u : Word α) (w : Word α) : Prop := ∃ l r : Word α, w = l ++ u ++ r

def UniqueDecoding (w : Word α) : Prop :=
  ∀ u v : Word α, Factor u w → Factor v w → u.flatten = v.flatten → u = v

end SpellingBPE
