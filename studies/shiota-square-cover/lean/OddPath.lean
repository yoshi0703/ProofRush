import Mathlib.Data.Finset.Card

namespace GridCover.OddPath

def touches (a b : Bool) : Prop := a = true ∨ b = true

def covers (left : Bool) : List Bool → Bool → Prop
  | [], right => touches left right
  | first :: rest, right => touches left first ∧ covers first rest right

def paid (a : Bool) : ℕ := if a then 1 else 0

def cost : List Bool → ℕ
  | [] => 0
  | first :: rest => paid first + cost rest

def penalty (left right : Bool) : ℕ := if left || right then 0 else 1

theorem first_pair_lower {left first second right : Bool}
    (h₁ : touches left first) (h₂ : touches first second) :
    1 + penalty left right ≤ paid first + paid second + penalty second right := by
  cases left <;> cases first <;> cases second <;> cases right <;>
    simp_all [touches, penalty, paid]

theorem lower (t : ℕ) {left right : Bool} {inside : List Bool}
    (length : inside.length = 2 * t) (cover : covers left inside right) :
    t + penalty left right ≤ cost inside := by
  induction t generalizing left inside with
  | zero =>
    cases inside with
    | nil =>
      cases left <;> cases right <;> simp_all [covers, touches, penalty, cost]
    | cons head tail => simp at length
  | succ t ih =>
    cases inside with
    | nil => simp at length
    | cons first tail =>
      cases tail with
      | nil => simp at length; omega
      | cons second rest =>
        have lenRest : rest.length = 2 * t := by simp at length; omega
        have h := ih lenRest cover.2.2
        have step := first_pair_lower (right := right) cover.1 cover.2.1
        simp only [cost]
        omega

theorem choose_first_pair (left right : Bool) :
    ∃ first second : Bool, touches left first ∧ touches first second ∧ touches second right ∧
      paid first + paid second = 1 + penalty left right := by
  cases left <;> cases right
  · exact ⟨true, true, by simp [touches, paid, penalty]⟩
  · exact ⟨true, false, by simp [touches, paid, penalty]⟩
  · exact ⟨false, true, by simp [touches, paid, penalty]⟩
  · exact ⟨false, true, by simp [touches, paid, penalty]⟩

theorem penalty_eq_zero {left right : Bool} (h : touches left right) :
    penalty left right = 0 := by
  cases left <;> cases right <;> simp_all [touches, penalty]

/-- An odd path of length `2*t+1` has `2*t` internal vertices. The endpoint
selection costs are outside this identity. -/
theorem attained (t : ℕ) (left right : Bool) (feasible : 0 < t ∨ touches left right) :
    ∃ inside : List Bool, inside.length = 2 * t ∧ covers left inside right ∧
      cost inside = t + penalty left right := by
  induction t generalizing left with
  | zero =>
    have h : touches left right := feasible.resolve_left (by omega)
    exact ⟨[], rfl, h, by simp [cost, penalty_eq_zero h]⟩
  | succ t ih =>
    obtain ⟨first, second, hleft, hmiddle, hright, hc⟩ := choose_first_pair left right
    obtain ⟨rest, len, valid, exactCost⟩ := ih second (Or.inr hright)
    refine ⟨first :: second :: rest, ?_, ⟨hleft, hmiddle, valid⟩, ?_⟩
    · simp only [List.length_cons, len]
      omega
    · simp only [cost]
      rw [exactCost, penalty_eq_zero hright]
      omega

theorem minimum_internal_cost (t : ℕ) (left right : Bool)
    (feasible : 0 < t ∨ touches left right) :
    (∃ inside : List Bool, inside.length = 2 * t ∧ covers left inside right ∧
      cost inside = t + penalty left right) ∧
    ∀ inside : List Bool, inside.length = 2 * t → covers left inside right →
      t + penalty left right ≤ cost inside :=
  ⟨attained t left right feasible, fun _ => lower t⟩

end GridCover.OddPath
