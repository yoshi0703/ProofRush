import OddPath
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GridCover.OddPath

variable {V : Type*} [DecidableEq V]

open scoped BigOperators

def vertexCover (edges : Finset (V × V)) (chosen : Finset V) : Prop :=
  ∀ e ∈ edges, e.1 ∈ chosen ∨ e.2 ∈ chosen

def missed (edges : Finset (V × V)) (chosen : Finset V) : Finset (V × V) :=
  edges.filter fun e => e.1 ∉ chosen ∧ e.2 ∉ chosen

def repair (edges : Finset (V × V)) (chosen : Finset V) : Finset V :=
  chosen ∪ (missed edges chosen).image Prod.fst

theorem repair_covers (edges : Finset (V × V)) (chosen : Finset V) :
    vertexCover edges (repair edges chosen) := by
  intro e he
  by_cases first : e.1 ∈ chosen
  · exact Or.inl (Finset.mem_union_left _ first)
  by_cases second : e.2 ∈ chosen
  · exact Or.inr (Finset.mem_union_left _ second)
  exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨e, Finset.mem_filter.mpr ⟨he, first, second⟩, rfl⟩))

theorem repair_cost (edges : Finset (V × V)) (chosen : Finset V) :
    (repair edges chosen).card ≤ chosen.card + (missed edges chosen).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_image_le _)

def chosenBool (chosen : Finset V) (p : V) : Bool := decide (p ∈ chosen)

theorem touches_chosenBool {chosen : Finset V} {e : V × V} :
    touches (chosenBool chosen e.1) (chosenBool chosen e.2) ↔
      e.1 ∈ chosen ∨ e.2 ∈ chosen := by
  simp [touches, chosenBool]

theorem penalty_sum (edges : Finset (V × V)) (chosen : Finset V) :
    (∑ e ∈ edges, penalty (chosenBool chosen e.1) (chosenBool chosen e.2)) =
      (missed edges chosen).card := by
  rw [missed, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h₁ : e.1 ∈ chosen <;> by_cases h₂ : e.2 ∈ chosen <;>
    simp [penalty, chosenBool, h₁, h₂]

def subdividedCover (edges : Finset (V × V)) (t : V × V → ℕ)
    (chosen : Finset V) (internal : (V × V) → List Bool) : Prop :=
  ∀ e ∈ edges, (internal e).length = 2 * t e ∧
    covers (chosenBool chosen e.1) (internal e) (chosenBool chosen e.2)

def subdivisionCost (edges : Finset (V × V)) (chosen : Finset V)
    (internal : (V × V) → List Bool) : ℕ :=
  chosen.card + ∑ e ∈ edges, cost (internal e)

/-- Each edge becomes an independently labelled path of odd length
`2*t(e)+1`, whose internal vertices are disjoint from all other paths.
The special case `t(e)=0` preserves the literal endpoint edge. -/
theorem subdivision_budget_iff (edges : Finset (V × V)) (t : V × V → ℕ) (k : ℕ) :
    (∃ chosen : Finset V, vertexCover edges chosen ∧ chosen.card ≤ k) ↔
    (∃ (chosen : Finset V) (internal : (V × V) → List Bool),
      subdividedCover edges t chosen internal ∧
        subdivisionCost edges chosen internal ≤ (∑ e ∈ edges, t e) + k) := by
  classical
  constructor
  · rintro ⟨chosen, cover, budget⟩
    have all (e : V × V) (he : e ∈ edges) :
        ∃ inside, inside.length = 2 * t e ∧
          covers (chosenBool chosen e.1) inside (chosenBool chosen e.2) ∧ cost inside = t e := by
      have touched := touches_chosenBool.mpr (cover e he)
      obtain ⟨inside, hlen, hc, exactCost⟩ := attained (t e) _ _ (Or.inr touched)
      exact ⟨inside, hlen, hc, by simpa [penalty_eq_zero touched] using exactCost⟩
    let internal (e : V × V) := if he : e ∈ edges then Classical.choose (all e he) else []
    have chosen_spec (e : V × V) (he : e ∈ edges) :
        (internal e).length = 2 * t e ∧
          covers (chosenBool chosen e.1) (internal e) (chosenBool chosen e.2) ∧
          cost (internal e) = t e := by
      simpa [internal, he] using Classical.choose_spec (all e he)
    have hSum : (∑ e ∈ edges, cost (internal e)) = ∑ e ∈ edges, t e :=
      Finset.sum_congr rfl fun e he => (chosen_spec e he).2.2
    refine ⟨chosen, internal, fun e he => ⟨(chosen_spec e he).1, (chosen_spec e he).2.1⟩, ?_⟩
    unfold subdivisionCost
    rw [hSum]
    omega
  · rintro ⟨chosen, internal, cover, budget⟩
    have perEdge (e : V × V) (he : e ∈ edges) :
        t e + penalty (chosenBool chosen e.1) (chosenBool chosen e.2) ≤ cost (internal e) :=
      lower (t e) (cover e he).1 (cover e he).2
    have hSum := Finset.sum_le_sum perEdge
    rw [Finset.sum_add_distrib, penalty_sum] at hSum
    have repairedCost := repair_cost edges chosen
    refine ⟨repair edges chosen, repair_covers edges chosen, ?_⟩
    unfold subdivisionCost at budget
    omega

end GridCover.OddPath
