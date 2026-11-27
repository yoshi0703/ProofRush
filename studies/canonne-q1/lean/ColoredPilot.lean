import BirthdayFull
import Mathlib.Data.Fintype.Sigma

namespace CanonneColoredPilot

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {B : Type*} [Fintype B]

abbrev Slot (K : B → ℕ) := Σ b : B, Fin (K b)

/-- The global mask chooses a group and one of its slots, or a fresh draw. -/
def coloredLatent (K : B → ℕ) (a : B → ℝ) : Option (Slot K) → ℝ
  | none => 1 - ∑ b, a b
  | some j => a j.1 / K j.1

theorem coloredLatent_isLaw {K : B → ℕ} {a : B → ℝ}
    (hK : ∀ b, 0 < K b) (ha : ∀ b, 0 ≤ a b) (hsum : ∑ b, a b ≤ 1) :
    IsLaw (coloredLatent K a) := by
  classical
  have hcast (b : B) : (K b : ℝ) ≠ 0 := by exact_mod_cast (hK b).ne'
  refine ⟨?_, ?_⟩
  · rintro (_ | j)
    · exact sub_nonneg.mpr hsum
    · exact div_nonneg (ha j.1) (by positivity)
  · rw [Fintype.sum_option, Fintype.sum_sigma]
    simp only [coloredLatent, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have htotal : ∑ b, (K b : ℝ) * (a b / K b) = ∑ b, a b :=
      Finset.sum_congr rfl fun b _ => by field_simp [hcast b]
    rw [htotal]
    ring

def activeRepeat {X : Type*} {n : ℕ} (x : Fin n → Option X) : Prop :=
  ∃ pair ∈ orderedPairs n, ∃ slot : X, x pair.1 = some slot ∧ x pair.2 = some slot

theorem active_repeat_bound {X : Type*} [Fintype X] {n : ℕ} {p : Option X → ℝ}
    (hp : IsLaw p) :
    eventMass (pilotLaw p) (activeRepeat (X := X) (n := n)) ≤
      (n.choose 2 : ℝ) * ∑ j : X, (p (some j))^2 := by
  classical
  have hn := (pilotLaw_isLaw (I := Fin n) hp).nonneg
  unfold activeRepeat
  apply (eventMass_union_le (pilotLaw p) hn (orderedPairs n) _).trans
  have pairBound (pair : Fin n × Fin n) (hpair : pair ∈ orderedPairs n) :
      eventMass (pilotLaw p) (fun x => ∃ j : X, x pair.1 = some j ∧ x pair.2 = some j)
        ≤ ∑ j : X, (p (some j))^2 := by
    have hlt : pair.1 < pair.2 := (Finset.mem_filter.mp hpair).2
    have eqEvent :
        eventMass (pilotLaw p) (fun x => ∃ j : X, x pair.1 = some j ∧ x pair.2 = some j) =
        eventMass (pilotLaw p) (fun x => ∃ j ∈ (Finset.univ : Finset X),
          x pair.1 = some j ∧ x pair.2 = some j) := by
      apply eventMass_congr
      simp
    rw [eqEvent]
    refine (eventMass_union_le (pilotLaw p) hn Finset.univ _).trans ?_
    simp [(two_coordinate_event hp hlt.ne), pow_two]
  calc
    _ ≤ ∑ _pair ∈ orderedPairs n, ∑ j : X, (p (some j))^2 := Finset.sum_le_sum pairBound
    _ = _ := by simp [orderedPairs_card, nsmul_eq_mul]

theorem colored_slot_square_sum {K : B → ℕ} {a : B → ℝ}
    (hK : ∀ b, 0 < K b) :
    (∑ j : Slot K, (coloredLatent K a (some j))^2) = ∑ b, (a b)^2 / K b := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  simp only [coloredLatent, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : (K b : ℝ) ≠ 0 := by exact_mod_cast (hK b).ne'
  field_simp [hb]

/-- One global birthday comparison, with disjoint slots in different bins. -/
theorem colored_repeat_bound {K : B → ℕ} {a : B → ℝ} {n : ℕ}
    (hK : ∀ b, 0 < K b) (ha : ∀ b, 0 ≤ a b) (hsum : ∑ b, a b ≤ 1) :
    eventMass (pilotLaw (coloredLatent K a)) (activeRepeat (n := n) (X := Slot K)) ≤
      (n.choose 2 : ℝ) * ∑ b, (a b)^2 / K b := by
  rw [← colored_slot_square_sum hK]
  exact active_repeat_bound (coloredLatent_isLaw hK ha hsum)

end
end CanonneColoredPilot
