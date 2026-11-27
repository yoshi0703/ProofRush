import GridGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

namespace GridCover

private theorem four_centers (a b c d : Center) : ({a,b,c,d} : Finset Center).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b,c,d} : Finset Center)
  have h2 := Finset.card_insert_le b ({c,d} : Finset Center)
  have h3 := Finset.card_insert_le c ({d} : Finset Center)
  simp only [Finset.card_singleton] at h3
  omega

theorem incidentCenters_card_le (e : GridEdge) : (incidentCenters e).card ≤ 4 := by
  cases e <;> apply four_centers

theorem admissible_card_le (input : Finset GridEdge) :
    (admissible input).card ≤ 4 * input.card := by
  calc
    _ ≤ (input.biUnion incidentCenters).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ e ∈ input, (incidentCenters e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ input, 4 := Finset.sum_le_sum fun e _ => incidentCenters_card_le e
    _ = _ := by simp [Nat.mul_comm]

/-- The selected centers pass the physical test precisely when their literal
eight-edge perimeters have union equal to the input edge set. -/
theorem physicalCover_iff_union (input : Finset GridEdge) (s : Finset Center) :
    physicalCover input s ↔ seedEdges s = input := by
  constructor
  · rintro ⟨hlegal, hall⟩
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨p, hp, h⟩ := Finset.mem_biUnion.mp he
      exact hlegal p hp h
    · intro e he
      exact Finset.mem_biUnion.mpr (hall e he)
  · intro h
    refine ⟨fun p hp e he => h ▸ Finset.mem_biUnion.mpr ⟨p, hp, he⟩, ?_⟩
    intro e he
    have hmem : e ∈ seedEdges s := h.symm ▸ he
    exact Finset.mem_biUnion.mp hmem

theorem physicalCover_card_le {input : Finset GridEdge} {s : Finset Center}
    (h : physicalCover input s) : s.card ≤ 4 * input.card :=
  (Finset.card_le_card (fun p hp => (mem_admissible input p).mpr (h.1 p hp))).trans
    (admissible_card_le input)

def distinctVerifier (input : Finset GridEdge) (k : ℕ) (s : Finset Center) : Bool :=
  decide (s.card = k ∧ seedEdges s = input)

theorem distinct_verifier_spec (input : Finset GridEdge) (k : ℕ) :
    (∃ selected, physicalCover input selected ∧ selected.card = k) ↔
    ∃ s : Finset Center, s.card ≤ 4 * input.card ∧ distinctVerifier input k s = true := by
  simp only [distinctVerifier, decide_eq_true_eq]
  constructor
  · rintro ⟨s, h, hk⟩
    exact ⟨s, physicalCover_card_le h, hk, (physicalCover_iff_union _ _).mp h⟩
  · rintro ⟨s, _, hk, h⟩
    exact ⟨s, (physicalCover_iff_union _ _).mpr h, hk⟩

/-- The literal list of placements may repeat centers and have a very large
length supplied in binary. A short set plus the nonemptiness check suffices. -/
def repeatedBudget (input : Finset GridEdge) (k : ℕ) : Prop :=
  ∃ xs : List Center, xs.length = k ∧ physicalCover input xs.toFinset

def repeatedVerifier (input : Finset GridEdge) (k : ℕ) (s : Finset Center) : Bool :=
  decide (s.card ≤ k ∧ (k = 0 ∨ s.Nonempty) ∧ seedEdges s = input)

theorem repeated_verifier_spec (input : Finset GridEdge) (k : ℕ) :
    repeatedBudget input k ↔ ∃ s : Finset Center,
      s.card ≤ 4 * input.card ∧ repeatedVerifier input k s = true := by
  simp only [repeatedVerifier, decide_eq_true_eq]
  constructor
  · rintro ⟨xs, rfl, h⟩
    refine ⟨xs.toFinset, physicalCover_card_le h,
      List.toFinset_card_le _, ?_, (physicalCover_iff_union _ _).mp h⟩
    cases xs with
    | nil => exact Or.inl rfl
    | cons x xs => exact Or.inr ⟨x, by simp⟩
  · rintro ⟨s, _, hk, hk0 | hn, he⟩
    · have hl : s.toList.length = k := by simpa [hk0] using hk
      exact ⟨s.toList, hl, by simpa using (physicalCover_iff_union _ _).mpr he⟩
    · obtain ⟨p, hp⟩ := hn
      let xs := s.toList ++ List.replicate (k - s.card) p
      have same : xs.toFinset = s := by
        ext q
        simp only [xs, List.mem_toFinset, List.mem_append, Finset.mem_toList]
        constructor
        · rintro (hq | hq)
          · exact hq
          · exact (List.eq_of_mem_replicate hq) ▸ hp
        · exact Or.inl
      refine ⟨xs, ?_, same ▸ (physicalCover_iff_union _ _).mpr he⟩
      simp only [xs, List.length_append, Finset.length_toList, List.length_replicate]
      omega

theorem repeated_iff_distinct_of_le (input : Finset GridEdge) (k : ℕ)
    (bound : k ≤ (admissible input).card) :
    repeatedBudget input k ↔ ∃ s : Finset Center, physicalCover input s ∧ s.card = k := by
  constructor
  · rintro ⟨xs, hlen, cover⟩
    have allowed : xs.toFinset ⊆ admissible input :=
      fun p hp => (mem_admissible input p).mpr (cover.1 p hp)
    have small : xs.toFinset.card ≤ k := (List.toFinset_card_le xs).trans_eq hlen
    obtain ⟨t, grows, legal, card⟩ := Finset.exists_subsuperset_card_eq allowed small bound
    refine ⟨t, ⟨fun p hp => (mem_admissible _ _).mp (legal hp), ?_⟩, card⟩
    intro e he
    obtain ⟨p, hp, covers⟩ := cover.2 e he
    exact ⟨p, grows hp, covers⟩
  · rintro ⟨s, cover, card⟩
    exact ⟨s.toList, by simpa using card, by simpa using cover⟩

end GridCover
