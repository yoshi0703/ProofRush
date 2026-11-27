import GridPitch17Reduction
import GridCertificates
import GridInduced
import GridOutputBounds

namespace GridCover.Shiota

open PathEmbedding.Stride17
open scoped BigOperators

structure Instance where
  edges : Finset GridEdge
  budget : ℕ

def exactDistinct (I : Instance) : Prop :=
  ∃ s : Finset Center, seedEdges s = I.edges ∧ s.card = I.budget

def exactWithRepetition (I : Instance) : Prop :=
  ∃ xs : List Center, xs.length = I.budget ∧ seedEdges xs.toFinset = I.edges

def atMost (I : Instance) : Prop :=
  ∃ s : Finset Center, seedEdges s = I.edges ∧ s.card ≤ I.budget

variable {V : Type} [DecidableEq V] (D : AxisGridSource.Drawing V)

/-- Explicit output edge set and clipped cardinality. All choices of stencil,
orientation and switch are computed from the source drawing. -/
def reduce (hdeg : D.boundedDegree) (b : ℕ) : Instance :=
  let A := D.certifiedLayout hdeg
  let offset := ∑ e ∈ D.edges.toFinset, (17*D.length e - 1 - skip (leftTee D e && rightTee D e))
  ⟨seedEdges (A.guardSet ∪ A.optionalSet),
    min (A.guardSet ∪ A.optionalSet).card (A.guardSet.card + offset + b)⟩

private theorem capacity (hdeg : D.boundedDegree) (b : ℕ) :
    (reduce D hdeg b).budget ≤ (admissible (reduce D hdeg b).edges).card := by
  let A := D.certifiedLayout hdeg
  let seeds := A.guardSet ∪ A.optionalSet
  have inclusion : seeds ⊆ admissible (seedEdges seeds) := by
    intro p hp
    exact (mem_admissible _ _).mpr (fun e he => Finset.mem_biUnion.mpr ⟨p,hp,he⟩)
  exact (min_le_left _ _).trans (Finset.card_le_card inclusion)

theorem distinct_reduction (hdeg : D.boundedDegree) (b : ℕ) :
    exactDistinct (reduce D hdeg b) ↔
    ∃ s : Finset V, OddPath.vertexCover D.edges.toFinset s ∧ s.card ≤ b := by
  have h := pitch17_exact_cover D hdeg b
  dsimp only at h
  simp only [physicalCover_iff_union] at h
  exact h

theorem repeat_reduction (hdeg : D.boundedDegree) (b : ℕ) :
    exactWithRepetition (reduce D hdeg b) ↔
    ∃ s : Finset V, OddPath.vertexCover D.edges.toFinset s ∧ s.card ≤ b := by
  let I := reduce D hdeg b
  have h := repeated_iff_distinct_of_le I.edges I.budget (capacity D hdeg b)
  simp only [repeatedBudget, physicalCover_iff_union] at h
  exact h.trans (distinct_reduction D hdeg b)

theorem atMost_reduction (hdeg : D.boundedDegree) (b : ℕ) :
    atMost (reduce D hdeg b) ↔
    ∃ s : Finset V, OddPath.vertexCover D.edges.toFinset s ∧ s.card ≤ b := by
  let I := reduce D hdeg b
  have pad : atMost I ↔ exactDistinct I := by
    constructor
    · rintro ⟨s,hunion,hcard⟩
      have hc := (physicalCover_iff_union I.edges s).mpr hunion
      have allowed : s ⊆ admissible I.edges := fun p hp => (mem_admissible _ _).mpr (hc.1 p hp)
      obtain ⟨t,grows,legal,card⟩ :=
        Finset.exists_subsuperset_card_eq allowed hcard (capacity D hdeg b)
      refine ⟨t,(physicalCover_iff_union I.edges t).mp ⟨fun p hp => (mem_admissible _ _).mp (legal hp),?_⟩,card⟩
      intro e he
      obtain ⟨p,hp,hedge⟩ := hc.2 e he
      exact ⟨p,grows hp,hedge⟩
    · rintro ⟨s,he,hk⟩
      exact ⟨s,he,hk.le⟩
  exact pad.trans (distinct_reduction D hdeg b)

theorem size_bound (hdeg : D.boundedDegree) (b : ℕ) :
    (reduce D hdeg b).edges.card ≤ 8*(49*D.vertices.length + 1274*(D.edges.length*(2*D.vertices.length))) ∧
    (reduce D hdeg b).budget ≤ 4*(reduce D hdeg b).edges.card :=
  ⟨D.output_edges hdeg, (capacity D hdeg b).trans (admissible_card_le _)⟩

end GridCover.Shiota
