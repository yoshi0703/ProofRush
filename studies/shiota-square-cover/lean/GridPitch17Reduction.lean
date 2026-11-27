import GridOriginalCoreJoin
import AxisGridCorePieces

namespace GridCover.PathEmbedding.Stride17

open GridCover.Placement
open scoped BigOperators

variable {V : Type} [DecidableEq V] (D : AxisGridSource.Drawing V)

theorem pitch17_core_matches (hdeg : D.boundedDegree) : CoreMatches D hdeg := by
  apply allCores D hdeg
  · apply originalCores D hdeg
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e he p
      apply AxisGridSourceCore.leftPoint
      exact he
    · intro e he p
      apply AxisGridSourceCore.rightPoint
      exact he
    · intro e he p q
      apply AxisGridSourceCore.leftLink
      exact he
    · intro e he p q
      apply AxisGridSourceCore.rightLink
      exact he
  · refine ⟨?_, ?_⟩
    · intro e he i hi hil p
      apply AxisGridSourceCore.interiorPoint <;> assumption
    · intro e he i hi hil p q
      apply AxisGridSourceCore.interiorLink <;> assumption

/-- The supplied finite plane drawing reduces to the exact constructed square cover instance. -/
theorem pitch17_exact_cover (hdeg : D.boundedDegree) (b : ℕ) :
    let A := D.certifiedLayout hdeg
    let F := embedded D (leftTee D) (rightTee D) (fun _ => false)
    (∃ s : Finset Center, physicalCover (seedEdges (A.guardSet ∪ A.optionalSet)) s ∧
        s.card = min (A.guardSet ∪ A.optionalSet).card ((A.guardSet.card + (∑ e ∈ F.edges, F.t e)) + b)) ↔
      (∃ s : Finset V, OddPath.vertexCover D.edges.toFinset s ∧ s.card ≤ b) :=
  concrete_exact_cover D hdeg (pitch17_core_matches D hdeg) b

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.pitch17_core_matches
#print axioms GridCover.PathEmbedding.Stride17.pitch17_exact_cover
