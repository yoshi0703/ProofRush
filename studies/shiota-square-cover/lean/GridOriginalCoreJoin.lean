import GridAllCores
import GridStarIncidence

namespace GridCover.PathEmbedding.Stride17

open GridCover.LocalCore GridCover.Placement

variable {V : Type} [DecidableEq V] (D : AxisGridSource.Drawing V)

theorem starPort_contribution {v : V} (hv : v ∈ D.vertices)
    (Q : Direction → Prop) (P : (V × V) → ℕ → Prop)
    (left : ∀ e ∈ D.edges, v = e.1 → (Q (D.direction e) ↔ P e 0))
    (right : ∀ e ∈ D.edges, v = e.2 →
      (Q (D.direction e).opposite ↔ P e (2 * D.length e))) :
    (∃ d ∈ D.sourcePorts v, Q d) ↔
      ∃ e ∈ D.edges, (v = e.1 ∧ P e 0) ∨
        (v = e.2 ∧ P e (2 * D.length e)) := by
  constructor
  · rintro ⟨d,hd,hQ⟩
    obtain ⟨e,he,⟨hv1,rfl⟩ | ⟨hv2,rfl⟩⟩ :=
      (D.source_hub_ports hv d).mp ((D.sourcePorts_correct hv d).mp hd)
    · exact ⟨e,he,Or.inl ⟨hv1,(left e he hv1).mp hQ⟩⟩
    · exact ⟨e,he,Or.inr ⟨hv2,(right e he hv2).mp hQ⟩⟩
  · rintro ⟨e,he,⟨hv1,hP⟩ | ⟨hv2,hP⟩⟩
    · exact ⟨D.direction e, (D.sourcePorts_correct hv _).mpr
        ((D.source_hub_ports hv _).mpr ⟨e,he,Or.inl ⟨hv1,rfl⟩⟩), (left e he hv1).mpr hP⟩
    · exact ⟨(D.direction e).opposite, (D.sourcePorts_correct hv _).mpr
        ((D.source_hub_ports hv _).mpr ⟨e,he,Or.inr ⟨hv2,rfl⟩⟩), (right e he hv2).mpr hP⟩

/-- Identifies the four local comparisons needed for endpoint arms before atlas assembly. -/
structure EndpointArms : Prop where
  leftPoint : ∀ e ∈ D.edges, ∀ p,
    p ∈ armAt (scalePoint (D.hub e.1)) (D.direction e) (leftTee D e) ↔ worldCorePoint D e 0 p
  rightPoint : ∀ e ∈ D.edges, ∀ p,
    p ∈ armAt (scalePoint (D.hub e.2)) (D.direction e).opposite (rightTee D e) ↔
      worldCorePoint D e (2 * D.length e) p
  leftLink : ∀ e ∈ D.edges, ∀ p q,
    armPair (scalePoint (D.hub e.1)) (D.direction e) (leftTee D e) p q ↔ worldCoreLink D e 0 p q
  rightLink : ∀ e ∈ D.edges, ∀ p q,
    armPair (scalePoint (D.hub e.2)) (D.direction e).opposite (rightTee D e) p q ↔
      worldCoreLink D e (2 * D.length e) p q

theorem originalCores (hdeg : D.boundedDegree) (arms : EndpointArms D) :
    OriginalCores D hdeg where
  points v hv p := by
    obtain ⟨k,o,hmod,hports,htee,hne⟩ := D.original_model_spec hdeg hv
    rw [hmod,normal_corePoint hne,hports]
    have hbit : decide (k = .tee) = decide (D.degree v = 3) := by simp only [htee]
    rw [hbit]
    apply starPort_contribution D hv
      (fun d => p ∈ armAt (scalePoint (D.hub v)) d (decide (D.degree v = 3)))
      (fun e i => worldCorePoint D e i p)
    · rintro e he rfl
      exact arms.leftPoint e he p
    · rintro e he rfl
      exact arms.rightPoint e he p
  links v hv p q := by
    obtain ⟨k,o,hmod,hports,htee,hne⟩ := D.original_model_spec hdeg hv
    rw [hmod,normal_coreLink hne,hports]
    have hbit : decide (k = .tee) = decide (D.degree v = 3) := by simp only [htee]
    rw [hbit]
    apply starPort_contribution D hv
      (fun d => armPair (scalePoint (D.hub v)) d (decide (D.degree v = 3)) p q)
      (fun e i => worldCoreLink D e i p q)
    · rintro e he rfl
      exact arms.leftLink e he p q
    · rintro e he rfl
      exact arms.rightLink e he p q

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.originalCores
