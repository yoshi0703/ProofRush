import GridConcretePathJoin

namespace GridCover.PathEmbedding.Stride17

open GridCover.Placement
open scoped BigOperators

variable {V : Type} (D : AxisGridSource.Drawing V)

/-- Every atlas hub is either a scaled source vertex or a scaled strict interior site. -/
theorem shapeHub_cases {h : Center} (hh : h ∈ D.coarseDrawing.shapeHubs) :
    (∃ v ∈ D.vertices, scalePoint (D.hub v) = h) ∨
      ∃ e ∈ D.edges, ∃ i, 0 < i ∧ i < 2 * D.length e ∧ scalePoint (D.site e i) = h := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
  rcases D.occupied_cases (List.mem_toFinset.mp hx) with ⟨v,hv,rfl⟩ | ⟨e,he,i,hi,hil,rfl⟩
  · exact Or.inl ⟨v,hv,rfl⟩
  · exact Or.inr ⟨e,he,i,hi,hil,rfl⟩

/-- The only indexed sites at a source vertex are the appropriate endpoints of incident edges. -/
theorem sourceHub_site_iff {v : V} (hv : v ∈ D.vertices) {e : V × V} (he : e ∈ D.edges)
    {i : ℕ} (hi : i ≤ 2 * D.length e) :
    scalePoint (D.site e i) = scalePoint (D.hub v) ↔
      (i = 0 ∧ v = e.1) ∨ (i = 2 * D.length e ∧ v = e.2) := by
  constructor
  · intro h
    have eq := scalePoint_injective h
    by_cases h0 : i = 0
    · exact Or.inl ⟨h0, (D.hub_injective (by simpa only [h0, D.site_zero] using eq)).symm⟩
    by_cases hl : i = 2 * D.length e
    · exact Or.inr ⟨hl, (D.hub_injective (by simpa only [hl, D.site_last he] using eq)).symm⟩
    exact False.elim (D.inside_clear_hub he hv
      (D.mem_inside.mpr ⟨i, by omega, by omega, eq⟩))
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rw [D.site_zero]
    · rw [D.site_last he]

/-- Each strict interior atlas hub belongs to a unique edge at a unique index. -/
theorem interiorHub_site_iff {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges)
    {i j : ℕ} (hi : 0 < i) (hil : i < 2 * D.length e) (hj : j ≤ 2 * D.length f) :
    scalePoint (D.site f j) = scalePoint (D.site e i) ↔ f = e ∧ j = i := by
  constructor
  · intro h
    have eq := scalePoint_injective h
    have hint : D.site e i ∈ D.inside e := D.mem_inside.mpr ⟨i,hi,hil,rfl⟩
    have hfe := D.other_edge_cannot_contain_inside he hf hint hj eq.symm
    subst f
    exact ⟨rfl, D.site_injective e eq⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem sourceHub_contribution {v : V} (hv : v ∈ D.vertices)
    (P : (V × V) → ℕ → Prop) :
    (∃ e ∈ D.edges, ∃ i ≤ 2 * D.length e, scalePoint (D.site e i) = scalePoint (D.hub v) ∧ P e i) ↔
      ∃ e ∈ D.edges, (v = e.1 ∧ P e 0) ∨ (v = e.2 ∧ P e (2 * D.length e)) := by
  constructor
  · rintro ⟨e,he,i,hi,eq,hP⟩
    rcases (sourceHub_site_iff D hv he hi).mp eq with ⟨rfl, hv1⟩ | ⟨rfl,hv2⟩
    · exact ⟨e,he,Or.inl ⟨hv1,hP⟩⟩
    · exact ⟨e,he,Or.inr ⟨hv2,hP⟩⟩
  · rintro ⟨e,he,⟨hv1,hP⟩ | ⟨hv2,hP⟩⟩
    · exact ⟨e,he,0,by omega,(sourceHub_site_iff D hv he (by omega)).mpr (Or.inl ⟨rfl,hv1⟩),hP⟩
    · exact ⟨e,he,2 * D.length e,le_rfl,(sourceHub_site_iff D hv he le_rfl).mpr (Or.inr ⟨rfl,hv2⟩),hP⟩

theorem interiorHub_contribution {e : V × V} (he : e ∈ D.edges)
    {i : ℕ} (hi : 0 < i) (hil : i < 2 * D.length e) (P : (V × V) → ℕ → Prop) :
    (∃ f ∈ D.edges, ∃ j ≤ 2 * D.length f, scalePoint (D.site f j) = scalePoint (D.site e i) ∧ P f j) ↔ P e i := by
  constructor
  · rintro ⟨f,hf,j,hj,eq,hP⟩
    obtain ⟨rfl,rfl⟩ := (interiorHub_site_iff D he hf hi hil hj).mp eq
    exact hP
  · exact fun hP => ⟨e,he,i,by omega,rfl,hP⟩

variable [DecidableEq V]

/-- Original stencils are the union of the world arms of their incident edges. -/
structure OriginalCores (hdeg : D.boundedDegree) : Prop where
  points : ∀ v ∈ D.vertices, ∀ p,
    ((D.certifiedLayout hdeg).model (scalePoint (D.hub v))).CoreOptional p ↔
      ∃ e ∈ D.edges, (v = e.1 ∧ worldCorePoint D e 0 p) ∨
        (v = e.2 ∧ worldCorePoint D e (2 * D.length e) p)
  links : ∀ v ∈ D.vertices, ∀ p q,
    ((D.certifiedLayout hdeg).model (scalePoint (D.hub v))).CoreLink p q ↔
      ∃ e ∈ D.edges, (v = e.1 ∧ worldCoreLink D e 0 p q) ∨
        (v = e.2 ∧ worldCoreLink D e (2 * D.length e) p q)

/-- A strict interior stencil supplies exactly its single world core contribution. -/
structure InteriorCores (hdeg : D.boundedDegree) : Prop where
  points : ∀ e ∈ D.edges, ∀ i, 0 < i → i < 2 * D.length e → ∀ p,
    ((D.certifiedLayout hdeg).model (scalePoint (D.site e i))).CoreOptional p ↔ worldCorePoint D e i p
  links : ∀ e ∈ D.edges, ∀ i, 0 < i → i < 2 * D.length e → ∀ p q,
    ((D.certifiedLayout hdeg).model (scalePoint (D.site e i))).CoreLink p q ↔ worldCoreLink D e i p q

theorem allCores (hdeg : D.boundedDegree)
    (original : OriginalCores D hdeg) (interior : InteriorCores D hdeg) :
    CoreMatches D hdeg where
  points h hh p := by
    rcases shapeHub_cases D hh with ⟨v,hv,rfl⟩ | ⟨e,he,i,hi,hil,rfl⟩
    · exact (original.points v hv p).trans
        (sourceHub_contribution D hv (fun e i => worldCorePoint D e i p)).symm
    · exact (interior.points e he i hi hil p).trans
        (interiorHub_contribution D he hi hil (fun e i => worldCorePoint D e i p)).symm
  links h hh p q := by
    rcases shapeHub_cases D hh with ⟨v,hv,rfl⟩ | ⟨e,he,i,hi,hil,rfl⟩
    · exact (original.links v hv p q).trans
        (sourceHub_contribution D hv (fun e i => worldCoreLink D e i p q)).symm
    · exact (interior.links e he i hi hil p q).trans
        (interiorHub_contribution D he hi hil (fun e i => worldCoreLink D e i p q)).symm

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.allCores
