import GridSourcePaths
import AxisGridPlacement

namespace GridCover.PathEmbedding.Stride17
open GridCover.Placement

variable {V : Type} [DecidableEq V]
variable (D : AxisGridSource.Drawing V)

/-- An original vertex occurs as a route endpoint. This excludes isolated
vertices, which do not change the source vertex-cover optimum. -/
def NoIsolated : Prop :=
  ∀ v ∈ D.vertices, ∃ e ∈ D.edges, AxisGridSource.Ends v e

def routedPoint (leftTee rightTee reverse : (V × V) → Bool)
    (e : V × V) (p : Center) : Prop :=
  p = hubPoint D e.1 ∨ p ∈ sourceInside D leftTee rightTee reverse e ∨ p = hubPoint D e.2

def routedLink (leftTee rightTee reverse : (V × V) → Bool)
    (e : V × V) (p q : Center) : Prop :=
  (p,q) ∈ pairs (hubPoint D e.1) (sourceInside D leftTee rightTee reverse e) (hubPoint D e.2) ∨
  (q,p) ∈ pairs (hubPoint D e.1) (sourceInside D leftTee rightTee reverse e) (hubPoint D e.2)

theorem allPoints_iff (noIso : NoIsolated D) (leftTee rightTee reverse : (V × V) → Bool)
    (p : Center) :
    p ∈ (embedded D leftTee rightTee reverse).points ↔
      ∃ e ∈ D.edges, routedPoint D leftTee rightTee reverse e p := by
  change p ∈ D.vertices.toFinset.map ⟨hubPoint D, _⟩ ∪
    D.edges.toFinset.biUnion (fun e => (sourceInside D leftTee rightTee reverse e).toFinset) ↔ _
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with h | h
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp h
      obtain ⟨e,he,hve⟩ := noIso v (List.mem_toFinset.mp hv)
      rcases hve with hv | hv
      · exact ⟨e,he,Or.inl (congrArg (hubPoint D) hv)⟩
      · exact ⟨e,he,Or.inr (Or.inr (congrArg (hubPoint D) hv))⟩
    · obtain ⟨e,he,hi⟩ := Finset.mem_biUnion.mp h
      exact ⟨e,List.mem_toFinset.mp he,Or.inr (Or.inl (List.mem_toFinset.mp hi))⟩
  · rintro ⟨e,he,h | h | h⟩
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr
        ⟨e.1,List.mem_toFinset.mpr (D.edge_endpoints e he).1,h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e,List.mem_toFinset.mpr he,List.mem_toFinset.mpr h⟩)
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr
        ⟨e.2,List.mem_toFinset.mpr (D.edge_endpoints e he).2,h.symm⟩)

theorem allLinks_iff (leftTee rightTee reverse : (V × V) → Bool) (p q : Center) :
    ((p,q) ∈ (embedded D leftTee rightTee reverse).allPairs ∨
      (q,p) ∈ (embedded D leftTee rightTee reverse).allPairs) ↔
      ∃ e ∈ D.edges, routedLink D leftTee rightTee reverse e p q := by
  simp only [Embedded.allPairs, embedded, Finset.mem_biUnion, List.mem_toFinset, routedLink]
  constructor
  · rintro (⟨e,he,h⟩ | ⟨e,he,h⟩)
    · exact ⟨e,he,Or.inl h⟩
    · exact ⟨e,he,Or.inr h⟩
  · rintro ⟨e,he,h | h⟩
    · exact Or.inl ⟨e,he,h⟩
    · exact Or.inr ⟨e,he,h⟩

omit [DecidableEq V] in
theorem pairs_map {P Q : Type*} (f : P → Q) (a : P) (xs : List P) (b : P) :
    pairs (f a) (xs.map f) (f b) = (pairs a xs b).map (fun (p,q) => (f p,f q)) := by
  induction xs generalizing a <;> simp [pairs, *]

abbrev unplace (e : V × V) : Center ≃ Center :=
  (world (sourceDir D e) (hubPoint D e.1)).symm

omit [DecidableEq V] in
theorem unplace_start (e : V × V) :
    unplace D e (hubPoint D e.1) = (0,0) := by
  apply (world (sourceDir D e) (hubPoint D e.1)).injective
  simp

omit [DecidableEq V] in
theorem unplace_end {e : V × V} (he : e ∈ D.edges) :
    unplace D e (hubPoint D e.2) = (34 * (D.length e : ℤ),0) := by
  apply (world (sourceDir D e) (hubPoint D e.1)).injective
  simpa using (end_hub D he).symm

omit [DecidableEq V] in
theorem routedPoint_local (leftTee rightTee reverse : (V × V) → Bool)
    {e : V × V} (he : e ∈ D.edges) (p : Center) :
    routedPoint D leftTee rightTee reverse e p ↔
      unplace D e p ∈ (0,0) :: internal (D.length e) (leftTee e) (rightTee e) (reverse e) ++
        [(34 * (D.length e : ℤ),0)] := by
  have world_mem (u : Center) :
      world (sourceDir D e) (hubPoint D e.1) u = p ↔ u = unplace D e p := by
    constructor
    · intro h
      simpa [unplace] using congrArg (unplace D e) h
    · intro h
      simpa [unplace] using congrArg (world (sourceDir D e) (hubPoint D e.1)) h
  have start : p = hubPoint D e.1 ↔ unplace D e p = (0,0) := by
    rw [← unplace_start D e]
    exact (unplace D e).injective.eq_iff.symm
  have end_at : p = hubPoint D e.2 ↔ unplace D e p = (34 * (D.length e : ℤ),0) := by
    rw [← unplace_end D he]
    exact (unplace D e).injective.eq_iff.symm
  simp [routedPoint, sourceInside, placedInternal, List.mem_map, world_mem, start, end_at]

omit [DecidableEq V] in
theorem routedLink_local (leftTee rightTee reverse : (V × V) → Bool)
    {e : V × V} (he : e ∈ D.edges) (p q : Center) :
    routedLink D leftTee rightTee reverse e p q ↔
      let middle := internal (D.length e) (leftTee e) (rightTee e) (reverse e)
      let last := ((34 * (D.length e : ℤ),0) : Center)
      (unplace D e p, unplace D e q) ∈ pairs (0,0) middle last ∨
      (unplace D e q, unplace D e p) ∈ pairs (0,0) middle last := by
  let w := world (sourceDir D e) (hubPoint D e.1)
  have ha : w (0,0) = hubPoint D e.1 := by simp [w]
  have hb : w (34 * (D.length e : ℤ),0) = hubPoint D e.2 := by
    simp [w, end_hub D he]
  have pair_mem (a b : Center) (xs : List (Center × Center)) :
      (a,b) ∈ xs.map (fun (p,q) => (w p,w q)) ↔ (unplace D e a, unplace D e b) ∈ xs := by
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨u,v⟩,hm,h⟩
      have hu := congrArg (fun e : Center × Center => w.symm e.1) h
      have hv := congrArg (fun e : Center × Center => w.symm e.2) h
      simp [w] at hu hv
      simpa [unplace, ← hu, ← hv] using hm
    · intro h
      exact ⟨_,h,by change (w (w.symm a),w (w.symm b)) = (a,b); simp⟩
  have eq := pairs_map (⇑w) ((0,0) : Center)
    (internal (D.length e) (leftTee e) (rightTee e) (reverse e))
    ((34 * (D.length e : ℤ),0) : Center)
  rw [ha, hb] at eq
  unfold routedLink sourceInside placedInternal
  rw [eq]
  exact or_congr (pair_mem _ _ _) (pair_mem _ _ _)

omit [DecidableEq V] in
theorem run_frame (e : V × V) (i : ℕ) (p : Center) :
    (D.runAt e i).scaled.alongAt p = (unplace D e p).1 - 17 * (i : ℤ) ∧
    (D.runAt e i).scaled.acrossAt p = (unplace D e p).2 := by
  change _ = (((sourceDir D e).localFrame (hubPoint D e.1)).point p).1 - _ ∧
    _ = (((sourceDir D e).localFrame (hubPoint D e.1)).point p).2
  simp only [Direction.frame_at]
  unfold AxisGridSource.Drawing.runAt AxisGridSource.Drawing.site AxisGridSource.site
  unfold AxisGridSource.Drawing.direction AxisGridSource.Drawing.axis
  unfold sourceDir hubPoint AxisGridSource.Drawing.hub
  cases hd : AxisGridSource.axis (D.coordinate e.1) (D.coordinate e.2) <;>
    simp [AxisGridSource.Drawing.axis, hd, toDir, Run.scaled, Run.alongAt, Run.acrossAt, Direction.longitudinal,
      Direction.lateral, AxisGridSource.advance, scalePoint, pitch, sub] <;>
    omega

omit [DecidableEq V] in
theorem run_optional_world (e : V × V) (i : ℕ) (p : Center) :
    (D.runAt e i).scaled.Optional p ↔
      17 * (i : ℤ) + 4 ≤ (unplace D e p).1 ∧
      (unplace D e p).1 ≤ 17 * (i : ℤ) + 13 ∧ (unplace D e p).2 = 0 := by
  unfold Run.Optional
  rw [(run_frame D e i p).1, (run_frame D e i p).2]
  change (_ ∧ _ ≤ 17 - 4 ∧ _) ↔ _
  omega

omit [DecidableEq V] in
theorem run_link_world (e : V × V) (i : ℕ) (p q : Center) :
    (D.runAt e i).scaled.Link p q ↔
      (17 * (i : ℤ) + 3 ≤ (unplace D e p).1 ∧ (unplace D e p).1 ≤ 17 * (i : ℤ) + 14 ∧
        (unplace D e p).2 = 0) ∧
      (17 * (i : ℤ) + 3 ≤ (unplace D e q).1 ∧ (unplace D e q).1 ≤ 17 * (i : ℤ) + 14 ∧
        (unplace D e q).2 = 0) ∧ unitApart (unplace D e p).1 (unplace D e q).1 := by
  simp only [Run.Link, (run_frame D e i p).1, (run_frame D e i p).2,
    (run_frame D e i q).1, (run_frame D e i q).2, unitApart]
  change ((_ ∧ _ ≤ 17 - 3 ∧ _) ∧ (_ ∧ _ ≤ 17 - 3 ∧ _) ∧ _) ↔ _
  omega

variable (models : ∀ h : Center, ModelAt h)
variable (port : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ d,
  d ∈ (models h).ports ↔ Outward D.coarseDrawing.shapeRuns h d)

def pathAtlas : Placement.Layout := D.coarseDrawing.assemble models port

omit [DecidableEq V] in
theorem mem_shapeRuns_iff {s : Run} :
    s ∈ D.coarseDrawing.shapeRuns ↔
      ∃ e ∈ D.edges, ∃ i < 2 * D.length e, (D.runAt e i).scaled = s := by
  constructor
  · intro hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨e,he,i,hi,rfl⟩ := D.mem_coarseRuns.mp hr
    exact ⟨e,he,i,hi,rfl⟩
  · rintro ⟨e,he,i,hi,rfl⟩
    exact Finset.mem_image.mpr ⟨D.runAt e i,D.mem_coarseRuns.mpr ⟨e,he,i,hi,rfl⟩,rfl⟩

omit [DecidableEq V] in
theorem site_is_atlasHub {e : V × V} (he : e ∈ D.edges) {i : ℕ}
    (hi : i ≤ 2 * D.length e) :
    scalePoint (D.site e i) ∈ D.coarseDrawing.shapeHubs :=
  Finset.mem_image.mpr ⟨_,List.mem_toFinset.mpr (D.site_mem_occupied he hi),rfl⟩

/-- The per-route topological decomposition and local core decomposition are
separate obligations. A source hub's core may contribute to several source
edges, each via its own arm. A private waypoint contributes to just its edge. -/
structure Pieces (leftTee rightTee reverse : (V × V) → Bool) where
  corePoint : (V × V) → ℕ → Center → Prop
  coreLink : (V × V) → ℕ → Center → Center → Prop
  pointAtHub : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ p, (models h).CoreOptional p ↔
    ∃ e ∈ D.edges, ∃ i ≤ 2 * D.length e, scalePoint (D.site e i) = h ∧ corePoint e i p
  linkAtHub : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ p q, (models h).CoreLink p q ↔
    ∃ e ∈ D.edges, ∃ i ≤ 2 * D.length e, scalePoint (D.site e i) = h ∧ coreLink e i p q
  pointOnRoute : ∀ e ∈ D.edges, ∀ p, routedPoint D leftTee rightTee reverse e p ↔
    (∃ i ≤ 2 * D.length e, corePoint e i p) ∨
    ∃ i < 2 * D.length e, (D.runAt e i).scaled.Optional p
  linkOnRoute : ∀ e ∈ D.edges, ∀ p q, routedLink D leftTee rightTee reverse e p q ↔
    (∃ i ≤ 2 * D.length e, coreLink e i p q) ∨
    ∃ i < 2 * D.length e, (D.runAt e i).scaled.Link p q

theorem atlasOptional_iff (noIso : NoIsolated D)
    {leftTee rightTee reverse : (V × V) → Bool}
    (B : Pieces D models leftTee rightTee reverse) (p : Center) :
    (pathAtlas D models port).IsOptional p ↔ p ∈ (embedded D leftTee rightTee reverse).points := by
  rw [allPoints_iff D noIso]
  change ((∃ h ∈ D.coarseDrawing.shapeHubs, (models h).CoreOptional p) ∨
    ∃ s ∈ D.coarseDrawing.shapeRuns, s.Optional p) ↔ _
  constructor
  · rintro (⟨h,hh,hp⟩ | ⟨s,hs,hp⟩)
    · obtain ⟨e,he,i,hi,_,hv⟩ := (B.pointAtHub h hh p).mp hp
      exact ⟨e,he,(B.pointOnRoute e he p).mpr (Or.inl ⟨i,hi,hv⟩)⟩
    · obtain ⟨e,he,i,hi,rfl⟩ := (mem_shapeRuns_iff D).mp hs
      exact ⟨e,he,(B.pointOnRoute e he p).mpr (Or.inr ⟨i,hi,hp⟩)⟩
  · rintro ⟨e,he,hp⟩
    rcases (B.pointOnRoute e he p).mp hp with ⟨i,hi,hv⟩ | ⟨i,hi,hv⟩
    · have hm := site_is_atlasHub D he hi
      exact Or.inl ⟨_,hm,(B.pointAtHub _ hm p).mpr ⟨e,he,i,hi,rfl,hv⟩⟩
    · exact Or.inr ⟨_,(mem_shapeRuns_iff D).mpr ⟨e,he,i,hi,rfl⟩,hv⟩

theorem atlasLink_iff {leftTee rightTee reverse : (V × V) → Bool}
    (B : Pieces D models leftTee rightTee reverse) (p q : Center) :
    (pathAtlas D models port).IsLink p q ↔
      ((p,q) ∈ (embedded D leftTee rightTee reverse).allPairs ∨
       (q,p) ∈ (embedded D leftTee rightTee reverse).allPairs) := by
  rw [allLinks_iff D]
  change ((∃ h ∈ D.coarseDrawing.shapeHubs, (models h).CoreLink p q) ∨
    ∃ s ∈ D.coarseDrawing.shapeRuns, s.Link p q) ↔ _
  constructor
  · rintro (⟨h,hh,hp⟩ | ⟨s,hs,hp⟩)
    · obtain ⟨e,he,i,hi,_,hv⟩ := (B.linkAtHub h hh p q).mp hp
      exact ⟨e,he,(B.linkOnRoute e he p q).mpr (Or.inl ⟨i,hi,hv⟩)⟩
    · obtain ⟨e,he,i,hi,rfl⟩ := (mem_shapeRuns_iff D).mp hs
      exact ⟨e,he,(B.linkOnRoute e he p q).mpr (Or.inr ⟨i,hi,hp⟩)⟩
  · rintro ⟨e,he,hp⟩
    rcases (B.linkOnRoute e he p q).mp hp with ⟨i,hi,hv⟩ | ⟨i,hi,hv⟩
    · have hm := site_is_atlasHub D he hi
      exact Or.inl ⟨_,hm,(B.linkAtHub _ hm p q).mpr ⟨e,he,i,hi,rfl,hv⟩⟩
    · exact Or.inr ⟨_,(mem_shapeRuns_iff D).mpr ⟨e,he,i,hi,rfl⟩,hv⟩

theorem atlas_represents (noIso : NoIsolated D)
    {leftTee rightTee reverse : (V × V) → Bool}
    (B : Pieces D models leftTee rightTee reverse)
    (guards optional : Finset Center) (required : Finset GridEdge) (graph : Finset (Center × Center))
    (opt : ∀ p, p ∈ optional ↔ (pathAtlas D models port).IsOptional p)
    (links : ∀ p q, ((p,q) ∈ graph ∨ (q,p) ∈ graph) ↔ (pathAtlas D models port).IsLink p q) :
    (embedded D leftTee rightTee reverse).represents (gridLayout guards optional required graph) := by
  constructor
  · intro p hp
    exact (opt p).mpr ((atlasOptional_iff D models port noIso B p).mpr hp)
  · intro p q
    exact (links p q).trans (atlasLink_iff D models port B p q)

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.atlas_represents
