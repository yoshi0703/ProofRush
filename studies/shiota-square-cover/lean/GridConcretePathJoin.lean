import GridPathAtlasJoin
import AxisGridModels
import GridPlacementFinite
import GridAxisPieces

namespace GridCover.PathEmbedding.Stride17

open GridCover.Placement
open scoped BigOperators

variable {V : Type} [DecidableEq V] (D : AxisGridSource.Drawing V)

def leftTee (e : V × V) : Bool := decide (D.degree e.1 = 3)
def rightTee (e : V × V) : Bool := decide (D.degree e.2 = 3)

def worldCorePoint (e : V × V) (i : ℕ) (p : Center) : Prop :=
  AxisPieces.corePoint (D.length e) (leftTee D e) (rightTee D e) i (unplace D e p)

def worldCoreLink (e : V × V) (i : ℕ) (p q : Center) : Prop :=
  AxisPieces.coreLink (D.length e) (leftTee D e) (rightTee D e) i (unplace D e p) (unplace D e q) ∨
  AxisPieces.coreLink (D.length e) (leftTee D e) (rightTee D e) i (unplace D e q) (unplace D e p)

omit [DecidableEq V] in
theorem stripPoint_world (e : V × V) (i : ℕ) (p : Center) :
    AxisPieces.stripPoint i (unplace D e p) ↔ (D.runAt e i).scaled.Optional p := by
  rw [run_optional_world D]
  unfold AxisPieces.stripPoint
  constructor
  · rintro ⟨k,lo,hi,eq⟩
    rw [eq]
    change 17 * (i : ℤ) + 4 ≤ (k : ℤ) ∧ (k : ℤ) ≤ 17 * (i : ℤ) + 13 ∧ (0 : ℤ) = 0
    exact ⟨by omega, by omega, rfl⟩
  · rintro ⟨lo,hi,eq⟩
    let x := (unplace D e p).1
    have h : (x.toNat : ℤ) = x := Int.toNat_of_nonneg (by dsimp [x]; omega)
    refine ⟨x.toNat, by dsimp [x] at h; omega, by dsimp [x] at h; omega, ?_⟩
    exact Prod.ext h.symm eq

omit [DecidableEq V] in
theorem stripLink_world (e : V × V) (i : ℕ) (p q : Center) :
    (AxisPieces.stripLink i (unplace D e p) (unplace D e q) ∨
      AxisPieces.stripLink i (unplace D e q) (unplace D e p)) ↔
        (D.runAt e i).scaled.Link p q := by
  rw [run_link_world D]
  have one_way (s t : Center) :
      AxisPieces.stripLink i s t ↔
        (17 * (i : ℤ) + 3 ≤ s.1 ∧ s.1 ≤ 17 * (i : ℤ) + 13 ∧ s.2 = 0) ∧
          t.1 = s.1 + 1 ∧ t.2 = 0 := by
    unfold AxisPieces.stripLink
    constructor
    · rintro ⟨k,lo,hi,rfl,rfl⟩
      change (17 * (i : ℤ) + 3 ≤ (k : ℤ) ∧ (k : ℤ) ≤ 17 * (i : ℤ) + 13 ∧
          (0 : ℤ) = 0) ∧ ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 ∧ (0 : ℤ) = 0
      exact ⟨⟨by omega, by omega, rfl⟩, by simp, rfl⟩
    · rintro ⟨⟨lo,hi,sz⟩,tstep,tz⟩
      have h : (s.1.toNat : ℤ) = s.1 := Int.toNat_of_nonneg (by omega)
      refine ⟨s.1.toNat, by omega, by omega, Prod.ext h.symm sz, ?_⟩
      apply Prod.ext
      · simp only [AxisPieces.row, Nat.cast_add, Nat.cast_one, h, tstep]
      · exact tz
  rw [one_way, one_way]
  unfold unitApart
  omega

theorem concretePointOnRoute {e : V × V} (he : e ∈ D.edges) (p : Center) :
    routedPoint D (leftTee D) (rightTee D) (fun _ => false) e p ↔
      (∃ i ≤ 2 * D.length e, worldCorePoint D e i p) ∨
      ∃ i < 2 * D.length e, (D.runAt e i).scaled.Optional p := by
  rw [routedPoint_local D _ _ _ he]
  have equal :
      (unplace D e p ∈ (0, 0) :: internal (D.length e) (leftTee D e) (rightTee D e) false ++
        [(34 * (D.length e : ℤ), 0)]) =
      (unplace D e p ∈ AxisPieces.full (D.length e) (leftTee D e) (rightTee D e)) := by
    simp [AxisPieces.full, AxisPieces.row]
  rw [equal, AxisPieces.point_pieces_iff (D.length_pos he)]
  simp only [worldCorePoint, stripPoint_world D]

theorem concreteLinkOnRoute {e : V × V} (he : e ∈ D.edges) (p q : Center) :
    routedLink D (leftTee D) (rightTee D) (fun _ => false) e p q ↔
      (∃ i ≤ 2 * D.length e, worldCoreLink D e i p q) ∨
      ∃ i < 2 * D.length e, (D.runAt e i).scaled.Link p q := by
  rw [routedLink_local D _ _ _ he]
  dsimp
  have localIff (p q : Center) :=
    AxisPieces.link_pieces_iff (D.length_pos he) (leftTee D e) (rightTee D e) p q
  simp only [AxisPieces.row, Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat] at localIff
  rw [localIff, localIff]
  constructor
  · rintro ((⟨i,hi,h⟩ | ⟨i,hi,h⟩) | (⟨i,hi,h⟩ | ⟨i,hi,h⟩))
    · exact Or.inl ⟨i,hi,Or.inl h⟩
    · exact Or.inr ⟨i,hi,(stripLink_world D e i p q).mp (Or.inl h)⟩
    · exact Or.inl ⟨i,hi,Or.inr h⟩
    · exact Or.inr ⟨i,hi,(stripLink_world D e i p q).mp (Or.inr h)⟩
  · rintro (⟨i,hi,h | h⟩ | ⟨i,hi,h⟩)
    · exact Or.inl (Or.inl ⟨i,hi,h⟩)
    · exact Or.inr (Or.inl ⟨i,hi,h⟩)
    · rcases (stripLink_world D e i p q).mpr h with hl | hr
      · exact Or.inl (Or.inr ⟨i,hi,hl⟩)
      · exact Or.inr (Or.inr ⟨i,hi,hr⟩)

structure CoreMatches (hdeg : D.boundedDegree) : Prop where
  points : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ p,
    ((D.certifiedLayout hdeg).model h).CoreOptional p ↔
      ∃ e ∈ D.edges, ∃ i ≤ 2 * D.length e, scalePoint (D.site e i) = h ∧ worldCorePoint D e i p
  links : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ p q,
    ((D.certifiedLayout hdeg).model h).CoreLink p q ↔
      ∃ e ∈ D.edges, ∃ i ≤ 2 * D.length e, scalePoint (D.site e i) = h ∧ worldCoreLink D e i p q

def concretePieces (hdeg : D.boundedDegree) (cores : CoreMatches D hdeg) :
    Pieces D (D.certifiedLayout hdeg).model (leftTee D) (rightTee D) (fun _ => false) where
  corePoint := worldCorePoint D
  coreLink := worldCoreLink D
  pointAtHub := cores.points
  linkAtHub := cores.links
  pointOnRoute := fun _ he => concretePointOnRoute D he
  linkOnRoute := fun _ he => concreteLinkOnRoute D he

theorem boundedDegree_noIsolated (hdeg : D.boundedDegree) : NoIsolated D := by
  intro v hv
  have hp : 0 < (D.incidentEdges v).card := (hdeg v hv).1
  obtain ⟨e,he⟩ := Finset.card_pos.mp hp
  obtain ⟨hm,hi⟩ := D.mem_incidentEdges.mp he
  exact ⟨e,hm,hi⟩

theorem concrete_atlas_represents (hdeg : D.boundedDegree)
    (cores : CoreMatches D hdeg) :
    let A := D.certifiedLayout hdeg
    (embedded D (leftTee D) (rightTee D) (fun _ => false)).represents
      (gridLayout A.guardSet A.optionalSet (seedEdges (A.guardSet ∪ A.optionalSet)) A.linkSet) := by
  let A := D.certifiedLayout hdeg
  have port : ∀ h ∈ D.coarseDrawing.shapeHubs, ∀ d,
      d ∈ (A.model h).ports ↔ Outward D.coarseDrawing.shapeRuns h d := A.port
  have pointwise : ∀ p, p ∈ A.optionalSet ↔ (pathAtlas D A.model port).IsOptional p :=
    A.mem_optional_iff
  have edgelinks : ∀ p q, ((p,q) ∈ A.linkSet ∨ (q,p) ∈ A.linkSet) ↔
      (pathAtlas D A.model port).IsLink p q := by
    intro p q
    simp only [A.mem_linkSet]
    exact ⟨fun h => h.elim id A.link_comm, Or.inl⟩
  exact atlas_represents D A.model port (boundedDegree_noIsolated D hdeg)
    (concretePieces D hdeg cores) _ _ _ _ pointwise edgelinks

theorem concrete_exact_cover (hdeg : D.boundedDegree)
    (cores : CoreMatches D hdeg) (b : ℕ) :
    let A := D.certifiedLayout hdeg
    let F := embedded D (leftTee D) (rightTee D) (fun _ => false)
    (∃ s : Finset Center, physicalCover (seedEdges (A.guardSet ∪ A.optionalSet)) s ∧
        s.card = min (A.guardSet ∪ A.optionalSet).card ((A.guardSet.card + (∑ e ∈ F.edges, F.t e)) + b)) ↔
      (∃ s : Finset V, OddPath.vertexCover D.edges.toFinset s ∧ s.card ≤ b) := by
  let A := D.certifiedLayout hdeg
  exact Embedded.assembled_path_budget_iff (embedded D (leftTee D) (rightTee D) (fun _ => false))
    A.guard_optional_disjoint A.finite_graph_ok A.finite_patches
    (concrete_atlas_represents D hdeg cores) b

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.concrete_exact_cover
