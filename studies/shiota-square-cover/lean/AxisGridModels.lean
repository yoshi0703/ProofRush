import AxisGridPlacement
import GridPlacementModels

namespace AxisGridSource.Drawing

open GridCover.Placement

variable {V : Type} [DecidableEq V] (D : Drawing V)

/-- The reduced source has maximum degree three and has no isolated vertices. -/
def boundedDegree : Prop := ∀ v ∈ D.vertices, 1 ≤ D.degree v ∧ D.degree v ≤ 3

theorem ports_at_original {v : V} (hv : v ∈ D.vertices) :
    portsOf D.coarseDrawing.shapeRuns (scalePoint (D.hub v)) = D.sourcePorts v := by
  ext d
  exact portsOf_spec.trans (D.sourcePorts_correct hv d).symm

omit [DecidableEq V] in
theorem ports_at_internal {e : V × V} (he : e ∈ D.edges) {p : Point} (hp : p ∈ D.inside e) :
    portsOf D.coarseDrawing.shapeRuns (scalePoint p) = {D.direction e, (D.direction e).opposite} := by
  ext d
  simpa only [Finset.mem_insert, Finset.mem_singleton] using portsOf_spec.trans (D.inside_ports he hp d)

theorem concrete_valid (hdeg : D.boundedDegree) :
    ∀ h ∈ D.coarseDrawing.shapeHubs,
      ValidPorts (D.switchAt h) (portsOf D.coarseDrawing.shapeRuns h) := by
  intro h hh
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hh
  have hp' : p ∈ D.occupied := List.mem_toFinset.mp hp
  rcases List.mem_append.mp hp' with hh | hi
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hh
    rw [D.ports_at_original hv,D.switchAt_hub hv]
    have hcard := D.sourcePorts_card v
    have hd := hdeg v hv
    refine ⟨Finset.card_pos.mp (by omega), ?_, by simp⟩
    intro he
    have hall : Direction.all.card = 4 := by decide
    rw [he] at hcard
    omega
  · obtain ⟨e,he,hi⟩ := List.mem_flatMap.mp hi
    rw [D.ports_at_internal he hi]
    cases hswitch : D.switchAt (scalePoint p) <;>
      cases haxis : D.axis e <;>
      simp only [direction,haxis,Direction.opposite] <;> decide

/-- The physically placed pitch-17 layout from a finite plane source drawing. -/
def certifiedLayout (hdeg : D.boundedDegree) : Layout :=
  D.coarseDrawing.concrete D.switchAt (D.concrete_valid hdeg)

theorem certifiedLayout_patches (hdeg : D.boundedDegree) :
    GridCover.HasCertifiedPatches (D.certifiedLayout hdeg).roles (D.certifiedLayout hdeg).links :=
  D.coarseDrawing.concrete_patches D.switchAt (D.concrete_valid hdeg)

theorem orientedPorts_tee_iff (k : Shape) (o : Orientation) :
    (orientedPorts k.ports o).card = 3 ↔ k = .tee := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases k <;> decide

theorem original_model_spec (hdeg : D.boundedDegree) {v : V} (hv : v ∈ D.vertices) :
    ∃ (k : Shape) (o : Orientation),
      (D.certifiedLayout hdeg).model (scalePoint (D.hub v)) =
        k.model o (scalePoint (D.hub v)) ∧
      orientedPorts k.ports o = D.sourcePorts v ∧
      (k = .tee ↔ D.degree v = 3) ∧ k ≠ .paritySwitch := by
  have hh : scalePoint (D.hub v) ∈ D.coarseDrawing.shapeHubs :=
    Finset.mem_image.mpr ⟨D.hub v,List.mem_toFinset.mpr
      (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨v,hv,rfl⟩))),rfl⟩
  have valid := D.concrete_valid hdeg _ hh
  obtain ⟨k,o,hmodel,hports,hswitch⟩ := selectModel_spec _ _ _ valid
  have hports' := hports.trans (D.ports_at_original hv)
  refine ⟨k,o,hmodel,hports',?_,?_⟩
  · have hh := orientedPorts_tee_iff k o
    rw [hports',D.sourcePorts_card] at hh
    exact hh.symm
  · rw [D.switchAt_hub hv] at hswitch
    simp at hswitch
    exact hswitch

def axisOrientation (e : V × V) : Orientation :=
  match D.axis e with
  | .east => ⟨false,false,false⟩
  | .north => ⟨true,false,false⟩

theorem inside_model_exact (hdeg : D.boundedDegree) {e : V × V} (he : e ∈ D.edges)
    {p : Point} (hp : p ∈ D.inside e) :
    (D.certifiedLayout hdeg).model (scalePoint p) =
      (if D.switchAt (scalePoint p) then Shape.paritySwitch else Shape.straight).model
        (D.axisOrientation e) (scalePoint p) := by
  change selectModel (D.switchAt (scalePoint p))
    (portsOf D.coarseDrawing.shapeRuns (scalePoint p)) (scalePoint p) = _
  rw [D.ports_at_internal he hp]
  cases hswitch : D.switchAt (scalePoint p) <;>
    cases ha : D.axis e <;> simp only [axisOrientation, direction, ha, Direction.opposite] <;> rfl

end AxisGridSource.Drawing
