import AxisGridModels
import GridPlacementSize

namespace AxisGridSource.Drawing

open GridCover GridCover.Placement

variable {V : Type} [DecidableEq V] (D : Drawing V)

omit [DecidableEq V] in
theorem coarse_hub_count :
    D.coarseDrawing.hubs.card ≤ D.vertices.length + D.edges.length*(2*D.vertices.length) := by
  change D.occupied.toFinset.card ≤ _
  apply (List.toFinset_card_le _).trans
  simpa [occupied] using Nat.add_le_add_left D.routes_size_bound D.vertices.length

omit [DecidableEq V] in
theorem coarse_run_count :
    D.coarseDrawing.runs.card ≤ D.edges.length*(2*D.vertices.length) := by
  change (D.edges.flatMap D.edgeRuns).toFinset.card ≤ _
  apply (List.toFinset_card_le _).trans
  generalize he : D.edges = es
  have bound : ∀ e ∈ es, (D.edgeRuns e).length ≤ 2*D.vertices.length := by
    intro e hx
    rw [D.edgeRuns_length]
    have hh := D.length_bound (e:=e) (he ▸ hx)
    omega
  clear he
  induction es with
  | nil => simp
  | cons a es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    have h1 := bound a List.mem_cons_self
    have h2 := ih fun e hm => bound e (List.mem_cons_of_mem a hm)
    omega

omit [DecidableEq V] in
theorem coarse_coordinates (p : Center) (hp : p ∈ D.coarseDrawing.hubs) :
    nearby (2*D.vertices.length) (0,0) p := by
  change p ∈ D.occupied.toFinset at hp
  rcases List.mem_append.mp (List.mem_toFinset.mp hp) with original | interior
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp original
    have h := D.coordinates_bounded v hv
    simp only [hub, double, nearby] at *
    omega
  · obtain ⟨e,he,hi⟩ := List.mem_flatMap.mp interior
    obtain ⟨i,_,bound,rfl⟩ := D.mem_inside.mp hi
    have hspan := D.site_span he (Nat.le_of_lt bound)
    obtain ⟨ha,hb⟩ := D.edge_endpoints e he
    have ca := D.coordinates_bounded e.1 ha
    have cb := D.coordinates_bounded e.2 hb
    unfold fineSpan span hub double at hspan
    unfold nearby
    dsimp only at *
    omega

private theorem numeric_bound {h r n m : ℕ} (hh : h ≤ n + m*(2*n)) (hr : r ≤ m*(2*n)) :
    8*(49*h + 1225*r) ≤ 8*(49*n + 1274*(m*(2*n))) := by omega

theorem output_edges (hdeg : D.boundedDegree) :
    let A := D.certifiedLayout hdeg
    (seedEdges (A.guardSet ∪ A.optionalSet)).card ≤
      8*(49*D.vertices.length + 1274*(D.edges.length*(2*D.vertices.length))) := by
  exact Nat.le_trans (m:=8*(49*D.coarseDrawing.hubs.card + 1225*D.coarseDrawing.runs.card))
    (D.coarseDrawing.output_size D.switchAt (D.concrete_valid hdeg))
    (numeric_bound D.coarse_hub_count D.coarse_run_count)

theorem output_centers (hdeg : D.boundedDegree) :
    ∀ p ∈ (D.certifiedLayout hdeg).domain, nearby (34*D.vertices.length + 17) (0,0) p := by
  intro p hp
  have h := D.coarseDrawing.output_coordinate_bound D.switchAt (D.concrete_valid hdeg)
    (2*D.vertices.length) D.coarse_coordinates p hp
  have eq : 17 * (2 * (D.vertices.length : ℤ)) + 17 = 34 * (D.vertices.length : ℤ) + 17 := by omega
  rw [eq] at h
  exact h

end AxisGridSource.Drawing
