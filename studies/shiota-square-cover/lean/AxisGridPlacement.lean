import AxisGridSource
import GridCoarseDrawing

namespace AxisGridSource.Drawing

open GridCover.Placement

variable {V : Type} (D : Drawing V)

def direction (e : V × V) : Direction :=
  match D.axis e with
  | .east => .east
  | .north => .north

def runAt (e : V × V) (i : Nat) : Run := ⟨D.site e i, D.direction e, 1⟩

theorem runAt_positive (e : V × V) (i : Nat) :
    (D.runAt e i).dir = .east ∨ (D.runAt e i).dir = .north := by
  unfold runAt direction
  cases D.axis e <;> simp

@[simp] theorem runAt_finish (e : V × V) (i : Nat) :
    (D.runAt e i).finish = D.site e (i+1) := by
  rw [D.site_succ]
  unfold runAt Run.finish direction
  cases D.axis e <;> simp [Direction.atSite, advance]

def edgeRuns (e : V × V) : List Run :=
  (List.range (2 * D.length e)).map (D.runAt e)

theorem edgeRuns_length (e : V × V) : (D.edgeRuns e).length = 2 * D.length e := by
  simp [edgeRuns]

theorem mem_edgeRuns {s : Run} {e : V × V} :
    s ∈ D.edgeRuns e ↔ ∃ i < 2 * D.length e, D.runAt e i = s := by
  simp [edgeRuns]

def coarseRuns : Finset Run := (D.edges.flatMap D.edgeRuns).toFinset

theorem mem_coarseRuns {s : Run} :
    s ∈ D.coarseRuns ↔ ∃ e ∈ D.edges, ∃ i < 2 * D.length e, D.runAt e i = s := by
  simp [coarseRuns, mem_edgeRuns]

/-- Subdivide each doubled source segment into positively oriented unit runs. -/
def coarseDrawing : CoarseDrawing where
  hubs := D.occupied.toFinset
  runs := D.coarseRuns
  lengthOne := by
    intro _ hs
    obtain ⟨e,_,i,_,rfl⟩ := D.mem_coarseRuns.mp hs
    rfl
  positive := by
    intro _ hs
    obtain ⟨e,_,i,_,rfl⟩ := D.mem_coarseRuns.mp hs
    exact D.runAt_positive e i
  startHub := by
    intro _ hs
    obtain ⟨e,he,i,hi,rfl⟩ := D.mem_coarseRuns.mp hs
    exact List.mem_toFinset.mpr (D.site_mem_occupied he (Nat.le_of_lt hi))
  finishHub := by
    intro _ hs
    obtain ⟨e,he,i,hi,rfl⟩ := D.mem_coarseRuns.mp hs
    rw [D.runAt_finish]
    exact List.mem_toFinset.mpr (D.site_mem_occupied he (by omega))

theorem coarse_start_mem {e : V × V} (he : e ∈ D.edges) :
    D.hub e.1 ∈ D.coarseDrawing.hubs := by
  rw [← D.site_zero e]
  exact List.mem_toFinset.mpr (D.site_mem_occupied he (Nat.zero_le _))

theorem coarse_end_mem {e : V × V} (he : e ∈ D.edges) :
    D.hub e.2 ∈ D.coarseDrawing.hubs := by
  rw [← D.site_last he]
  exact List.mem_toFinset.mpr (D.site_mem_occupied he (Nat.le_refl _))

theorem coarse_inside_mem {e : V × V} (he : e ∈ D.edges) {p : Point}
    (hp : p ∈ D.inside e) : p ∈ D.coarseDrawing.hubs := by
  obtain ⟨i,_,hi,rfl⟩ := D.mem_inside.mp hp
  exact List.mem_toFinset.mpr (D.site_mem_occupied he (Nat.le_of_lt hi))

theorem coarse_outward_iff (p : Point) (d : Direction) :
    Outward D.coarseDrawing.runs p d ↔
    ∃ e ∈ D.edges, ∃ i < 2 * D.length e,
      (p = D.site e i ∧ d = D.direction e) ∨
      (p = D.site e (i+1) ∧ d = (D.direction e).opposite) := by
  constructor
  · rintro ⟨s,hs,hp,hd⟩
    rcases hs with hs | hs
    · obtain ⟨e,he,i,hi,rfl⟩ := D.mem_coarseRuns.mp hs
      exact ⟨e,he,i,hi,Or.inl ⟨hp.symm,hd.symm⟩⟩
    · obtain ⟨e,he,i,hi,hs⟩ := D.mem_coarseRuns.mp hs
      have hr : s = (D.runAt e i).reverse := by
        simpa using congrArg Run.reverse hs.symm
      subst s
      exact ⟨e,he,i,hi,Or.inr ⟨by simpa [Run.reverse] using hp.symm, hd.symm⟩⟩
  · rintro ⟨e,he,i,hi,⟨hp,hd⟩ | ⟨hp,hd⟩⟩
    · exact ⟨D.runAt e i, Or.inl (D.mem_coarseRuns.mpr ⟨e,he,i,hi,rfl⟩),hp.symm,hd.symm⟩
    · refine ⟨(D.runAt e i).reverse, Or.inr ?_, ?_, hd.symm⟩
      · change (D.runAt e i).reverse.reverse ∈ D.coarseRuns
        simpa using D.mem_coarseRuns.mpr ⟨e,he,i,hi,rfl⟩
      · simpa [Run.reverse] using hp.symm

theorem shaped_outward_iff (p : Point) (d : Direction) :
    Outward D.coarseDrawing.shapeRuns (scalePoint p) d ↔
    Outward D.coarseDrawing.runs p d := by
  constructor
  · rintro ⟨s,hs,hp,hd⟩
    rcases hs with hs | hs
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
      exact ⟨r,Or.inl hr,scalePoint_injective hp,hd⟩
    · obtain ⟨r,hr,hs⟩ := Finset.mem_image.mp hs
      have h : s = r.reverse.scaled := by
        have h' := congrArg Run.reverse hs.symm
        simpa [Run.scaled_reverse] using h'
      subst s
      exact ⟨r.reverse,Or.inr (by simpa using hr),scalePoint_injective hp,hd⟩
  · rintro ⟨s,hs,hp,hd⟩
    refine ⟨s.scaled, ?_, congrArg scalePoint hp, hd⟩
    rcases hs with hs | hs
    · exact Or.inl (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨s.reverse,hs,s.scaled_reverse.symm⟩)

theorem other_edge_cannot_contain_inside {e f : V × V} (he : e ∈ D.edges)
    (hf : f ∈ D.edges) {p : Point} (hp : p ∈ D.inside e) {i : Nat}
    (hi : i ≤ 2 * D.length f) (h : p = D.site f i) : f = e := by
  by_contra hne
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [D.site_zero f] at h
    exact (D.inside_clear_hub he (D.edge_endpoints f hf).1) (h ▸ hp)
  by_cases hlast : i = 2 * D.length f
  · rw [hlast, D.site_last hf] at h
    exact (D.inside_clear_hub he (D.edge_endpoints f hf).2) (h ▸ hp)
  · exact D.inside_disjoint he hf (Ne.symm hne) hp
      (D.mem_inside.mpr ⟨i,hpos,by omega,h.symm⟩)

theorem inside_ports {e : V × V} (he : e ∈ D.edges) {p : Point}
    (hp : p ∈ D.inside e) (d : Direction) :
    Outward D.coarseDrawing.shapeRuns (scalePoint p) d ↔
      d = D.direction e ∨ d = (D.direction e).opposite := by
  rw [D.shaped_outward_iff, D.coarse_outward_iff]
  constructor
  · rintro ⟨f,hf,i,hi,⟨h,hd⟩ | ⟨h,hd⟩⟩
    · have h' := D.other_edge_cannot_contain_inside he hf hp (Nat.le_of_lt hi) h
      exact Or.inl (h' ▸ hd)
    · have h' := D.other_edge_cannot_contain_inside he hf hp (by omega) h
      exact Or.inr (h' ▸ hd)
  · obtain ⟨i,hi,hil,h⟩ := D.mem_inside.mp hp
    rintro (hd | hd)
    · exact ⟨e,he,i,hil,Or.inl ⟨h.symm,hd⟩⟩
    · refine ⟨e,he,i-1,by omega,Or.inr ⟨?_,hd⟩⟩
      have h1 : i-1+1 = i := by omega
      rw [h1,h]

theorem source_hub_ports {v : V} (hv : v ∈ D.vertices) (d : Direction) :
    Outward D.coarseDrawing.shapeRuns (scalePoint (D.hub v)) d ↔
      ∃ e ∈ D.edges,
      (v = e.1 ∧ d = D.direction e) ∨ (v = e.2 ∧ d = (D.direction e).opposite) := by
  rw [D.shaped_outward_iff,D.coarse_outward_iff]
  constructor
  · rintro ⟨e,he,i,hi,⟨hp,hd⟩ | ⟨hp,hd⟩⟩
    · have hi' : i = 0 := by
        by_contra h
        exact D.inside_clear_hub he hv (D.mem_inside.mpr ⟨i,by omega,hi,hp.symm⟩)
      rw [hi',D.site_zero e] at hp
      exact ⟨e,he,Or.inl ⟨D.hub_injective hp, hd⟩⟩
    · have hi' : i+1 = 2 * D.length e := by
        by_contra h
        exact D.inside_clear_hub he hv (D.mem_inside.mpr ⟨i+1,by omega,by omega,hp.symm⟩)
      rw [hi',D.site_last he] at hp
      exact ⟨e,he,Or.inr ⟨D.hub_injective hp,hd⟩⟩
  · rintro ⟨e,he,⟨rfl,hd⟩ | ⟨rfl,hd⟩⟩
    · have h := D.length_pos he
      exact ⟨e,he,0,by omega,Or.inl ⟨(D.site_zero e).symm,hd⟩⟩
    · have h := D.length_pos he
      refine ⟨e,he,2 * D.length e - 1,by omega,Or.inr ⟨?_,hd⟩⟩
      have h' : 2 * D.length e - 1 + 1 = 2 * D.length e := by omega
      rw [h',D.site_last he]

theorem coarse_sites_card :
    D.coarseDrawing.hubs.card ≤ D.vertices.length + D.edges.length*(2*D.vertices.length) :=
  (List.toFinset_card_le D.occupied).trans D.occupied_size_bound

theorem support_run_count_bound :
    (D.edges.flatMap D.edgeRuns).length ≤ D.edges.length * (2 * D.vertices.length) := by
  generalize hes : D.edges = es
  have all : ∀ e ∈ es, (D.edgeRuns e).length ≤ 2 * D.vertices.length := by
    intro e he
    rw [D.edgeRuns_length]
    have h := D.length_bound (hes ▸ he)
    omega
  clear hes
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul]
    have h1 := all e List.mem_cons_self
    have h2 := ih (fun f hf => all f (List.mem_cons_of_mem _ hf))
    omega

theorem coarse_runs_card :
    D.coarseDrawing.runs.card ≤ D.edges.length * (2 * D.vertices.length) :=
  (List.toFinset_card_le (D.edges.flatMap D.edgeRuns)).trans D.support_run_count_bound

section Degrees
variable [DecidableEq V]

def incidentEdges (v : V) : Finset (V × V) :=
  D.edges.toFinset.filter (fun e => v = e.1 ∨ v = e.2)

theorem mem_incidentEdges {v : V} {e : V × V} :
    e ∈ D.incidentEdges v ↔ e ∈ D.edges ∧ Ends v e := by
  simp [incidentEdges, Ends]

def degree (v : V) : Nat := (D.incidentEdges v).card

def localDirection (v : V) (e : V × V) : Direction :=
  if v = e.1 then D.direction e else (D.direction e).opposite

omit [DecidableEq V] in
theorem endpoints_distinct {e : V × V} (he : e ∈ D.edges) : e.1 ≠ e.2 := by
  intro eq
  have h := D.edge_straight e he
  simp [straight, eq] at h

theorem localDirection_spec {e : V × V} (he : e ∈ D.edges) {v : V} (hv : Ends v e)
    (d : Direction) :
    D.localDirection v e = d ↔
    (v = e.1 ∧ d = D.direction e) ∨ (v = e.2 ∧ d = (D.direction e).opposite) := by
  rcases hv with rfl | rfl
  · simp [localDirection, D.endpoints_distinct he, eq_comm]
  · simp [localDirection, Ne.symm (D.endpoints_distinct he), eq_comm]

/-- An incident port leads to the immediately adjacent strict interior site. -/
theorem port_neighbor_inside {e : V × V} (he : e ∈ D.edges) {v : V} (hv : Ends v e) :
    (D.localDirection v e).atSite (D.hub v) 1 ∈ D.inside e := by
  have hlen := D.length_pos he
  rcases hv with rfl | rfl
  · refine D.mem_inside.mpr ⟨1,by omega,by omega,?_⟩
    have hf := D.runAt_finish e 0
    simpa [runAt, Run.finish, D.site_zero e, localDirection] using hf.symm
  · let i := 2 * D.length e - 1
    have hii : i+1 = 2 * D.length e := by dsimp [i]; omega
    have hf := D.runAt_finish e i
    rw [hii,D.site_last he] at hf
    refine D.mem_inside.mpr ⟨i,by dsimp [i]; omega,by dsimp [i]; omega,?_⟩
    have hrev := ((D.runAt e i).reverse_finish).symm
    change D.site e i = (D.direction e).opposite.atSite (D.runAt e i).finish 1 at hrev
    simpa [hf, localDirection, Ne.symm (D.endpoints_distinct he)] using hrev

theorem localDirection_injective (v : V) :
    Set.InjOn (D.localDirection v) (D.incidentEdges v : Set (V × V)) := by
  intro e he f hf eq
  by_contra ne
  obtain ⟨he,hve⟩ := D.mem_incidentEdges.mp he
  obtain ⟨hf,hvf⟩ := D.mem_incidentEdges.mp hf
  have eGerm := D.port_neighbor_inside he hve
  have fGerm := D.port_neighbor_inside hf hvf
  rw [eq] at eGerm
  exact D.inside_disjoint he hf ne eGerm fGerm

def sourcePorts (v : V) : Finset Direction := (D.incidentEdges v).image (D.localDirection v)

theorem sourcePorts_card (v : V) : (D.sourcePorts v).card = D.degree v :=
  Finset.card_image_of_injOn (D.localDirection_injective v)

theorem sourcePorts_correct {v : V} (hv : v ∈ D.vertices) (d : Direction) :
    d ∈ D.sourcePorts v ↔
      Outward D.coarseDrawing.shapeRuns (scalePoint (D.hub v)) d := by
  rw [D.source_hub_ports hv d]
  constructor
  · intro hd
    obtain ⟨e,he,hd⟩ := Finset.mem_image.mp hd
    obtain ⟨he,hve⟩ := D.mem_incidentEdges.mp he
    exact ⟨e,he,(D.localDirection_spec he hve d).mp hd⟩
  · rintro ⟨e,he,hs⟩
    have hve : Ends v e := hs.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    exact Finset.mem_image.mpr ⟨e,D.mem_incidentEdges.mpr ⟨he,hve⟩,
      (D.localDirection_spec he hve d).mpr hs⟩

def teeCount (e : V × V) : Nat :=
  (if D.degree e.1 = 3 then 1 else 0) + (if D.degree e.2 = 3 then 1 else 0)

theorem teeCount_le (e : V × V) : D.teeCount e ≤ 2 := by
  unfold teeCount
  split <;> split <;> omega

def hasSwitch (p : Point) : Prop :=
  ∃ e ∈ D.edges.toFinset, D.teeCount e % 2 = 0 ∧ p = scalePoint (D.dedicated e)

instance (p : Point) : Decidable (D.hasSwitch p) := by
  unfold hasSwitch
  infer_instance

def switchAt (p : Point) : Bool := decide (D.hasSwitch p)

theorem switchAt_spec (p : Point) :
    D.switchAt p = true ↔
      ∃ e ∈ D.edges, D.teeCount e % 2 = 0 ∧ p = scalePoint (D.dedicated e) := by
  simp [switchAt, hasSwitch]

theorem switchAt_hub {v : V} (hv : v ∈ D.vertices) :
    D.switchAt (scalePoint (D.hub v)) = false := by
  cases h : D.switchAt (scalePoint (D.hub v))
  · rfl
  · obtain ⟨e,he,_,h⟩ := (D.switchAt_spec _).mp h
    have heq := scalePoint_injective h
    exact (D.inside_clear_hub he hv (heq.symm ▸ D.dedicated_inside he)).elim

theorem switchAt_inside {e : V × V} (he : e ∈ D.edges) {p : Point} (hp : p ∈ D.inside e) :
    D.switchAt (scalePoint p) = true ↔ D.switch (D.teeCount e) e p := by
  rw [D.switchAt_spec]
  constructor
  · rintro ⟨f,hf,hm,h⟩
    have hp' := scalePoint_injective h
    have hef : f = e := by
      by_contra ne
      exact D.inside_disjoint he hf (Ne.symm ne) hp (hp'.symm ▸ D.dedicated_inside hf)
    subst f
    exact ⟨hm,hp'⟩
  · rintro ⟨h,rfl⟩
    exact ⟨e,he,h,rfl⟩

theorem switchAt_site {e : V × V} (he : e ∈ D.edges) {i : Nat}
    (hi : 0 < i) (hl : i < 2 * D.length e) :
    D.switchAt (scalePoint (D.site e i)) = true ↔ D.teeCount e % 2 = 0 ∧ i = 1 := by
  rw [D.switchAt_inside he (D.mem_inside.mpr ⟨i,hi,hl,rfl⟩)]
  simp [switch,D.dedicated_index]

def leftTee (e : V × V) : Bool := decide (D.degree e.1 = 3)
def rightTee (e : V × V) : Bool := decide (D.degree e.2 = 3)

theorem even_tees_iff (e : V × V) :
    D.teeCount e % 2 = 0 ↔ D.leftTee e = D.rightTee e := by
  unfold teeCount leftTee rightTee
  split <;> split <;> simp_all

def intendedLength (e : V × V) : Nat :=
  17 * (2 * D.length e) - D.teeCount e -
    (if D.teeCount e % 2 = 0 then 1 else 0)

theorem intendedLength_odd {e : V × V} (he : e ∈ D.edges) :
    D.intendedLength e % 2 = 1 := by
  have hlen := D.length_pos he
  have htee := D.teeCount_le e
  unfold intendedLength
  split <;> omega

end Degrees

end AxisGridSource.Drawing
