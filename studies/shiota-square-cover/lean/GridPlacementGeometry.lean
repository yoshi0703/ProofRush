import GridGlobal

namespace GridCover.Placement

def add (p q : Center) : Center := (p.1 + q.1, p.2 + q.2)
def sub (p q : Center) : Center := (p.1 - q.1, p.2 - q.2)

def composeIso (g h : GridIso) : GridIso where
  point := g.point.trans h.point
  edge := g.edge.trans h.edge
  perim p e := (h.perim (g.point p) (g.edge e)).trans (g.perim p e)
  close p q := (h.close (g.point p) (g.point q)).trans (g.close p q)

@[simp] theorem composeIso_point (g h : GridIso) (p : Center) :
    (composeIso g h).point p = h.point (g.point p) := rfl

def shiftGrid (g : Center) : GridIso :=
  composeIso (composeIso (horizontalShift g.1) transposeGrid)
    (composeIso (horizontalShift g.2) transposeGrid)

@[simp] theorem shiftGrid_point (g p : Center) : (shiftGrid g).point p = add p g := rfl

def reflectXEdge : GridEdge → GridEdge
  | .horizontal x y => .horizontal (-x - 1) y
  | .vertical x y => .vertical (-x) y

def reflectX : GridIso where
  point := {
    toFun := fun p => (-p.1, p.2)
    invFun := fun p => (-p.1, p.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  edge := {
    toFun := reflectXEdge
    invFun := reflectXEdge
    left_inv := by intro e; cases e <;> simp [reflectXEdge]
    right_inv := by intro e; cases e <;> simp [reflectXEdge] }
  perim := by
    rintro ⟨x,y⟩ e
    change reflectXEdge e ∈ perimeter (-x,y) ↔ e ∈ perimeter (x,y)
    cases e <;> simp [reflectXEdge, perimeter] <;> omega
  close := by
    rintro ⟨x,y⟩ ⟨u,v⟩
    change nearby 2 (-x,y) (-u,v) ↔ nearby 2 (x,y) (u,v)
    simp [nearby]
    omega

inductive Direction
  | east | west | north | south
  deriving DecidableEq

namespace Direction

def vector : Direction → Center
  | east => (1,0)
  | west => (-1,0)
  | north => (0,1)
  | south => (0,-1)

def opposite : Direction → Direction
  | east => west
  | west => east
  | north => south
  | south => north

/-- Local coordinates can be reflected in the transversal, since both flanks have one phase. -/
def frame : Direction → GridIso
  | east => horizontalShift 0
  | west => reflectX
  | north => transposeGrid
  | south => composeIso transposeGrid reflectX

def longitudinal : Direction → Center → ℤ
  | east => fun p => p.1
  | west => fun p => -p.1
  | north => fun p => p.2
  | south => fun p => -p.2

def lateral : Direction → Center → ℤ
  | east | west => fun p => p.2
  | north | south => fun p => p.1

@[simp] theorem frame_point (d : Direction) (p : Center) :
    d.frame.point p = (d.longitudinal p, d.lateral p) := by
  rcases p with ⟨x,y⟩
  cases d
  · change (x + 0, y) = (x, y)
    simp
  · rfl
  · rfl
  · rfl

def atSite (d : Direction) (h : Center) (t : ℤ) : Center :=
  match d with
  | east => (h.1 + t, h.2)
  | west => (h.1 - t, h.2)
  | north => (h.1, h.2 + t)
  | south => (h.1, h.2 - t)

def localFrame (d : Direction) (h : Center) : GridIso :=
  composeIso (shiftGrid (-h.1, -h.2)) d.frame

@[simp] theorem frame_at (d : Direction) (h p : Center) :
    (d.localFrame h).point p = (d.longitudinal (sub p h), d.lateral (sub p h)) := by
  simp [localFrame, sub, add, sub_eq_add_neg]

@[simp] theorem longitudinal_atSite (d : Direction) (h : Center) (t : ℤ) :
    d.longitudinal (sub (d.atSite h t) h) = t := by
  cases d <;> simp [longitudinal, atSite, sub]

@[simp] theorem lateral_atSite (d : Direction) (h : Center) (t : ℤ) :
    d.lateral (sub (d.atSite h t) h) = 0 := by
  cases d <;> simp [lateral, atSite, sub]

theorem alongside (d : Direction) (h : Center) (L : ℤ) (p : Center) :
    d.opposite.longitudinal (sub p (d.atSite h L)) = L - d.longitudinal (sub p h) ∧
    d.opposite.lateral (sub p (d.atSite h L)) = d.lateral (sub p h) := by
  cases d <;> simp [longitudinal, lateral, atSite, opposite, sub] <;> omega

theorem nearby_frame (d : Direction) (h p q : Center) (r : ℤ) :
    nearby r ((d.localFrame h).point p) ((d.localFrame h).point q) ↔ nearby r p q := by
  rw [frame_at, frame_at]
  cases d <;> simp [nearby, longitudinal, lateral, sub] <;> omega

theorem along_vector (d : Direction) (p : Center) : along d.vector p = d.longitudinal p := by
  cases d <;> simp [vector, along, longitudinal]

theorem transverse_vector (d : Direction) (p : Center) :
    transverse d.vector p = d.lateral p ∨ transverse d.vector p = -d.lateral p := by
  cases d <;> simp [vector, transverse, lateral]

end Direction

theorem nearby_symm {r : ℤ} {x y : Center} : nearby r x y ↔ nearby r y x := by
  unfold nearby
  omega

theorem nearby_mono {r s : ℤ} {x y : Center} (hr : r ≤ s) (h : nearby r x y) : nearby s x y := by
  unfold nearby at *
  omega

theorem nearby_refl {r : ℤ} (hr : 0 ≤ r) (p : Center) : nearby r p p := by
  unfold nearby
  omega

theorem nearby_diff {r : ℤ} {p q : Center} : nearby r (0,0) (sub q p) ↔ nearby r p q := by
  simp [nearby, sub]
  omega

theorem guardPhase_reverse {L t : ℤ} (h : L % 4 = 1) :
    inBand 0 (L - t) ↔ inBand 0 t := by
  unfold inBand
  simp only [sub_zero]
  omega

/-- One oriented segment between consecutive hubs. -/
structure Run where
  start : Center
  dir : Direction
  length : ℤ
  deriving DecidableEq

namespace Run

def finish (s : Run) : Center := s.dir.atSite s.start s.length

def alongAt (s : Run) (p : Center) : ℤ := s.dir.longitudinal (sub p s.start)

def acrossAt (s : Run) (p : Center) : ℤ := s.dir.lateral (sub p s.start)

def Across (s : Run) (p : Center) : Prop := -1 ≤ s.acrossAt p ∧ s.acrossAt p ≤ 1

def Axis (s : Run) (p : Center) : Prop :=
  0 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length ∧ s.acrossAt p = 0

/-- Support for strip material and both endpoints of every seam link. -/
def Tube (s : Run) (p : Center) : Prop :=
  3 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length - 3 ∧ s.Across p

def reverse (s : Run) : Run := ⟨s.finish, s.dir.opposite, s.length⟩

@[simp] theorem reverse_finish (s : Run) : s.reverse.finish = s.start := by
  obtain ⟨⟨x,y⟩,d,L⟩ := s
  cases d <;> simp [finish, reverse, Direction.atSite, Direction.opposite]

@[simp] theorem reverse_reverse (s : Run) : s.reverse.reverse = s := by
  obtain ⟨h,d,L⟩ := s
  cases d <;> simp [reverse, finish, Direction.atSite, Direction.opposite]

theorem reverse_along (s : Run) (p : Center) :
    s.reverse.alongAt p = s.length - s.alongAt p :=
  (s.dir.alongside s.start s.length p).1

@[simp] theorem reverse_across (s : Run) (p : Center) :
    s.reverse.acrossAt p = s.acrossAt p :=
  (s.dir.alongside s.start s.length p).2

@[simp] theorem reverse_axis (s : Run) (p : Center) : s.reverse.Axis p ↔ s.Axis p := by
  simp only [Axis, reverse_along, reverse_across]
  change (0 ≤ s.length - s.alongAt p ∧ s.length - s.alongAt p ≤ s.length ∧ _) ↔ _
  omega

@[simp] theorem reverse_tube (s : Run) (p : Center) : s.reverse.Tube p ↔ s.Tube p := by
  simp only [Tube, reverse_along, Across, reverse_across]
  change (3 ≤ s.length - s.alongAt p ∧ s.length - s.alongAt p ≤ s.length - 3 ∧ _) ↔ _
  omega

theorem close_axis {s : Run} {p : Center} (h : s.Tube p) :
    ∃ q, s.Axis q ∧ nearby 1 p q := by
  refine ⟨s.dir.atSite s.start (s.alongAt p), ?_, ?_⟩
  · unfold Axis
    change 0 ≤ s.dir.longitudinal (sub (s.dir.atSite s.start (s.alongAt p)) s.start) ∧
      s.dir.longitudinal (sub (s.dir.atSite s.start (s.alongAt p)) s.start) ≤ s.length ∧
      s.dir.lateral (sub (s.dir.atSite s.start (s.alongAt p)) s.start) = 0
    simp only [Direction.longitudinal_atSite, Direction.lateral_atSite, and_true]
    unfold Tube at h
    omega
  · obtain ⟨hstart, d, L⟩ := s
    cases d <;>
      simp [Tube, Across, nearby, alongAt, acrossAt, sub, Direction.longitudinal,
        Direction.lateral, Direction.atSite] at h ⊢ <;> omega

theorem close_longitudinal {s : Run} {p q : Center} {r : ℤ} (h : nearby r p q) :
    s.alongAt p - r ≤ s.alongAt q ∧ s.alongAt q ≤ s.alongAt p + r := by
  obtain ⟨hstart,d,L⟩ := s
  cases d <;> simp [nearby, alongAt, sub, Direction.longitudinal] at h ⊢ <;> omega

theorem close_lateral {s : Run} {p q : Center} {r : ℤ} (h : nearby r p q) :
    s.acrossAt p - r ≤ s.acrossAt q ∧ s.acrossAt q ≤ s.acrossAt p + r := by
  obtain ⟨hstart,d,L⟩ := s
  cases d <;> simp [nearby, acrossAt, sub, Direction.lateral] at h ⊢ <;> omega

theorem near_start_iff (s : Run) (r : ℤ) (p : Center) :
    nearby r s.start p ↔ -r ≤ s.alongAt p ∧ s.alongAt p ≤ r ∧
      -r ≤ s.acrossAt p ∧ s.acrossAt p ≤ r := by
  obtain ⟨hstart,d,L⟩ := s
  cases d <;>
    simp [nearby, alongAt, acrossAt, sub, Direction.longitudinal, Direction.lateral] <;> omega

theorem patch_longitudinal {s : Run} {p q : Center} (h : s.Tube q) (hp : nearby 2 p q)
    (hStart : ¬ nearby 5 s.start p) (hFinish : ¬ nearby 5 s.finish p) :
    ∀ z, nearby 2 p z → 4 ≤ s.alongAt z ∧ s.alongAt z ≤ s.length - 4 := by
  intro z hz
  have low : ∀ (s : Run), s.Tube q → ¬ nearby 5 s.start p → 4 ≤ s.alongAt z := by
    intro s hq hAway
    have x := close_longitudinal (s := s) hp
    have y := close_lateral (s := s) hp
    have xz := close_longitudinal (s := s) hz
    rw [near_start_iff] at hAway
    unfold Tube Across at hq
    omega
  have hstart := low s h hStart
  have hfinish := low s.reverse ((reverse_tube s q).mpr h) hFinish
  rw [reverse_along] at hfinish
  omega

/-- Outside a hub's radius-five collar, no radius-two patch sees two distinct outgoing runs. -/
theorem neighboring_runs {s t : Run} {p q u : Center}
    (same : t.start = s.start) (different : s.dir ≠ t.dir)
    (hs : s.Tube q) (ht : t.Tube u) (hq : nearby 2 p q) (hu : nearby 2 p u) :
    nearby 5 s.start p := by
  rcases s with ⟨a,d,L⟩
  rcases t with ⟨b,e,M⟩
  change b = a at same
  subst b
  cases d <;> cases e <;>
    simp [Tube, Across, nearby, alongAt, acrossAt, sub, Direction.longitudinal,
      Direction.lateral] at different hs ht hq hu ⊢ <;> omega

def Optional (s : Run) (p : Center) : Prop :=
  4 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length - 4 ∧ s.acrossAt p = 0

def Guard (s : Run) (p : Center) : Prop :=
  4 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length - 4 ∧
    (s.acrossAt p = -1 ∨ s.acrossAt p = 1) ∧ inBand 0 (s.alongAt p)

def Link (s : Run) (p q : Center) : Prop :=
  (3 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length - 3 ∧ s.acrossAt p = 0) ∧
  (3 ≤ s.alongAt q ∧ s.alongAt q ≤ s.length - 3 ∧ s.acrossAt q = 0) ∧
  unitApart (s.alongAt p) (s.alongAt q)

theorem optional_tube {s : Run} {p : Center} (h : s.Optional p) : s.Tube p := by
  unfold Tube Across Optional at *
  omega

theorem guard_tube {s : Run} {p : Center} (h : s.Guard p) : s.Tube p := by
  unfold Tube Across Guard at *
  omega

theorem link_tube {s : Run} {p q : Center} (h : s.Link p q) : s.Tube p ∧ s.Tube q := by
  unfold Tube Across Link at *
  omega

@[simp] theorem reverse_optional (s : Run) (p : Center) : s.reverse.Optional p ↔ s.Optional p := by
  unfold Optional
  rw [reverse_along, reverse_across]
  change (4 ≤ s.length - s.alongAt p ∧ s.length - s.alongAt p ≤ s.length - 4 ∧ _) ↔ _
  omega

theorem reverse_guard (s : Run) (h : s.length % 4 = 1) (p : Center) :
    s.reverse.Guard p ↔ s.Guard p := by
  unfold Guard
  rw [reverse_along, reverse_across, guardPhase_reverse (L := s.length) (t := s.alongAt p) h]
  change (4 ≤ s.length - s.alongAt p ∧ s.length - s.alongAt p ≤ s.length - 4 ∧
    (s.acrossAt p = -1 ∨ s.acrossAt p = 1) ∧ inBand 0 (s.alongAt p)) ↔
    (4 ≤ s.alongAt p ∧ s.alongAt p ≤ s.length - 4 ∧
     (s.acrossAt p = -1 ∨ s.acrossAt p = 1) ∧ inBand 0 (s.alongAt p))
  constructor <;> intro hp <;> exact ⟨by omega, by omega, hp.2.2⟩

@[simp] theorem reverse_link (s : Run) (p q : Center) : s.reverse.Link p q ↔ s.Link p q := by
  simp only [Link, reverse_along, reverse_across, unitApart]
  change ((3 ≤ s.length - s.alongAt p ∧ s.length - s.alongAt p ≤ s.length - 3 ∧ _) ∧
    (3 ≤ s.length - s.alongAt q ∧ s.length - s.alongAt q ≤ s.length - 3 ∧ _) ∧ _) ↔ _
  omega

theorem link_nearby {s : Run} {p q : Center} (h : s.Link p q) : nearby 2 p q := by
  obtain ⟨a,d,L⟩ := s
  cases d <;>
    simp [Link, nearby, alongAt, acrossAt, sub, Direction.longitudinal,
      Direction.lateral, unitApart] at h ⊢ <;> omega

theorem link_ne {s : Run} {p q : Center} (h : s.Link p q) : p ≠ q := by
  intro hh
  subst q
  unfold Link unitApart at h
  omega

end Run

end GridCover.Placement
