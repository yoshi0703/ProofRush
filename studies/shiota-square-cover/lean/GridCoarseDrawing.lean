import GridPlacementAtlas

namespace GridCover.Placement

def scalePoint (p : Center) : Center := (17 * p.1, 17 * p.2)

theorem scalePoint_injective : Function.Injective scalePoint := by
  rintro ⟨x,y⟩ ⟨a,b⟩ eq
  simp [scalePoint] at eq ⊢
  omega

theorem scaled_hubs_apart {p q : Center} (h : nearby 16 (scalePoint p) (scalePoint q)) : p = q := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨a,b⟩
  simp [nearby, scalePoint] at h ⊢
  omega

namespace Run

def scaled (s : Run) : Run := ⟨scalePoint s.start, s.dir, 17 * s.length⟩

@[simp] theorem scaled_finish (s : Run) : s.scaled.finish = scalePoint s.finish := by
  rcases s with ⟨⟨x,y⟩,d,L⟩
  cases d <;> simp [scaled, finish, Direction.atSite, scalePoint] <;> omega

theorem scaled_reverse (s : Run) : s.scaled.reverse = s.reverse.scaled := by
  change Run.mk s.scaled.finish _ _ = Run.mk (scalePoint s.finish) _ _
  rw [scaled_finish]
  rfl

@[simp] theorem scaled_start (s : Run) : s.scaled.start = scalePoint s.start := rfl

structure Bounds where
  xlo : ℤ
  xhi : ℤ
  ylo : ℤ
  yhi : ℤ

def Bounds.Covers (b : Bounds) (p : Center) : Prop :=
  b.xlo ≤ p.1 ∧ p.1 ≤ b.xhi ∧ b.ylo ≤ p.2 ∧ p.2 ≤ b.yhi

def Bounds.scale (b : Bounds) : Bounds := ⟨17 * b.xlo, 17 * b.xhi, 17 * b.ylo, 17 * b.yhi⟩

def Bounds.point (p : Center) : Bounds := ⟨p.1, p.1, p.2, p.2⟩

def bounds (s : Run) : Bounds :=
  let (x,y) := s.start
  match s.dir with
  | .east => ⟨x,x+s.length,y,y⟩
  | .west => ⟨x-s.length,x,y,y⟩
  | .north => ⟨x,x,y,y+s.length⟩
  | .south => ⟨x,x,y-s.length,y⟩

theorem covers_iff (s : Run) (p : Center) : s.bounds.Covers p ↔ s.Axis p := by
  rcases s with ⟨⟨x,y⟩,d,L⟩
  cases d <;> simp [bounds, Bounds.Covers, Axis, alongAt, acrossAt, sub,
    Direction.longitudinal, Direction.lateral] <;> omega

theorem scale_bounds (s : Run) : s.scaled.bounds = s.bounds.scale := by
  rcases s with ⟨⟨x,y⟩,d,L⟩
  cases d <;> simp [bounds, scaled, Bounds.scale, scalePoint, Bounds.mk.injEq] <;> omega

theorem Bounds.overlap_of_scaled_near {a b : Bounds} {p q : Center} {r : ℤ}
    (radius : r ≤ 16) (ha : a.scale.Covers p) (hb : b.scale.Covers q) (h : nearby r p q) :
    ∃ z, a.Covers z ∧ b.Covers z := by
  refine ⟨(max a.xlo b.xlo, max a.ylo b.ylo), ?_⟩
  simp only [Bounds.scale, Bounds.Covers] at ha hb
  simp only [Bounds.Covers, le_max_left, le_max_right, max_le_iff, true_and]
  unfold nearby at h
  omega

theorem coarse_axis_endpoints {s : Run} (length : s.length = 1) {p : Center} (h : s.Axis p) :
    Incident s p := by
  rcases s with ⟨⟨x,y⟩,d,L⟩
  rcases p with ⟨a,b⟩
  cases d <;>
    simp [Axis, alongAt, acrossAt, sub, Direction.longitudinal, Direction.lateral,
      Incident, finish, Direction.atSite] at length h ⊢ <;> omega

theorem scaled_run_away_of_nonincident {s : Run} {p q : Center} (length : s.length = 1)
    (hn : ¬ Incident s p) (h : s.scaled.Axis q) : ¬ nearby 8 (scalePoint p) q := by
  intro near
  have ha : (Bounds.point p).scale.Covers (scalePoint p) := by simp [Bounds.Covers, Bounds.point, Bounds.scale, scalePoint]
  have hb : s.bounds.scale.Covers q := by
    rw [← scale_bounds]; exact (s.scaled.covers_iff q).mpr h
  obtain ⟨z, hz, hr⟩ := Bounds.overlap_of_scaled_near (by decide) ha hb near
  have eq : z = p := by
    rcases z with ⟨zx,zy⟩
    rcases p with ⟨px,py⟩
    simp [Bounds.Covers, Bounds.point] at hz ⊢
    omega
  subst z
  exact hn (coarse_axis_endpoints length ((s.covers_iff p).mp hr))

theorem scaled_axes_far_of_disjoint {s t : Run} (ls : s.length = 1) (lt : t.length = 1)
    (notShared : ¬ ∃ p, Incident s p ∧ Incident t p) : FarRuns s.scaled t.scaled := by
  intro p q hp hq near
  have ha : s.bounds.scale.Covers p := by
    rw [← scale_bounds]; exact (s.scaled.covers_iff p).mpr hp
  have hb : t.bounds.scale.Covers q := by
    rw [← scale_bounds]; exact (t.scaled.covers_iff q).mpr hq
  obtain ⟨z, hz, hr⟩ := Bounds.overlap_of_scaled_near (by decide) ha hb near
  exact notShared ⟨z, coarse_axis_endpoints ls ((s.covers_iff z).mp hz),
    coarse_axis_endpoints lt ((t.covers_iff z).mp hr)⟩

theorem same_dir_and_start {s t : Run} (ls : s.length = 1) (lt : t.length = 1)
    (start : s.start = t.start) (dir : s.dir = t.dir) : s = t := by
  rcases s with ⟨a,d,l⟩
  rcases t with ⟨b,e,k⟩
  simp_all

end Run

/-- Finite embedded subgraph of the coarse square lattice. Store each edge in a positive direction. -/
structure CoarseDrawing where
  hubs : Finset Center
  runs : Finset Run
  lengthOne : ∀ s ∈ runs, s.length = 1
  positive : ∀ s ∈ runs, s.dir = .east ∨ s.dir = .north
  startHub : ∀ s ∈ runs, s.start ∈ hubs
  finishHub : ∀ s ∈ runs, s.finish ∈ hubs

namespace CoarseDrawing

def shapeHubs (D : CoarseDrawing) : Finset Center := D.hubs.image scalePoint

def shapeRuns (D : CoarseDrawing) : Finset Run := D.runs.image Run.scaled

theorem coarse_run_no_reverse (D : CoarseDrawing) {s t : Run}
    (hs : s ∈ D.runs) (ht : t ∈ D.runs) : s.reverse ≠ t := by
  have a := D.positive s hs
  have b := D.positive t ht
  intro eq
  subst t
  change s.dir.opposite = .east ∨ s.dir.opposite = .north at b
  rcases a with h | h <;> simp [h, Direction.opposite] at b

theorem incident_different_ports (D : CoarseDrawing) {s t : Run}
    (hs : s ∈ D.runs) (ht : t ∈ D.runs) (hd : s ≠ t)
    {p : Center} (si : Incident s p) (ti : Incident t p) : DifferAtHub s.scaled t.scaled := by
  have l := D.lengthOne s hs
  have m := D.lengthOne t ht
  rcases si with sa | sa <;> rcases ti with tb | tb
  · refine ⟨s.scaled, t.scaled, Or.inl rfl, Or.inl rfl, by simp [sa,tb], ?_⟩
    exact fun eq => hd (Run.same_dir_and_start l m (sa.trans tb.symm) eq)
  · refine ⟨s.scaled, t.scaled.reverse, Or.inl rfl, Or.inr rfl, ?_, ?_⟩
    · change s.scaled.start = t.scaled.finish
      simp [sa,tb]
    · intro eq
      have e : s = t.reverse := Run.same_dir_and_start l m (sa.trans tb.symm) eq
      exact D.coarse_run_no_reverse ht hs e.symm
  · refine ⟨s.scaled.reverse, t.scaled, Or.inr rfl, Or.inl rfl, ?_, ?_⟩
    · change s.scaled.finish = t.scaled.start
      simp [sa,tb]
    · intro eq
      have e : s.reverse = t := Run.same_dir_and_start l m (sa.trans tb.symm) eq
      exact D.coarse_run_no_reverse hs ht e
  · refine ⟨s.scaled.reverse, t.scaled.reverse, Or.inr rfl, Or.inr rfl, ?_, ?_⟩
    · change s.scaled.finish = t.scaled.finish
      simp [sa,tb]
    · intro eq
      have e : s.reverse = t.reverse := Run.same_dir_and_start l m (sa.trans tb.symm) eq
      have ee := congrArg Run.reverse e
      exact hd (by simpa using ee)

theorem scaled_runs_apart (D : CoarseDrawing) {s t : Run}
    (hs : s ∈ D.shapeRuns) (ht : t ∈ D.shapeRuns) (hd : s ≠ t) :
    FarRuns s t ∨ DifferAtHub s t := by
  classical
  obtain ⟨sr,hSr,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨tr,hTr,rfl⟩ := Finset.mem_image.mp ht
  by_cases shared : ∃ p, Incident sr p ∧ Incident tr p
  · obtain ⟨p,hp,hq⟩ := shared
    exact Or.inr (D.incident_different_ports hSr hTr (fun eq => hd (congrArg Run.scaled eq)) hp hq)
  · exact Or.inl (Run.scaled_axes_far_of_disjoint (D.lengthOne sr hSr) (D.lengthOne tr hTr) shared)

theorem scaled_hub_run_apart (D : CoarseDrawing) {h : Center} {s : Run}
    (hh : h ∈ D.shapeHubs) (hs : s ∈ D.shapeRuns) (hn : ¬ Incident s h) {q : Center}
    (hq : s.Axis q) : ¬ nearby 8 h q := by
  obtain ⟨r,hR,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨t,hT,rfl⟩ := Finset.mem_image.mp hs
  refine Run.scaled_run_away_of_nonincident (D.lengthOne t hT) ?_ hq
  intro hi
  apply hn
  rcases hi with he | he
  · exact Or.inl (by simp [he])
  · exact Or.inr (by simp [he])

def assemble (D : CoarseDrawing) (models : ∀ h : Center, ModelAt h)
    (port : ∀ h ∈ D.shapeHubs, ∀ d, d ∈ (models h).ports ↔ Outward D.shapeRuns h d) : Layout where
  hubs := D.shapeHubs
  runs := D.shapeRuns
  model := models
  startHub := by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨r.start,D.startHub r hr,rfl⟩
  finishHub := by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨r.finish,D.finishHub r hr,(r.scaled_finish).symm⟩
  port := port
  long := by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    change 17 ≤ 17 * r.length
    rw [D.lengthOne r hr]
    decide
  phase := by
    intro s hs
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
    change (17 * r.length) % 4 = 1
    rw [D.lengthOne r hr]
    decide
  hubsApart := by
    intro h hh j hj ne near
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hj
    exact ne (congrArg scalePoint (scaled_hubs_apart near))
  hubRunApart := fun _ hh _ hs ha _ hq => D.scaled_hub_run_apart hh hs ha hq
  runsApart := fun _ hs _ ht ne => D.scaled_runs_apart hs ht ne

theorem certified_scaled_layout (D : CoarseDrawing) (models : ∀ h : Center, ModelAt h)
    (port : ∀ h ∈ D.shapeHubs, ∀ d, d ∈ (models h).ports ↔ Outward D.shapeRuns h d) :
    HasCertifiedPatches (D.assemble models port).roles (D.assemble models port).links :=
  (D.assemble models port).hasCertifiedPatches

end CoarseDrawing

end GridCover.Placement
