import GridPlacementGeometry

namespace GridCover.Placement

namespace Run

/-- A ray uses the starting point and direction, independently of the finite run length. -/
def RayOptional (s : Run) (p : Center) : Prop := 4 ≤ s.alongAt p ∧ s.acrossAt p = 0

def RayGuard (s : Run) (p : Center) : Prop :=
  4 ≤ s.alongAt p ∧ (s.acrossAt p = -1 ∨ s.acrossAt p = 1) ∧ inBand 0 (s.alongAt p)

def RayLink (s : Run) (p q : Center) : Prop :=
  (3 ≤ s.alongAt p ∧ s.acrossAt p = 0) ∧ (3 ≤ s.alongAt q ∧ s.acrossAt q = 0) ∧
  unitApart (s.alongAt p) (s.alongAt q)

def ray (h : Center) (d : Direction) : Run := ⟨h,d,0⟩

theorem collar_optional {s : Run} {p : Center} (length : 17 ≤ s.length)
    (hp : nearby 7 s.start p) : s.Optional p ↔ (ray s.start s.dir).RayOptional p := by
  have bound := (near_start_iff s 7 p).mp hp
  unfold Optional RayOptional
  change (_ ∧ _ ∧ _) ↔ 4 ≤ s.alongAt p ∧ s.acrossAt p = 0
  omega

theorem collar_guard {s : Run} {p : Center} (length : 17 ≤ s.length)
    (hp : nearby 7 s.start p) : s.Guard p ↔ (ray s.start s.dir).RayGuard p := by
  have bound := (near_start_iff s 7 p).mp hp
  unfold Guard RayGuard
  change (_ ∧ _ ∧ _) ↔ 4 ≤ s.alongAt p ∧ _
  change (_ ∧ _ ∧ _) ↔ 4 ≤ s.alongAt p ∧
    (s.acrossAt p = -1 ∨ s.acrossAt p = 1) ∧ inBand 0 (s.alongAt p)
  exact ⟨fun hh => ⟨hh.1, hh.2.2⟩, fun hh => ⟨hh.1, by omega, hh.2⟩⟩

theorem collar_link {s : Run} {p q : Center} (length : 17 ≤ s.length)
    (hp : nearby 7 s.start p) (hq : nearby 7 s.start q) :
    s.Link p q ↔ (ray s.start s.dir).RayLink p q := by
  have bp := (near_start_iff s 7 p).mp hp
  have bq := (near_start_iff s 7 q).mp hq
  unfold Link RayLink
  change (_ ∧ _ ∧ _) ↔ (3 ≤ s.alongAt p ∧ s.acrossAt p = 0) ∧
    (3 ≤ s.alongAt q ∧ s.acrossAt q = 0) ∧ unitApart (s.alongAt p) (s.alongAt q)
  constructor
  · rintro ⟨⟨a, _, b⟩, ⟨c, _, d⟩, e⟩
    exact ⟨⟨a,b⟩, ⟨c,d⟩, e⟩
  · rintro ⟨⟨a,b⟩, ⟨c,d⟩, e⟩
    exact ⟨⟨a,by omega,b⟩, ⟨c,by omega,d⟩, e⟩

end Run

structure ModelAt (h : Center) where
  stencil : Stencil
  localize : GridIso
  ports : Finset Direction
  near : ∀ (r : ℤ) (p : Center), nearby r (0,0) (localize.point p) ↔ nearby r h p
  checked : ∀ p ∈ box 5 (0,0), rawCheck stencil.roles stencil.links p
  valid : stencil.dataValid
  portOptional : ∀ d ∈ ports, nearby 3 h (d.atSite h 3) ∧ localize.point (d.atSite h 3) ∈ stencil.optional
  optional : ∀ p, stencil.roles (localize.point p) = .optional ↔
    (nearby 3 h p ∧ localize.point p ∈ stencil.optional) ∨
    ∃ d ∈ ports, (Run.ray h d).RayOptional p
  guard : ∀ p, stencil.roles (localize.point p) = .guard ↔
    (nearby 3 h p ∧ localize.point p ∈ stencil.guards) ∨
    ∃ d ∈ ports, (Run.ray h d).RayGuard p
  links : ∀ p q, stencil.links (localize.point p) (localize.point q) = true ↔
    (nearby 3 h p ∧ nearby 3 h q ∧
      ((localize.point p, localize.point q) ∈ stencil.graph ∨
       (localize.point q, localize.point p) ∈ stencil.graph)) ∨
    ∃ d ∈ ports, (Run.ray h d).RayLink p q

def ModelAt.CoreOptional {h : Center} (M : ModelAt h) (p : Center) : Prop :=
  nearby 3 h p ∧ M.localize.point p ∈ M.stencil.optional

def ModelAt.CoreGuard {h : Center} (M : ModelAt h) (p : Center) : Prop :=
  nearby 3 h p ∧ M.localize.point p ∈ M.stencil.guards

def ModelAt.CoreLink {h : Center} (M : ModelAt h) (p q : Center) : Prop :=
  nearby 3 h p ∧ nearby 3 h q ∧
    ((M.localize.point p, M.localize.point q) ∈ M.stencil.graph ∨
     (M.localize.point q, M.localize.point p) ∈ M.stencil.graph)

def Incident (s : Run) (h : Center) : Prop := s.start = h ∨ s.finish = h

def Oriented (R : Finset Run) (s : Run) : Prop := s ∈ R ∨ s.reverse ∈ R

def Outward (R : Finset Run) (h : Center) (d : Direction) : Prop :=
  ∃ s, Oriented R s ∧ s.start = h ∧ s.dir = d

def FarRuns (s t : Run) : Prop := ∀ p q, s.Axis p → t.Axis q → ¬ nearby 6 p q

def DifferAtHub (s t : Run) : Prop :=
  ∃ a b : Run, (a = s ∨ a = s.reverse) ∧ (b = t ∨ b = t.reverse) ∧
    a.start = b.start ∧ a.dir ≠ b.dir

structure Layout where
  hubs : Finset Center
  runs : Finset Run
  model : ∀ h : Center, ModelAt h
  startHub : ∀ s ∈ runs, s.start ∈ hubs
  finishHub : ∀ s ∈ runs, s.finish ∈ hubs
  port : ∀ h ∈ hubs, ∀ d, d ∈ (model h).ports ↔ Outward runs h d
  long : ∀ s ∈ runs, 17 ≤ s.length
  phase : ∀ s ∈ runs, s.length % 4 = 1
  hubsApart : ∀ h ∈ hubs, ∀ j ∈ hubs, h ≠ j → ¬ nearby 16 h j
  hubRunApart : ∀ h ∈ hubs, ∀ s ∈ runs, ¬ Incident s h → ∀ q, s.Axis q → ¬ nearby 8 h q
  runsApart : ∀ s ∈ runs, ∀ t ∈ runs, s ≠ t → FarRuns s t ∨ DifferAtHub s t

namespace Layout

def IsOptional (A : Layout) (p : Center) : Prop :=
  (∃ h ∈ A.hubs, (A.model h).CoreOptional p) ∨ ∃ s ∈ A.runs, s.Optional p

def IsGuard (A : Layout) (p : Center) : Prop :=
  (∃ h ∈ A.hubs, (A.model h).CoreGuard p) ∨ ∃ s ∈ A.runs, s.Guard p

def IsLink (A : Layout) (p q : Center) : Prop :=
  (∃ h ∈ A.hubs, (A.model h).CoreLink p q) ∨ ∃ s ∈ A.runs, s.Link p q

instance (A : Layout) (p : Center) : Decidable (A.IsOptional p) := by
  unfold IsOptional ModelAt.CoreOptional Run.Optional
  infer_instance

instance (A : Layout) (p : Center) : Decidable (A.IsGuard p) := by
  unfold IsGuard ModelAt.CoreGuard Run.Guard
  infer_instance

instance (A : Layout) (p q : Center) : Decidable (A.IsLink p q) := by
  unfold IsLink ModelAt.CoreLink Run.Link
  infer_instance

def roles (A : Layout) (p : Center) : Role :=
  if A.IsOptional p then .optional else if A.IsGuard p then .guard else .empty

def links (A : Layout) (p q : Center) : Bool := decide (A.IsLink p q)

private theorem roles_congr {A : Layout} {p : Center} {r : Role}
    (ho : A.IsOptional p ↔ r = .optional) (hg : A.IsGuard p ↔ r = .guard) : A.roles p = r := by
  classical
  cases r <;> simp_all [roles]

theorem oriented_long (A : Layout) {s : Run} (hs : Oriented A.runs s) : 17 ≤ s.length := by
  rcases hs with h | h
  · exact A.long s h
  · exact A.long s.reverse h

theorem oriented_optional (A : Layout) {s : Run} (hs : Oriented A.runs s) {p : Center}
    (h : s.Optional p) : ∃ t ∈ A.runs, t.Optional p := by
  rcases hs with hs | hs
  · exact ⟨s, hs, h⟩
  · exact ⟨s.reverse, hs, (s.reverse_optional p).mpr h⟩

theorem oriented_guard (A : Layout) {s : Run} (hs : Oriented A.runs s) {p : Center}
    (h : s.Guard p) : ∃ t ∈ A.runs, t.Guard p := by
  rcases hs with hs | hs
  · exact ⟨s, hs, h⟩
  · exact ⟨s.reverse, hs, (s.reverse_guard (A.phase s.reverse hs) p).mpr h⟩

theorem oriented_link (A : Layout) {s : Run} (hs : Oriented A.runs s) {p q : Center}
    (h : s.Link p q) : ∃ t ∈ A.runs, t.Link p q := by
  rcases hs with hs | hs
  · exact ⟨s, hs, h⟩
  · exact ⟨s.reverse, hs, (s.reverse_link p q).mpr h⟩

theorem collar_only_core (A : Layout) {h j p : Center} (hh : h ∈ A.hubs) (hj : j ∈ A.hubs)
    (hp : nearby 7 h p) (jp : nearby 3 j p) : j = h := by
  by_contra ne
  have hjh := nearby_trans hp (nearby_symm.mp jp)
  exact (A.hubsApart h hh j hj (fun eq => ne eq.symm))
    (nearby_mono (by decide : (7 + 3 : ℤ) ≤ 16) hjh)

theorem collar_incident (A : Layout) {h p : Center} {s : Run} (hh : h ∈ A.hubs)
    (hs : s ∈ A.runs) (hp : nearby 7 h p) (ht : s.Tube p) : Incident s h := by
  by_contra hno
  obtain ⟨q, hq, hpq⟩ := Run.close_axis ht
  exact A.hubRunApart h hh s hs hno q hq (nearby_trans hp hpq)

theorem collar_optional (A : Layout) {h p : Center} (hh : h ∈ A.hubs) (hp : nearby 7 h p) :
    A.IsOptional p ↔ (A.model h).stencil.roles ((A.model h).localize.point p) = .optional := by
  rw [(A.model h).optional]
  constructor
  · rintro (⟨j, hj, hm⟩ | ⟨s, hs, hm⟩)
    · have eq := A.collar_only_core hh hj hp hm.1
      subst j
      exact Or.inl hm
    · rcases A.collar_incident hh hs hp (Run.optional_tube hm) with hstart | hfinish
      · have hlocal : nearby 7 s.start p := hstart.symm ▸ hp
        have hout := (Run.collar_optional (A.long s hs) hlocal).mp hm
        exact Or.inr ⟨s.dir, (A.port h hh _).mpr ⟨s, Or.inl hs, hstart, rfl⟩, hstart ▸ hout⟩
      · have hrev : s.reverse.start = h := hfinish
        have hlocal : nearby 7 s.reverse.start p := hrev.symm ▸ hp
        have hout := (Run.collar_optional (s := s.reverse) (A.long s hs) hlocal).mp
          ((s.reverse_optional p).mpr hm)
        exact Or.inr ⟨s.reverse.dir,
          (A.port h hh _).mpr ⟨s.reverse, Or.inr (by simpa using hs), hfinish, rfl⟩,
          show (Run.ray h s.reverse.dir).RayOptional p from hrev ▸ hout⟩
  · rintro (hm | ⟨d, hd, hm⟩)
    · exact Or.inl ⟨h, hh, hm⟩
    · obtain ⟨s, hs, rfl, rfl⟩ := (A.port h hh d).mp hd
      exact Or.inr (A.oriented_optional hs ((Run.collar_optional (A.oriented_long hs) hp).mpr hm))

theorem collar_guard (A : Layout) {h p : Center} (hh : h ∈ A.hubs) (hp : nearby 7 h p) :
    A.IsGuard p ↔ (A.model h).stencil.roles ((A.model h).localize.point p) = .guard := by
  rw [(A.model h).guard]
  constructor
  · rintro (⟨j, hj, hm⟩ | ⟨s, hs, hm⟩)
    · have eq := A.collar_only_core hh hj hp hm.1
      subst j
      exact Or.inl hm
    · rcases A.collar_incident hh hs hp (Run.guard_tube hm) with hstart | hfinish
      · have hlocal : nearby 7 s.start p := hstart.symm ▸ hp
        have hout := (Run.collar_guard (A.long s hs) hlocal).mp hm
        exact Or.inr ⟨s.dir, (A.port h hh _).mpr ⟨s, Or.inl hs, hstart, rfl⟩, hstart ▸ hout⟩
      · have hrev : s.reverse.start = h := hfinish
        have hlocal : nearby 7 s.reverse.start p := hrev.symm ▸ hp
        have hout := (Run.collar_guard (s := s.reverse) (A.long s hs) hlocal).mp
          ((s.reverse_guard (A.phase s hs) p).mpr hm)
        exact Or.inr ⟨s.reverse.dir,
          (A.port h hh _).mpr ⟨s.reverse, Or.inr (by simpa using hs), hfinish, rfl⟩,
          show (Run.ray h s.reverse.dir).RayGuard p from hrev ▸ hout⟩
  · rintro (hm | ⟨d, hd, hm⟩)
    · exact Or.inl ⟨h, hh, hm⟩
    · obtain ⟨s, hs, rfl, rfl⟩ := (A.port h hh d).mp hd
      exact Or.inr (A.oriented_guard hs ((Run.collar_guard (A.oriented_long hs) hp).mpr hm))

theorem collar_link (A : Layout) {h p q : Center} (hh : h ∈ A.hubs)
    (hp : nearby 7 h p) (hq : nearby 7 h q) :
    A.IsLink p q ↔ (A.model h).stencil.links ((A.model h).localize.point p) ((A.model h).localize.point q) = true := by
  rw [(A.model h).links]
  constructor
  · rintro (⟨j, hj, hm⟩ | ⟨s, hs, hm⟩)
    · have eq := A.collar_only_core hh hj hp hm.1
      subst j
      exact Or.inl hm
    · rcases A.collar_incident hh hs hp (Run.link_tube hm).1 with hstart | hfinish
      · have hlocal : nearby 7 s.start p := hstart.symm ▸ hp
        have hlocal' : nearby 7 s.start q := hstart.symm ▸ hq
        have hout := (Run.collar_link (A.long s hs) hlocal hlocal').mp hm
        exact Or.inr ⟨s.dir, (A.port h hh _).mpr ⟨s, Or.inl hs, hstart, rfl⟩, hstart ▸ hout⟩
      · have hrev : s.reverse.start = h := hfinish
        have hlocal : nearby 7 s.reverse.start p := hrev.symm ▸ hp
        have hlocal' : nearby 7 s.reverse.start q := hrev.symm ▸ hq
        have hout := (Run.collar_link (s := s.reverse) (A.long s hs) hlocal hlocal').mp
          ((s.reverse_link p q).mpr hm)
        exact Or.inr ⟨s.reverse.dir,
          (A.port h hh _).mpr ⟨s.reverse, Or.inr (by simpa using hs), hfinish, rfl⟩,
          show (Run.ray h s.reverse.dir).RayLink p q from hrev ▸ hout⟩
  · rintro (hm | ⟨d, hd, hm⟩)
    · exact Or.inl ⟨h, hh, hm⟩
    · obtain ⟨s, hs, rfl, rfl⟩ := (A.port h hh d).mp hd
      exact Or.inr (A.oriented_link hs ((Run.collar_link (A.oriented_long hs) hp hq).mpr hm))

def AwayFromHubs (A : Layout) (p : Center) : Prop :=
  ∀ h ∈ A.hubs, ¬ nearby 5 h p

theorem patch_no_core (A : Layout) {p q h : Center} (away : A.AwayFromHubs p)
    (hh : h ∈ A.hubs) (hpq : nearby 2 p q) : ¬ nearby 3 h q := by
  intro hc
  exact away h hh (nearby_trans hc (nearby_symm.mp hpq))

theorem patch_unique_run (A : Layout) {s t : Run} {p q u : Center}
    (away : A.AwayFromHubs p) (hs : s ∈ A.runs) (ht : t ∈ A.runs)
    (sq : s.Tube q) (tu : t.Tube u) (pq : nearby 2 p q) (pu : nearby 2 p u) : t = s := by
  by_contra ne
  rcases A.runsApart s hs t ht (fun eq => ne eq.symm) with far | common
  · obtain ⟨a, ha, hqa⟩ := Run.close_axis sq
    obtain ⟨b, hb, hub⟩ := Run.close_axis tu
    exact far a b ha hb (nearby_trans (nearby_symm.mp hqa)
      (nearby_trans (nearby_symm.mp pq) (nearby_trans pu hub)))
  · obtain ⟨a, b, sa, tb, same, different⟩ := common
    have hh : a.start ∈ A.hubs := by
      rcases sa with heq | heq
      · rw [heq]; exact A.startHub s hs
      · rw [heq]; exact A.finishHub s hs
    have ha : a.Tube q := by rcases sa with heq | heq <;> simpa [heq] using sq
    have hb : b.Tube u := by rcases tb with heq | heq <;> simpa [heq] using tu
    exact away a.start hh (Run.neighboring_runs same.symm different ha hb pq pu)

theorem patch_optional (A : Layout) {s : Run} {p q z : Center} (away : A.AwayFromHubs p)
    (hs : s ∈ A.runs) (sq : s.Tube q) (pq : nearby 2 p q) (pz : nearby 2 p z) :
    A.IsOptional z ↔ s.Optional z := by
  constructor
  · rintro (⟨h, hh, hc⟩ | ⟨t, ht, ho⟩)
    · exact False.elim (A.patch_no_core away hh pz hc.1)
    · have eq := A.patch_unique_run away hs ht sq (Run.optional_tube ho) pq pz
      simpa [eq] using ho
  · exact fun ho => Or.inr ⟨s, hs, ho⟩

theorem patch_guard (A : Layout) {s : Run} {p q z : Center} (away : A.AwayFromHubs p)
    (hs : s ∈ A.runs) (sq : s.Tube q) (pq : nearby 2 p q) (pz : nearby 2 p z) :
    A.IsGuard z ↔ s.Guard z := by
  constructor
  · rintro (⟨h, hh, hc⟩ | ⟨t, ht, ho⟩)
    · exact False.elim (A.patch_no_core away hh pz hc.1)
    · have eq := A.patch_unique_run away hs ht sq (Run.guard_tube ho) pq pz
      simpa [eq] using ho
  · exact fun ho => Or.inr ⟨s, hs, ho⟩

theorem patch_link (A : Layout) {s : Run} {p q z w : Center} (away : A.AwayFromHubs p)
    (hs : s ∈ A.runs) (sq : s.Tube q) (pq : nearby 2 p q) (pz : nearby 2 p z) :
    A.IsLink z w ↔ s.Link z w := by
  constructor
  · rintro (⟨h, hh, hc⟩ | ⟨t, ht, ho⟩)
    · exact False.elim (A.patch_no_core away hh pz hc.1)
    · have eq := A.patch_unique_run away hs ht sq (Run.link_tube ho).1 pq pz
      simpa [eq] using ho
  · exact fun ho => Or.inr ⟨s, hs, ho⟩

theorem exists_strip_of_seed (A : Layout) {p q : Center} (away : A.AwayFromHubs p)
    (pq : nearby 2 p q) (seed : A.roles q ≠ .empty) :
    ∃ s ∈ A.runs, s.Tube q := by
  classical
  have existsRole : A.IsOptional q ∨ A.IsGuard q := by
    by_contra none
    exact seed (by simp [roles, not_or.mp none])
  rcases existsRole with (⟨h,hh,hc⟩ | ⟨s,hs,ho⟩) | (⟨h,hh,hc⟩ | ⟨s,hs,hg⟩)
  · exact False.elim (A.patch_no_core away hh pq hc.1)
  · exact ⟨s,hs,Run.optional_tube ho⟩
  · exact False.elim (A.patch_no_core away hh pq hc.1)
  · exact ⟨s,hs,Run.guard_tube hg⟩

theorem hasCertifiedPatches (A : Layout) : HasCertifiedPatches A.roles A.links := by
  classical
  intro p material
  by_cases existsHub : ∃ h ∈ A.hubs, nearby 5 h p
  · obtain ⟨h, hh, hp⟩ := existsHub
    let M := A.model h
    have hclose : ∀ q ∈ box 2 p, nearby 7 h q :=
      fun q hq => nearby_trans hp (mem_box.mp hq)
    refine ⟨M.stencil.roles, M.stencil.links, M.localize, ?_, ?_, ?_⟩
    · intro q hq
      exact roles_congr (A.collar_optional hh (hclose q hq)) (A.collar_guard hh (hclose q hq))
    · intro q hq r hr
      apply Bool.eq_iff_iff.mpr
      simpa only [links, decide_eq_true_eq] using A.collar_link hh (hclose q hq) (hclose r hr)
    · exact M.checked _ (mem_box.mpr ((M.near 5 p).mpr hp))
  · have away : A.AwayFromHubs p := fun h hh near => existsHub ⟨h, hh, near⟩
    obtain ⟨q, hq, material⟩ := material
    obtain ⟨s, hs, sq⟩ := A.exists_strip_of_seed away (mem_box.mp hq) material
    have clip : ∀ z ∈ box 2 p, 4 ≤ s.alongAt z ∧ s.alongAt z ≤ s.length - 4 :=
      fun z hz => Run.patch_longitudinal sq (mem_box.mp hq) (away _ (A.startHub s hs))
        (away _ (A.finishHub s hs)) z (mem_box.mp hz)
    let g := s.dir.localFrame s.start
    refine ⟨wireRoles 0, wireLinks, g, ?_, ?_, wire_raw 0 (g.point p)⟩
    · intro z hz
      have hc := clip z hz
      apply roles_congr
      · rw [A.patch_optional away hs sq (mem_box.mp hq) (mem_box.mp hz)]
        change s.Optional z ↔ wireRoles 0 ((s.dir.localFrame s.start).point z) = .optional
        rw [Direction.frame_at]
        change s.Optional z ↔ wireRoles 0 (s.alongAt z, s.acrossAt z) = .optional
        by_cases hzero : s.acrossAt z = 0
        · simp [Run.Optional, wireRoles, hc.1, hc.2, hzero]
        · simp only [Run.Optional, wireRoles, hc.1, hc.2, hzero, ite_false, true_and]
          split_ifs <;> decide
      · rw [A.patch_guard away hs sq (mem_box.mp hq) (mem_box.mp hz)]
        change s.Guard z ↔ wireRoles 0 ((s.dir.localFrame s.start).point z) = .guard
        rw [Direction.frame_at]
        change s.Guard z ↔ wireRoles 0 (s.alongAt z, s.acrossAt z) = .guard
        simp only [Run.Guard, hc.1, hc.2, true_and, wireRoles]
        split_ifs <;> simp_all
    · intro z hz w hw
      have cz := clip z hz
      have cw := clip w hw
      apply Bool.eq_iff_iff.mpr
      simp only [links, decide_eq_true_eq]
      rw [A.patch_link away hs sq (mem_box.mp hq) (mem_box.mp hz)]
      change s.Link z w ↔ wireLinks ((s.dir.localFrame s.start).point z)
        ((s.dir.localFrame s.start).point w) = true
      rw [Direction.frame_at, Direction.frame_at]
      change s.Link z w ↔ wireLinks (s.alongAt z, s.acrossAt z) (s.alongAt w, s.acrossAt w) = true
      simp only [Run.Link, wireLinks, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨_,_, a⟩, ⟨_,_,b⟩,c⟩
        exact ⟨a,b,c⟩
      · rintro ⟨a,b,c⟩
        exact ⟨⟨by omega, by omega, a⟩, ⟨by omega, by omega, b⟩, c⟩

end Layout

end GridCover.Placement
