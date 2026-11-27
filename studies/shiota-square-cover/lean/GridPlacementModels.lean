import GridCoarseDrawing

namespace GridCover.Placement

namespace Direction

def all : Finset Direction := {.east, .west, .north, .south}

@[simp] theorem mem_all (d : Direction) : d ∈ all := by cases d <;> decide

def swapped : Direction → Direction
  | east => north | west => south | north => east | south => west

def flipX : Direction → Direction
  | east => west | west => east | north => north | south => south

def flipY : Direction → Direction
  | east => east | west => west | north => south | south => north

end Direction

structure Orientation where
  swap : Bool
  negX : Bool
  negY : Bool

namespace Orientation

def apply (o : Orientation) (p : Center) : Center :=
  let (x,y) := if o.swap then (p.2,p.1) else p
  (if o.negX then -x else x, if o.negY then -y else y)

def dir (o : Orientation) (d : Direction) : Direction :=
  let e := if o.swap then d.swapped else d
  let f := if o.negX then e.flipX else e
  if o.negY then f.flipY else f

def reflectY : GridIso := composeIso transposeGrid (composeIso reflectX transposeGrid)

def iso (o : Orientation) : GridIso :=
  composeIso (if o.swap then transposeGrid else horizontalShift 0)
    (composeIso (if o.negX then reflectX else horizontalShift 0)
      (if o.negY then reflectY else horizontalShift 0))

@[simp] theorem reflectX_point (p : Center) : reflectX.point p = (-p.1,p.2) := rfl
@[simp] theorem reflectY_point (p : Center) : reflectY.point p = (p.1,-p.2) := rfl
@[simp] theorem transpose_point (p : Center) : transposeGrid.point p = (p.2,p.1) := rfl
@[simp] theorem shift0_point (p : Center) : (horizontalShift 0).point p = p := by
  change (p.1 + 0, p.2) = p
  simp

@[simp] theorem iso_point (o : Orientation) (p : Center) : o.iso.point p = o.apply p := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> simp [iso, apply]

theorem dir_surj (o : Orientation) : Function.Surjective o.dir := by
  rcases o with ⟨s,x,y⟩
  intro d
  cases s <;> cases x <;> cases y <;> cases d <;>
    first | exact ⟨.east, rfl⟩ | exact ⟨.west, rfl⟩ | exact ⟨.north, rfl⟩ | exact ⟨.south, rfl⟩

theorem along_preserved (o : Orientation) (p : Center) (d : Direction) :
    (o.dir d).longitudinal (o.apply p) = d.longitudinal p := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;>
    simp [dir, apply, Direction.swapped, Direction.flipX, Direction.flipY, Direction.longitudinal]

theorem lateral_preserved (o : Orientation) (p : Center) (d : Direction) :
    (o.dir d).lateral (o.apply p) = d.lateral p ∨
      (o.dir d).lateral (o.apply p) = -d.lateral p := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;>
    simp [dir, apply, Direction.swapped, Direction.flipX, Direction.flipY, Direction.lateral]

def atHub (o : Orientation) (h : Center) : GridIso :=
  composeIso (shiftGrid (-h.1,-h.2)) o.iso

@[simp] theorem atHub_point (o : Orientation) (h p : Center) :
    (o.atHub h).point p = o.apply (sub p h) := by
  simp [atHub, add, sub, sub_eq_add_neg]

theorem atHub_near (o : Orientation) (h : Center) (r : ℤ) (p : Center) :
    nearby r (0,0) ((o.atHub h).point p) ↔ nearby r h p := by
  rw [atHub_point]
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> simp [apply, nearby, sub] <;> omega

theorem atHub_along (o : Orientation) (h p : Center) (d : Direction) :
    along (o.dir d).vector ((o.atHub h).point p) = (Run.ray h d).alongAt p := by
  rw [atHub_point, Direction.along_vector, along_preserved]
  rfl

theorem atHub_across (o : Orientation) (h p : Center) (d : Direction) :
    transverse (o.dir d).vector ((o.atHub h).point p) = (Run.ray h d).acrossAt p ∨
    transverse (o.dir d).vector ((o.atHub h).point p) = -(Run.ray h d).acrossAt p := by
  rw [atHub_point]
  rcases Direction.transverse_vector (o.dir d) (o.apply (sub p h)) with a | a <;>
    rcases o.lateral_preserved (sub p h) d with b | b <;>
    rw [a,b] <;> simp [Run.acrossAt, Run.ray]

theorem atHub_across_zero (o : Orientation) (h p : Center) (d : Direction) :
    transverse (o.dir d).vector ((o.atHub h).point p) = 0 ↔ (Run.ray h d).acrossAt p = 0 := by
  rcases o.atHub_across h p d with eq | eq
  · rw [eq]
  · rw [eq]; omega

theorem atHub_across_one (o : Orientation) (h p : Center) (d : Direction) :
    (transverse (o.dir d).vector ((o.atHub h).point p) = -1 ∨
     transverse (o.dir d).vector ((o.atHub h).point p) = 1) ↔
    ((Run.ray h d).acrossAt p = -1 ∨ (Run.ray h d).acrossAt p = 1) := by
  rcases o.atHub_across h p d with eq | eq
  · rw [eq]
  · rw [eq]; omega

theorem atHub_port (o : Orientation) (h : Center) (d : Direction) :
    (o.atHub h).point (d.atSite h 3) = (o.dir d).atSite (0,0) 3 := by
  rw [atHub_point]
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> cases d <;>
    simp [apply, dir, Direction.atSite, Direction.swapped, Direction.flipX, Direction.flipY, sub]

end Orientation

namespace Run

theorem ray_optional_outside {h p : Center} {d : Direction} (hp : (ray h d).RayOptional p) :
    ¬ nearby 3 h p := by
  intro near
  have bound := (near_start_iff (ray h d) 3 p).mp near
  unfold RayOptional at hp
  omega

theorem ray_guard_outside {h p : Center} {d : Direction} (hp : (ray h d).RayGuard p) :
    ¬ nearby 3 h p := by
  intro near
  have bound := (near_start_iff (ray h d) 3 p).mp near
  unfold RayGuard at hp
  omega

theorem ray_link_near {h p q : Center} {d : Direction} (hp : (ray h d).RayLink p q) :
    nearby 2 p q := by
  cases d <;>
    simp [RayLink, ray, alongAt, acrossAt, nearby, sub, Direction.longitudinal,
      Direction.lateral, unitApart] at hp ⊢ <;> omega

theorem ray_opt_guard_incompatible {h p : Center} {d e : Direction}
    (hp : (ray h d).RayOptional p) (hq : (ray h e).RayGuard p) : False := by
  cases d <;> cases e <;>
    simp [RayOptional, RayGuard, ray, alongAt, acrossAt, sub, Direction.longitudinal,
      Direction.lateral] at hp hq <;> omega

end Run

def rayCodes (ports : Finset Direction) : Finset (Center × ℤ) :=
  ports.image (fun d => (d.vector, 0))

def orientedPorts (ports : Finset Direction) (o : Orientation) : Finset Direction :=
  Direction.all.filter fun d => o.dir d ∈ ports

@[simp] theorem mem_orientedPorts {ports : Finset Direction} {o : Orientation} {d : Direction} :
    d ∈ orientedPorts ports o ↔ o.dir d ∈ ports := by simp [orientedPorts]

theorem exists_rays {S : Stencil} {ports : Finset Direction} (o : Orientation)
    (hrays : S.rays = rayCodes ports) (Q : Center × ℤ → Prop) (P : Direction → Prop)
    (compat : ∀ d, Q ((o.dir d).vector, 0) ↔ P d) :
    (∃ ray ∈ S.rays, Q ray) ↔ ∃ d ∈ orientedPorts ports o, P d := by
  rw [hrays]
  constructor
  · rintro ⟨ray, hr, hrQ⟩
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨e, rfl⟩ := o.dir_surj d
    exact ⟨e, mem_orientedPorts.mpr hd, (compat e).mp hrQ⟩
  · rintro ⟨d, hd, hP⟩
    exact ⟨_, Finset.mem_image.mpr ⟨o.dir d, mem_orientedPorts.mp hd, rfl⟩, (compat d).mpr hP⟩

def makeModel (h : Center) (S : Stencil) (canonical : Finset Direction) (o : Orientation)
    (hrays : S.rays = rayCodes canonical) (valid : S.dataValid)
    (raw : ∀ p ∈ box 5 (0,0), rawCheck S.roles S.links p)
    (site : ∀ d ∈ canonical, d.atSite (0,0) 3 ∈ S.optional) : ModelAt h where
  stencil := S
  localize := o.atHub h
  ports := orientedPorts canonical o
  near := o.atHub_near h
  checked := raw
  valid := valid
  portOptional := by
    intro d hd
    refine ⟨?_, ?_⟩
    · cases d <;> simp [Direction.atSite, nearby] <;> omega
    · rw [o.atHub_port]
      exact site (o.dir d) (mem_orientedPorts.mp hd)
  optional := by
    intro p
    have ho := exists_rays o hrays
      (fun r => 3 < along r.1 ((o.atHub h).point p) ∧ transverse r.1 ((o.atHub h).point p) = 0)
      (fun d => (Run.ray h d).RayOptional p) (by
        intro d
        simp only [o.atHub_along, o.atHub_across_zero, Run.RayOptional]
        omega)
    unfold Stencil.roles
    simp only [mem_box, o.atHub_near h, ho]
    by_cases core : nearby 3 h p
    · have noOpt : ¬ ∃ d ∈ orientedPorts canonical o, (Run.ray h d).RayOptional p := by
        rintro ⟨d,_,hd⟩
        exact Run.ray_optional_outside hd core
      simp only [core, ite_true, true_and, noOpt, or_false]
      split_ifs <;> simp_all
    · simp only [core, ite_false, false_and, false_or]
      split_ifs <;> simp_all
  guard := by
    intro p
    have ho := exists_rays o hrays
      (fun r => 3 < along r.1 ((o.atHub h).point p) ∧ transverse r.1 ((o.atHub h).point p) = 0)
      (fun d => (Run.ray h d).RayOptional p) (by
        intro d
        simp only [o.atHub_along, o.atHub_across_zero, Run.RayOptional]
        omega)
    have hg := exists_rays o hrays
      (fun r => 3 < along r.1 ((o.atHub h).point p) ∧
        (transverse r.1 ((o.atHub h).point p) = -1 ∨ transverse r.1 ((o.atHub h).point p) = 1) ∧
        inBand r.2 (along r.1 ((o.atHub h).point p)))
      (fun d => (Run.ray h d).RayGuard p) (by
        intro d
        simp only [o.atHub_along, o.atHub_across_one, Run.RayGuard]
        constructor <;> intro hp <;> exact ⟨by omega, hp.2⟩)
    unfold Stencil.roles
    simp only [mem_box, o.atHub_near h, ho, hg]
    by_cases core : nearby 3 h p
    · have noGuard : ¬ ∃ d ∈ orientedPorts canonical o, (Run.ray h d).RayGuard p := by
        rintro ⟨d,_,hd⟩
        exact Run.ray_guard_outside hd core
      simp only [core, ite_true, true_and, noGuard, or_false]
      split_ifs with nop hguard
      · simp only [false_iff]
        exact fun hmem => (Finset.disjoint_left.mp valid.1 hmem nop)
      · simp only [hguard, iff_self]
      · simp only [hguard, iff_self]
    · simp only [core, ite_false, false_and, false_or]
      split_ifs with op g
      · simp only [false_iff]
        rintro ⟨d,hd,hg'⟩
        obtain ⟨e,he,ho'⟩ := ho.mp op
        exact Run.ray_opt_guard_incompatible ho' hg'
      · exact ⟨fun _ => hg.mp g, fun _ => rfl⟩
      · exact ⟨fun h => by contradiction, fun h => False.elim (g (hg.mpr h))⟩
  links := by
    intro p q
    have hx := exists_rays o hrays
      (fun r => 3 ≤ along r.1 ((o.atHub h).point p) ∧ 3 ≤ along r.1 ((o.atHub h).point q) ∧
        transverse r.1 ((o.atHub h).point p) = 0 ∧ transverse r.1 ((o.atHub h).point q) = 0 ∧
        unitApart (along r.1 ((o.atHub h).point p)) (along r.1 ((o.atHub h).point q)))
      (fun d => (Run.ray h d).RayLink p q) (by
        intro d
        simp only [o.atHub_along, o.atHub_across_zero, Run.RayLink]
        exact ⟨fun hp => ⟨⟨hp.1,hp.2.2.1⟩, ⟨hp.2.1,hp.2.2.2.1⟩, hp.2.2.2.2⟩,
          fun hp => ⟨hp.1.1, hp.2.1.1, hp.1.2, hp.2.1.2, hp.2.2⟩⟩)
    simp only [Stencil.links, decide_eq_true_eq, hx]
    have coreEdge : ∀ p' q', ((o.atHub h).point p', (o.atHub h).point q') ∈ S.graph →
        nearby 3 h p' ∧ nearby 3 h q' ∧ nearby 2 ((o.atHub h).point p') ((o.atHub h).point q') := by
      intro p' q' hp
      obtain ⟨ha,hb,_,hc⟩ := valid.2.2.2.1 _ hp
      exact ⟨(o.atHub_near h 3 p').mp (mem_box.mp (valid.2.2.1 ha)),
        (o.atHub_near h 3 q').mp (mem_box.mp (valid.2.2.1 hb)), hc⟩
    constructor
    · rintro ⟨_, hp | hp | hp⟩
      · obtain ⟨ha,hb,_⟩ := coreEdge p q hp
        exact Or.inl ⟨ha,hb,Or.inl hp⟩
      · obtain ⟨ha,hb,_⟩ := coreEdge q p hp
        exact Or.inl ⟨hb,ha,Or.inr hp⟩
      · exact Or.inr hp
    · rintro (⟨_,_,hp | hp⟩ | ⟨d,hd,hx⟩)
      · exact ⟨(coreEdge p q hp).2.2, Or.inl hp⟩
      · exact ⟨nearby_symm.mp (coreEdge q p hp).2.2, Or.inr (Or.inl hp)⟩
      · exact ⟨((o.atHub h).close p q).mpr (Run.ray_link_near hx), Or.inr (Or.inr ⟨d,hd,hx⟩)⟩

inductive Shape
  | endCap | straight | elbow | tee | paritySwitch
  deriving DecidableEq

namespace Shape

def ports : Shape → Finset Direction
  | endCap => {.east}
  | straight | paritySwitch => {.east,.west}
  | elbow => {.east,.north}
  | tee => {.east,.north,.west}

def stencil : Shape → Stencil
  | endCap => Fixed.end_cap
  | straight => Fixed.line
  | elbow => Fixed.corner
  | tee => Fixed.tee
  | paritySwitch => Fixed.switch

theorem rays (k : Shape) : k.stencil.rays = rayCodes k.ports := by cases k <;> decide

theorem data (k : Shape) : k.stencil.dataValid := by
  cases k
  · exact Fixed.end_cap_data
  · exact Fixed.line_data
  · exact Fixed.corner_data
  · exact Fixed.tee_data
  · exact Fixed.switch_data

theorem raw (k : Shape) : ∀ p ∈ box 5 (0,0), rawCheck k.stencil.roles k.stencil.links p := by
  cases k
  · exact Fixed.end_cap_raw
  · exact Fixed.line_raw
  · exact Fixed.corner_raw
  · exact Fixed.tee_raw
  · exact Fixed.switch_raw

theorem site (k : Shape) : ∀ d ∈ k.ports, d.atSite (0,0) 3 ∈ k.stencil.optional := by
  intro d
  cases k <;> cases d <;> decide

def model (k : Shape) (o : Orientation) (h : Center) : ModelAt h :=
  makeModel h k.stencil k.ports o k.rays k.data k.raw k.site

end Shape

def orientationChoices : List Orientation :=
  [⟨false,false,false⟩, ⟨false,true,false⟩, ⟨false,false,true⟩, ⟨false,true,true⟩,
   ⟨true,false,false⟩, ⟨true,true,false⟩, ⟨true,false,true⟩, ⟨true,true,true⟩]

def modelChoices (flipParity : Bool) : List (Shape × Orientation) :=
  (if flipParity then [Shape.paritySwitch] else [.endCap,.straight,.elbow,.tee]).flatMap
    (fun k => orientationChoices.map (fun o => (k,o)))

def ValidPorts (flipParity : Bool) (P : Finset Direction) : Prop :=
  P.Nonempty ∧ P ≠ Direction.all ∧
    (flipParity = true → P = {.east,.west} ∨ P = {.north,.south})

instance (flipParity : Bool) (P : Finset Direction) : Decidable (ValidPorts flipParity P) := by
  unfold ValidPorts
  infer_instance

def pick (flipParity : Bool) (P : Finset Direction) : Option (Shape × Orientation) :=
  (modelChoices flipParity).find? (fun entry => decide (orientedPorts entry.1.ports entry.2 = P))

def maskBit (e w n s : Bool) : Direction → Bool
  | .east => e | .west => w | .north => n | .south => s

def mask (e w n s : Bool) : Finset Direction :=
  Direction.all.filter (fun p => maskBit e w n s p = true)

private theorem pick_masks (b e w n s : Bool) :
    ValidPorts b (mask e w n s) → (pick b (mask e w n s)).isSome = true := by
  cases b <;> cases e <;> cases w <;> cases n <;> cases s <;> intro valid <;>
    first
    | decide
    | have h : mask false false false false = ∅ := by decide
      have hn := valid.1
      rw [h] at hn
      simp at hn
    | exact False.elim (valid.2.1 (by decide))
    | rcases valid.2.2 rfl with bad | bad
      · exact False.elim ((by decide : _ ≠ _) bad)
      · exact False.elim ((by decide : _ ≠ _) bad)

theorem pick_exists (b : Bool) (P : Finset Direction) (hp : ValidPorts b P) :
    (pick b P).isSome = true := by
  have eq : mask (decide (.east ∈ P)) (decide (.west ∈ P))
      (decide (.north ∈ P)) (decide (.south ∈ P)) = P := by
    ext d
    unfold mask
    rw [Finset.mem_filter]
    simp only [Direction.mem_all, true_and]
    cases d <;> simp only [maskBit, decide_eq_true_eq]
  have hm := pick_masks b _ _ _ _ (show ValidPorts b _ by rwa [eq])
  rwa [eq] at hm

def selectModel (b : Bool) (P : Finset Direction) (h : Center) : ModelAt h :=
  let (k,o) := (pick b P).getD (.endCap, ⟨false,false,false⟩)
  k.model o h

theorem selectModel_ports (b : Bool) (P : Finset Direction) (h : Center) (ok : ValidPorts b P) :
    (selectModel b P h).ports = P := by
  have ne := pick_exists b P ok
  cases he : pick b P with
  | none => simp [he] at ne
  | some spec =>
    have good := List.find?_some (show (modelChoices b).find? _ = some spec from he)
    change decide (orientedPorts spec.1.ports spec.2 = P) = true at good
    simpa [selectModel, he, Shape.model, makeModel] using of_decide_eq_true good

theorem selectModel_spec (b : Bool) (P : Finset Direction) (h : Center) (ok : ValidPorts b P) :
    ∃ (k : Shape) (o : Orientation), selectModel b P h = k.model o h ∧
      orientedPorts k.ports o = P ∧ (k = .paritySwitch ↔ b = true) := by
  have ne := pick_exists b P ok
  cases he : pick b P with
  | none => simp [he] at ne
  | some spec =>
    rcases spec with ⟨k,o⟩
    have mem := List.mem_of_find?_eq_some (show (modelChoices b).find? _ = some (k,o) from he)
    have hm : k ∈ (if b then [Shape.paritySwitch] else [.endCap,.straight,.elbow,.tee]) := by
      unfold modelChoices at mem
      obtain ⟨k', hk', hk⟩ := List.mem_flatMap.mp mem
      obtain ⟨o', _, heq⟩ := List.mem_map.mp hk
      cases heq
      exact hk'
    refine ⟨k,o,by simp [selectModel,he],?_,?_⟩
    · simpa [selectModel, he, Shape.model, makeModel] using selectModel_ports b P h ok
    · cases b <;> cases k <;> simp_all

def isPort (R : Finset Run) (h : Center) (d : Direction) : Prop :=
  ∃ s ∈ R, (s.start = h ∧ s.dir = d) ∨ (s.finish = h ∧ s.dir.opposite = d)

instance (R : Finset Run) (h : Center) (d : Direction) : Decidable (isPort R h d) := by
  unfold isPort
  infer_instance

theorem isPort_iff {R : Finset Run} {h : Center} {d : Direction} :
    isPort R h d ↔ Outward R h d := by
  constructor
  · rintro ⟨s,hs,hi | hi⟩
    · exact ⟨s,Or.inl hs,hi⟩
    · exact ⟨s.reverse,Or.inr (by simpa using hs),hi⟩
  · rintro ⟨s,hs,he,hd⟩
    rcases hs with hs | hs
    · exact ⟨s,hs,Or.inl ⟨he,hd⟩⟩
    · have rev : s.reverse.dir.opposite = s.dir := by
        change s.dir.opposite.opposite = s.dir
        cases s.dir <;> rfl
      exact ⟨s.reverse,hs,Or.inr ⟨by simpa using he, by simpa [rev] using hd⟩⟩

def portsOf (R : Finset Run) (h : Center) : Finset Direction :=
  Direction.all.filter fun d => isPort R h d

@[simp] theorem portsOf_spec {R : Finset Run} {h : Center} {d : Direction} :
    d ∈ portsOf R h ↔ Outward R h d := by
  simp [portsOf, isPort_iff]

def CoarseDrawing.concrete (D : CoarseDrawing) (flipParity : Center → Bool)
    (valid : ∀ h ∈ D.shapeHubs, ValidPorts (flipParity h) (portsOf D.shapeRuns h)) : Layout :=
  D.assemble (fun h => selectModel (flipParity h) (portsOf D.shapeRuns h) h) (by
    intro h hh d
    rw [selectModel_ports _ _ _ (valid h hh)]
    exact portsOf_spec)

theorem CoarseDrawing.concrete_patches (D : CoarseDrawing) (flipParity : Center → Bool)
    (valid : ∀ h ∈ D.shapeHubs, ValidPorts (flipParity h) (portsOf D.shapeRuns h)) :
    HasCertifiedPatches (D.concrete flipParity valid).roles (D.concrete flipParity valid).links :=
  (D.concrete flipParity valid).hasCertifiedPatches

end GridCover.Placement
