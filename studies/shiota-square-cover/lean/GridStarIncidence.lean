import GridPlacementModels
import GridCorePaths
import GridStridePath

namespace GridCover.LocalCore

open GridCover.Placement GridCover.CorePaths GridCover.PathEmbedding.Stride17

def armAt (h : Center) (d : Direction) (tee : Bool) : List Center :=
  if tee then [h,d.atSite h 2,d.atSite h 3]
  else [h,d.atSite h 1,d.atSite h 2,d.atSite h 3]

def armPair (h : Center) (d : Direction) (tee : Bool) (p q : Center) : Prop :=
  (p,q) ∈ (armAt h d tee).zip (armAt h d tee).tail ∨
  (q,p) ∈ (armAt h d tee).zip (armAt h d tee).tail

private def listedDirections : List Direction := [.east,.west,.north,.south]

private theorem listedDirections_all (d : Direction) : d ∈ listedDirections := by
  cases d <;> decide

private def armPaths (k : Shape) : List (List Center) :=
  (listedDirections.filter (fun d => decide (d ∈ k.ports))).map (fun d => arm d (decide (k = .tee)))

private theorem armPaths_skeleton {k : Shape} (h : k ≠ .paritySwitch) :
    isSkeleton k.stencil (armPaths k) := by
  cases k with
  | endCap => exact all_fixed_skeletons.1
  | straight => exact all_fixed_skeletons.2.2.2.1
  | elbow => exact all_fixed_skeletons.2.1
  | tee => exact all_fixed_skeletons.2.2.1
  | paritySwitch => exact (h rfl).elim

private theorem mem_armPaths {k : Shape} {path : List Center} :
    path ∈ armPaths k ↔ ∃ d ∈ k.ports, arm d (decide (k = .tee)) = path := by
  simp [armPaths, listedDirections_all]

theorem localize_atSite (o : Orientation) (h : Center) (d : Direction) (x : ℤ) :
    (o.atHub h).point (d.atSite h x) = (o.dir d).atSite (0,0) x := by
  rcases o with ⟨s,a,b⟩
  cases s <;> cases a <;> cases b <;> cases d <;>
    simp [Direction.atSite, Orientation.dir, Orientation.apply, Direction.swapped,
      Direction.flipX, Direction.flipY, sub]

private theorem localize_hub (o : Orientation) (h : Center) :
    (o.atHub h).point h = (0,0) := by
  have he := localize_atSite o h .east 0
  cases hd : o.dir .east <;> simpa [hd, Direction.atSite] using he

theorem map_armAt (o : Orientation) (h : Center) (d : Direction) (b : Bool) :
    (armAt h d b).map (o.atHub h).point = arm (o.dir d) b := by
  cases b <;> simp [arm,armAt,localize_atSite,localize_hub, -Orientation.atHub_point]

theorem armAt_near (h : Center) (d : Direction) (b : Bool) (p : Center)
    (hp : p ∈ armAt h d b) : nearby 3 h p := by
  have step (t : ℤ) (lo : 0 ≤ t) (hi : t ≤ 3) : nearby 3 h (d.atSite h t) := by
    cases d <;> simp [nearby, Direction.atSite] <;> omega
  cases b
  · simp [armAt] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact nearby_refl (r := 3) (by decide) _
    · exact step 1 (by decide) (by decide)
    · exact step 2 (by decide) (by decide)
    · exact step 3 (by decide) (by decide)
  · simp [armAt] at hp
    rcases hp with rfl | rfl | rfl
    · exact nearby_refl (r := 3) (by decide) _
    · exact step 2 (by decide) (by decide)
    · exact step 3 (by decide) (by decide)

theorem map_arm_mem (o : Orientation) (h : Center) (d : Direction) (b : Bool) (p : Center) :
    (o.atHub h).point p ∈ arm (o.dir d) b ↔ p ∈ armAt h d b := by
  rw [← map_armAt o h d b]
  simp only [List.mem_map, Equiv.apply_eq_iff_eq, exists_eq_right]

theorem armPair_iff (h : Center) (d : Direction) (b : Bool) (p q : Center) :
    armPair h d b p q ↔
      (p = h ∧ q = d.atSite h (1 + skip b)) ∨ (q = h ∧ p = d.atSite h (1 + skip b)) ∨
      (b = false ∧ ((p = d.atSite h 1 ∧ q = d.atSite h 2) ∨
        (q = d.atSite h 1 ∧ p = d.atSite h 2))) ∨
      (p = d.atSite h 2 ∧ q = d.atSite h 3) ∨ (q = d.atSite h 2 ∧ p = d.atSite h 3) := by
  cases b <;> simp [armPair, armAt, skip] <;> tauto

theorem armPair_near (h : Center) (d : Direction) (b : Bool) (p q : Center)
    (hp : armPair h d b p q) : nearby 3 h p ∧ nearby 3 h q := by
  refine ⟨armAt_near h d b p ?_, armAt_near h d b q ?_⟩
  all_goals cases b <;> simp [armPair,armAt] at hp ⊢ <;> tauto

theorem map_arm_pair (o : Orientation) (h : Center) (d : Direction) (b : Bool)
    (p q : Center) :
    (let path := arm (o.dir d) b
      let x := (o.atHub h).point p
      let y := (o.atHub h).point q
      (x,y) ∈ path.zip path.tail ∨ (y,x) ∈ path.zip path.tail) ↔ armPair h d b p q := by
  change armPair (0,0) (o.dir d) b ((o.atHub h).point p) ((o.atHub h).point q) ↔ _
  rw [armPair_iff, armPair_iff]
  simp only [← localize_atSite o h d]
  simp only [← localize_hub o h, Equiv.apply_eq_iff_eq]

theorem normal_corePoint {k : Shape} {o : Orientation} {h : Center} (hne : k ≠ .paritySwitch)
    (p : Center) :
    (k.model o h).CoreOptional p ↔
      ∃ d ∈ orientedPorts k.ports o, p ∈ armAt h d (decide (k = .tee)) := by
  change (nearby 3 h p ∧ (o.atHub h).point p ∈ k.stencil.optional) ↔ _
  rw [skeleton_point_iff (armPaths_skeleton hne)]
  constructor
  · rintro ⟨_,path,hp,hm⟩
    obtain ⟨c,hc,rfl⟩ := mem_armPaths.mp hp
    obtain ⟨d,rfl⟩ := o.dir_surj c
    exact ⟨d,mem_orientedPorts.mpr hc,(map_arm_mem o h d _ p).mp hm⟩
  · rintro ⟨d,hd,hp⟩
    have ha := armAt_near h d _ p hp
    have hm := (map_arm_mem o h d _ p).mpr hp
    exact ⟨ha,_,mem_armPaths.mpr ⟨_,mem_orientedPorts.mp hd,rfl⟩,hm⟩

theorem normal_coreLink {k : Shape} {o : Orientation} {h : Center} (hne : k ≠ .paritySwitch)
    (p q : Center) :
    (k.model o h).CoreLink p q ↔
      ∃ d ∈ orientedPorts k.ports o, armPair h d (decide (k = .tee)) p q := by
  change (nearby 3 h p ∧ nearby 3 h q ∧
    (((o.atHub h).point p,(o.atHub h).point q) ∈ k.stencil.graph ∨
     ((o.atHub h).point q,(o.atHub h).point p) ∈ k.stencil.graph)) ↔ _
  rw [skeleton_link_iff (armPaths_skeleton hne)]
  constructor
  · rintro ⟨_,_,path,hp,hm⟩
    obtain ⟨c,hc,rfl⟩ := mem_armPaths.mp hp
    obtain ⟨d,rfl⟩ := o.dir_surj c
    exact ⟨d,mem_orientedPorts.mpr hc,(map_arm_pair o h d _ p q).mp hm⟩
  · rintro ⟨d,hd,hp⟩
    obtain ⟨hn,hm⟩ := armPair_near h d _ p q hp
    exact ⟨hn,hm,_,mem_armPaths.mpr ⟨_,mem_orientedPorts.mp hd,rfl⟩,
      (map_arm_pair o h d _ p q).mpr hp⟩

end GridCover.LocalCore
