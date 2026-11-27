import AxisGridCoreArithmetic
import GridStarIncidence
import GridConcretePathJoin

namespace GridCover.AxisGridSourceCore

open AxisPieces GridCover.Placement GridCover.CorePaths GridCover.LocalCore
open GridCover.PathEmbedding.Stride17

variable {V : Type} [DecidableEq V] (D : AxisGridSource.Drawing V)

omit [DecidableEq V] in
theorem sourceDir_eq (e : V × V) : sourceDir D e = D.direction e := by
  unfold sourceDir AxisGridSource.Drawing.direction
  cases D.axis e <;> rfl

omit [DecidableEq V] in
theorem left_atSite (e : V × V) (s : ℤ) :
    unplace D e ((sourceDir D e).atSite (scalePoint (D.hub e.1)) s) = (s,0) := by
  change unplace D e ((sourceDir D e).atSite (hubPoint D e.1) s) = (s,0)
  rw [← world_axis (sourceDir D e) (hubPoint D e.1) s]
  exact (world (sourceDir D e) (hubPoint D e.1)).symm_apply_apply (s,0)

omit [DecidableEq V] in
theorem right_atSite {e : V × V} (he : e ∈ D.edges) (s : ℤ) :
    centered (2 * D.length e)
      (unplace D e ((sourceDir D e).opposite.atSite (scalePoint (D.hub e.2)) s)) = (-s,0) := by
  have start : scalePoint (D.hub e.2) = (sourceDir D e).atSite
      (scalePoint (D.hub e.1)) (34 * (D.length e : ℤ)) := (end_hub D he).symm
  rw [start]
  have back : (sourceDir D e).opposite.atSite
      ((sourceDir D e).atSite (scalePoint (D.hub e.1)) (34 * (D.length e : ℤ))) s =
      (sourceDir D e).atSite (scalePoint (D.hub e.1)) (34 * (D.length e : ℤ) - s) := by
    cases sourceDir D e <;> simp [Direction.atSite,Direction.opposite] <;> omega
  rw [back,left_atSite]
  apply Prod.ext
  · simp [centered]
    omega
  · rfl

private theorem move_arm_point (f : Center → Center) (inj : Function.Injective f)
    (h : Center) (d d' : Direction) (b : Bool) (p : Center)
    (hh : f h = (0,0))
    (hs : ∀ t, f (d.atSite h t) = d'.atSite (0,0) t) :
    p ∈ armAt h d b ↔ f p ∈ arm d' b := by
  cases b <;> simp [armAt,arm] <;> simp only [← hs] <;> simp only [← hh,inj.eq_iff]

private theorem move_arm_link (f : Center → Center) (inj : Function.Injective f)
    (h : Center) (d d' : Direction) (b : Bool) (p q : Center)
    (hh : f h = (0,0))
    (hs : ∀ t, f (d.atSite h t) = d'.atSite (0,0) t) :
    armPair h d b p q ↔ pairMem (arm d' b) (f p) (f q) := by
  change armPair h d b p q ↔ armPair (0,0) d' b (f p) (f q)
  rw [armPair_iff,armPair_iff]
  simp only [← hs]
  simp only [← hh,inj.eq_iff]

private theorem centered_injective (i : ℕ) : Function.Injective (centered i) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simp [centered] at h ⊢
  exact h

theorem leftPoint {e : V × V} (he : e ∈ D.edges) (p : Center) :
    p ∈ armAt (scalePoint (D.hub e.1)) (D.direction e) (leftTee D e) ↔ worldCorePoint D e 0 p := by
  unfold worldCorePoint
  rw [corePoint_left (D.length_pos he)]
  apply move_arm_point (unplace D e) (unplace D e).injective
  · exact unplace_start D e
  · intro t
    simpa [Direction.atSite,sourceDir_eq] using left_atSite D e t

theorem leftLink {e : V × V} (he : e ∈ D.edges) (p q : Center) :
    armPair (scalePoint (D.hub e.1)) (D.direction e) (leftTee D e) p q ↔ worldCoreLink D e 0 p q := by
  unfold worldCoreLink
  rw [coreLink_left (D.length_pos he)]
  apply move_arm_link (unplace D e) (unplace D e).injective
  · exact unplace_start D e
  · intro t
    simpa [Direction.atSite,sourceDir_eq] using left_atSite D e t

theorem rightPoint {e : V × V} (he : e ∈ D.edges) (p : Center) :
    p ∈ armAt (scalePoint (D.hub e.2)) (D.direction e).opposite (rightTee D e) ↔
      worldCorePoint D e (2 * D.length e) p := by
  unfold worldCorePoint
  rw [corePoint_right (D.length_pos he)]
  apply move_arm_point (fun q => centered (2 * D.length e) (unplace D e q))
    ((centered_injective _).comp (unplace D e).injective)
  · simpa [start_point] using right_atSite D he 0
  · intro t
    simpa [Direction.atSite,sourceDir_eq] using right_atSite D he t

theorem rightLink {e : V × V} (he : e ∈ D.edges) (p q : Center) :
    armPair (scalePoint (D.hub e.2)) (D.direction e).opposite (rightTee D e) p q ↔
      worldCoreLink D e (2 * D.length e) p q := by
  unfold worldCoreLink
  rw [coreLink_right (D.length_pos he)]
  apply move_arm_link (fun q => centered (2 * D.length e) (unplace D e q))
    ((centered_injective _).comp (unplace D e).injective)
  · simpa [start_point] using right_atSite D he 0
  · intro t
    simpa [Direction.atSite,sourceDir_eq] using right_atSite D he t

omit [DecidableEq V] in
theorem core_local_coordinates (e : V × V) (i : ℕ) (p : Center) :
    ((D.axisOrientation e).atHub (scalePoint (D.site e i))).point p =
      centered i (unplace D e p) := by
  change _ = centered i (((sourceDir D e).localFrame (hubPoint D e.1)).point p)
  simp only [Direction.frame_at,Orientation.atHub_point]
  unfold AxisGridSource.Drawing.axisOrientation AxisGridSource.Drawing.site
    AxisGridSource.site AxisGridSource.Drawing.axis
  unfold sourceDir hubPoint AxisGridSource.Drawing.hub
  cases hd : AxisGridSource.axis (D.coordinate e.1) (D.coordinate e.2) <;>
    simp [AxisGridSource.Drawing.axis, hd, toDir, Direction.longitudinal, Direction.lateral,
      AxisGridSource.advance, Orientation.apply, scalePoint, pitch, sub, centered] <;> omega

theorem switchAt_core_index {e : V × V} (he : e ∈ D.edges) {i : ℕ}
    (hi : 0 < i) (hil : i < 2 * D.length e) :
    D.switchAt (scalePoint (D.site e i)) = isSwitchIndex (leftTee D e) (rightTee D e) i := by
  apply Bool.eq_iff_iff.mpr
  rw [D.switchAt_site he hi hil,D.even_tees_iff]
  simp [isSwitchIndex,useSwitch,AxisGridSource.Drawing.leftTee,AxisGridSource.Drawing.rightTee,
    leftTee,rightTee]

private theorem exactCoreSkeleton (b : Bool) :
    isSkeleton (if b then Shape.paritySwitch else Shape.straight).stencil (corePaths b) := by
  cases b
  · exact all_fixed_skeletons.2.2.2.1
  · exact all_fixed_skeletons.2.2.2.2

private theorem corePoints_near (b : Bool) :
    ∀ p ∈ skeletonPoints (corePaths b), nearby 3 (0,0) p := by
  cases b <;> decide

private theorem corePair_near (b : Bool) (x y : Center)
    (h : ∃ path ∈ corePaths b, pairMem path x y) :
    nearby 3 (0,0) x ∧ nearby 3 (0,0) y := by
  obtain ⟨path,hp,h⟩ := h
  have near (p : Center) (h : p ∈ path) : nearby 3 (0,0) p :=
    corePoints_near b p (by simp [skeletonPoints]; exact ⟨path,hp,h⟩)
  have pairNear (x y : Center) (h : (x,y) ∈ path.zip path.tail) :
      nearby 3 (0,0) x ∧ nearby 3 (0,0) y := by
    obtain ⟨hx,hy⟩ := List.of_mem_zip h
    exact ⟨near x hx,near y (List.tail_subset path hy)⟩
  rcases h with h | h
  · exact pairNear _ _ h
  · exact (pairNear _ _ h).symm

theorem interiorPoint (hdeg : D.boundedDegree) {e : V × V} (he : e ∈ D.edges) {i : ℕ}
    (hi : 0 < i) (hil : i < 2 * D.length e) (p : Center) :
    ((D.certifiedLayout hdeg).model (scalePoint (D.site e i))).CoreOptional p ↔
      worldCorePoint D e i p := by
  rw [D.inside_model_exact hdeg he (D.mem_inside.mpr ⟨i,hi,hil,rfl⟩),
    switchAt_core_index D he hi hil]
  let b := isSwitchIndex (leftTee D e) (rightTee D e) i
  let h := scalePoint (D.site e i)
  let o := D.axisOrientation e
  change (nearby 3 h p ∧ _ ∈ (if b then Shape.paritySwitch else Shape.straight).stencil.optional) ↔ _
  rw [(exactCoreSkeleton b).1]
  unfold worldCorePoint
  rw [corePoint_inside hi hil, ← core_local_coordinates D e i p]
  constructor
  · exact And.right
  · intro hp
    exact ⟨(o.atHub_near h 3 p).mp (corePoints_near b _ hp),hp⟩

theorem interiorLink (hdeg : D.boundedDegree) {e : V × V} (he : e ∈ D.edges) {i : ℕ}
    (hi : 0 < i) (hil : i < 2 * D.length e) (p q : Center) :
    ((D.certifiedLayout hdeg).model (scalePoint (D.site e i))).CoreLink p q ↔ worldCoreLink D e i p q := by
  rw [D.inside_model_exact hdeg he (D.mem_inside.mpr ⟨i,hi,hil,rfl⟩),
    switchAt_core_index D he hi hil]
  let b := isSwitchIndex (leftTee D e) (rightTee D e) i
  let h := scalePoint (D.site e i)
  let o := D.axisOrientation e
  let x := (o.atHub h).point p
  let y := (o.atHub h).point q
  change (nearby 3 h p ∧ nearby 3 h q ∧
    ((x,y) ∈ (if b then Shape.paritySwitch else Shape.straight).stencil.graph ∨
     (y,x) ∈ (if b then Shape.paritySwitch else Shape.straight).stencil.graph)) ↔ _
  rw [skeleton_link_iff (exactCoreSkeleton b)]
  dsimp [x,y]
  unfold worldCoreLink
  rw [coreLink_inside hi hil,← core_local_coordinates D e i p,← core_local_coordinates D e i q]
  constructor
  · exact fun hp => hp.2.2
  · intro hp
    have hn := corePair_near b _ _ hp
    exact ⟨(o.atHub_near h 3 p).mp hn.1,(o.atHub_near h 3 q).mp hn.2,hp⟩

end GridCover.AxisGridSourceCore
