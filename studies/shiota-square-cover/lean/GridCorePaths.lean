import GridPlacementGeometry
import GridFixedStencils

namespace GridCover.CorePaths

open GridCover.Placement

def arm (d : Direction) (tee : Bool) : List Center :=
  let h : Center := (0, 0)
  if tee then [h, d.atSite h 2, d.atSite h 3]
  else [h, d.atSite h 1, d.atSite h 2, d.atSite h 3]

def switchPath : List Center := [(-3,0), (-2,0), (0,1), (0,-1), (2,0), (3,0)]

def skeletonPoints (paths : List (List Center)) : Finset Center := paths.flatten.toFinset

def skeletonLinks (paths : List (List Center)) : Finset (Center × Center) :=
  (paths.flatMap fun path => path.zip path.tail).toFinset

def symmetric (edges : Finset (Center × Center)) := edges ∪ edges.image Prod.swap

def endPaths := [arm .east false]
def cornerPaths := [arm .east false, arm .north false]
def teePaths := [arm .east true, arm .west true, arm .north true]
def linePaths := [arm .east false, arm .west false]

/-- An exact equality of finite point and unoriented edge sets. This checks all
vertices and all links of the selected stencil. -/
def isSkeleton (s : Stencil) (paths : List (List Center)) : Prop :=
  s.optional = skeletonPoints paths ∧ symmetric s.graph = symmetric (skeletonLinks paths)

instance (s : Stencil) (paths : List (List Center)) : Decidable (isSkeleton s paths) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem all_fixed_skeletons :
    isSkeleton Fixed.end_cap endPaths ∧ isSkeleton Fixed.corner cornerPaths ∧
    isSkeleton Fixed.tee teePaths ∧ isSkeleton Fixed.line linePaths ∧
    isSkeleton Fixed.switch [switchPath] := by decide

theorem mem_symmetric (s : Finset (Center × Center)) (p q : Center) :
    (p,q) ∈ symmetric s ↔ (p,q) ∈ s ∨ (q,p) ∈ s := by
  rw [symmetric, Finset.mem_union]
  apply or_congr_right
  constructor
  · intro h
    obtain ⟨x, hx, eq⟩ := Finset.mem_image.mp h
    have swap : x = (q,p) := by simpa using congrArg Prod.swap eq
    exact swap ▸ hx
  · intro h
    exact Finset.mem_image.mpr ⟨(q,p), h, rfl⟩

theorem skeleton_point_iff {s : Stencil} {paths : List (List Center)} (h : isSkeleton s paths)
    (p : Center) : p ∈ s.optional ↔ ∃ path ∈ paths, p ∈ path := by
  simp [h.1, skeletonPoints]

theorem skeleton_link_iff {s : Stencil} {paths : List (List Center)} (h : isSkeleton s paths)
    (p q : Center) : ((p,q) ∈ s.graph ∨ (q,p) ∈ s.graph) ↔
    ∃ path ∈ paths, (p,q) ∈ path.zip path.tail ∨ (q,p) ∈ path.zip path.tail := by
  rw [← mem_symmetric, h.2, mem_symmetric]
  simp only [skeletonLinks, List.mem_toFinset, List.mem_flatMap]
  constructor
  · rintro (⟨path, hp, he⟩ | ⟨path, hp, he⟩)
    · exact ⟨path, hp, Or.inl he⟩
    · exact ⟨path, hp, Or.inr he⟩
  · rintro ⟨path, hp, he | he⟩
    · exact Or.inl ⟨path, hp, he⟩
    · exact Or.inr ⟨path, hp, he⟩

end GridCover.CorePaths
