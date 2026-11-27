import GridStridePath
import AxisGridSource

namespace GridCover.PathEmbedding.Stride17

open GridCover.Placement

def pitch (p : Center) : Center := (17*p.1, 17*p.2)

theorem pitch_injective : Function.Injective pitch := by
  intro p q e
  have h₁ := congrArg Prod.fst e
  have h₂ := congrArg Prod.snd e
  simp [pitch] at h₁ h₂
  exact Prod.ext (by omega) (by omega)

def toDir : AxisGridSource.Axis → Direction
  | .east => .east
  | .north => .north

def NearAxis (a b p : Center) : Prop := AxisGridSource.span (pitch a) (pitch b) p

def lo (p : Center) : Center := (p.1 / 17, p.2 / 17)
def hi (p : Center) : Center := ((p.1 + 16) / 17, (p.2 + 16) / 17)
def closest (p : Center) : Center := ((p.1 + 8) / 17, (p.2 + 8) / 17)

theorem nearAxis_round {a b p : Center} (h : NearAxis a b p) :
    AxisGridSource.span a b (lo p) ∧ AxisGridSource.span a b (hi p) ∧
      AxisGridSource.span a b (closest p) := by
  simp only [NearAxis, AxisGridSource.span, pitch, lo, hi, closest] at *
  omega

theorem exact_pitch {p : Center} (h : lo p = hi p) : pitch (lo p) = p := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [lo, hi] at h₁ h₂
  apply Prod.ext <;> simp only [pitch, lo] <;> omega

@[simp] theorem closest_pitch (p : Center) : closest (pitch p) = p := by
  apply Prod.ext <;> simp only [closest, pitch] <;> omega

theorem world_east (a p : Center) : world .east a p = (a.1 + p.1, a.2 + p.2) := by
  apply ((Direction.east.localFrame a).point).injective
  simp [world, Direction.longitudinal, Direction.lateral, sub]

theorem world_north (a p : Center) : world .north a p = (a.1 + p.2, a.2 + p.1) := by
  apply ((Direction.north.localFrame a).point).injective
  simp [world, Direction.longitudinal, Direction.lateral, sub]

variable {V : Type} (D : AxisGridSource.Drawing V)

def hubPoint (v : V) : Center := pitch (D.hub v)

def sourceDir (e : V × V) : Direction := toDir (D.axis e)

theorem end_hub {e : V × V} (he : e ∈ D.edges) :
    (sourceDir D e).atSite (hubPoint D e.1) (34*(D.length e) : ℤ) = hubPoint D e.2 := by
  have h := congrArg pitch (D.site_last he)
  simp only [AxisGridSource.Drawing.site, AxisGridSource.site, AxisGridSource.Drawing.hub,
    sourceDir, hubPoint, AxisGridSource.Drawing.axis] at *
  cases hd : AxisGridSource.axis (D.coordinate e.1) (D.coordinate e.2) <;>
    simp [hd, toDir, Direction.atSite, AxisGridSource.advance, pitch] at h ⊢ <;>
    omega

theorem site_on_pitch_span {e : V × V} (he : e ∈ D.edges) {i : ℕ}
    (hi : i ≤ 34 * D.length e) :
    NearAxis (D.hub e.1) (D.hub e.2) ((sourceDir D e).atSite (hubPoint D e.1) i) := by
  have h := end_hub D he
  rw [NearAxis, ← hubPoint, ← hubPoint, ← h]
  unfold sourceDir
  cases D.axis e <;> simp [toDir, Direction.atSite, AxisGridSource.span] <;> omega

theorem closest_jog {e : V × V} {j : ℤ} (hj : j = 1 ∨ j = -1) :
    closest (world (sourceDir D e) (hubPoint D e.1) (17,j)) = D.site e 1 := by
  unfold sourceDir hubPoint AxisGridSource.Drawing.site AxisGridSource.site AxisGridSource.Drawing.hub
  unfold AxisGridSource.Drawing.axis
  cases AxisGridSource.axis (D.coordinate e.1) (D.coordinate e.2) <;>
    rcases hj with rfl | rfl <;>
    apply Prod.ext <;> simp [toDir, world_east, world_north, closest, pitch, AxisGridSource.advance] <;>
    omega

theorem site_not_end {e : V × V} (he : e ∈ D.edges)
    {i : ℕ} (hi : 0 < i) (hil : i < 34 * D.length e)
    {v : V} (hv : AxisGridSource.Ends v e) :
    (sourceDir D e).atSite (hubPoint D e.1) i ≠ hubPoint D v := by
  have hinj : Function.Injective (fun j : ℤ => (sourceDir D e).atSite (hubPoint D e.1) j) := by
    intro j k hk
    have h := congrArg (fun p => (sourceDir D e).longitudinal (sub p (hubPoint D e.1))) hk
    simpa only [Direction.longitudinal_atSite] using h
  rcases hv with hv | hv
  · rw [hv]
    intro h
    have hzero : (i : ℤ) = 0 := hinj (h.trans (start_point _ _).symm)
    omega
  · rw [hv, ← end_hub D he]
    intro h
    have h' : (i : ℤ) = 34 * (D.length e : ℤ) := hinj h
    omega

def sourceInside (leftTee rightTee reverse : (V × V) → Bool) (e : V × V) : List Center :=
  placedInternal (sourceDir D e) (hubPoint D e.1) (D.length e) (leftTee e) (rightTee e) (reverse e)

theorem sourceInside_shape (leftTee rightTee reverse : (V × V) → Bool)
    {e : V × V} (he : e ∈ D.edges) {p : Center}
    (hp : p ∈ sourceInside D leftTee rightTee reverse e) :
    (∃ i : ℕ, 0 < i ∧ i < 34 * D.length e ∧
        p = (sourceDir D e).atSite (hubPoint D e.1) i) ∨
      (∃ j : ℤ, (j = 1 ∨ j = -1) ∧ p = world (sourceDir D e) (hubPoint D e.1) (17,j)) := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  rcases (internal_mem_iff (D.length_pos he) _ _ _ _).mp hq with
    ⟨i,hi,hil,_,rfl⟩ | ⟨_,rfl | rfl⟩
  · exact Or.inl ⟨i, by omega, by omega, world_axis _ _ _⟩
  · exact Or.inr ⟨1, Or.inl rfl, rfl⟩
  · exact Or.inr ⟨-1, Or.inr rfl, rfl⟩

theorem sourceInside_round_span (leftTee rightTee reverse : (V × V) → Bool)
    {e : V × V} (he : e ∈ D.edges) {p : Center}
    (hp : p ∈ sourceInside D leftTee rightTee reverse e) :
    D.fineSpan e (closest p) := by
  rcases sourceInside_shape D _ _ _ he hp with ⟨i,_,hil,rfl⟩ | ⟨j,hj,rfl⟩
  · exact (nearAxis_round (site_on_pitch_span D he (by omega : i ≤ _))).2.2
  · rw [closest_jog D hj]
    exact D.site_span he (by have h := D.length_pos he; omega)

theorem sourceInside_avoids_hub (leftTee rightTee reverse : (V × V) → Bool)
    {e : V × V} (he : e ∈ D.edges) {v : V} (hv : v ∈ D.vertices) :
    hubPoint D v ∉ sourceInside D leftTee rightTee reverse e := by
  intro hp
  have hs := sourceInside_round_span D _ _ _ he hp
  rw [hubPoint, closest_pitch] at hs
  have hve := D.touching_vertex he hv hs
  rcases sourceInside_shape D _ _ _ he hp with ⟨i,hi,hil,h⟩ | ⟨j,hj,h⟩
  · exact site_not_end D he hi hil hve h.symm
  · have eq := congrArg closest h
    rw [hubPoint, closest_pitch, closest_jog D hj] at eq
    exact D.site_ne_ends he (by decide : 0 < 1)
      (by have h := D.length_pos he; omega) hve eq.symm

theorem sourceInside_routes_disjoint (leftTee rightTee reverse : (V × V) → Bool)
    {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges) (hef : e ≠ f) {p : Center}
    (hp : p ∈ sourceInside D leftTee rightTee reverse e)
    (hq : p ∈ sourceInside D leftTee rightTee reverse f) : False := by
  have r1 := sourceInside_round_span D _ _ _ he hp
  have r2 := sourceInside_round_span D _ _ _ hf hq
  obtain ⟨v,hve,hvf,hv⟩ := D.touching_edges he hf hef r1 r2
  rcases sourceInside_shape D _ _ _ he hp with ⟨i,hi',hil,heq⟩ | ⟨j,hj,hjog⟩
  · rcases sourceInside_shape D _ _ _ hf hq with ⟨k,_,hkl,keq⟩ | ⟨j,hj,hjog⟩
    · have ps : NearAxis (D.hub e.1) (D.hub e.2) p :=
        heq ▸ site_on_pitch_span D he (by omega : i ≤ _)
      have qs : NearAxis (D.hub f.1) (D.hub f.2) p :=
        keq ▸ site_on_pitch_span D hf (by omega : k ≤ _)
      have hr1 := nearAxis_round ps
      have hr2 := nearAxis_round qs
      obtain ⟨w,hwe,_,hw⟩ := D.touching_edges he hf hef hr1.1 hr2.1
      obtain ⟨w',_,_,hw'⟩ := D.touching_edges he hf hef hr1.2.1 hr2.2.1
      have eq := D.shared_unique he hf hef
        (AxisGridSource.span_rounding hr1.1).1 (AxisGridSource.span_rounding hr2.1).1
        (AxisGridSource.span_rounding hr1.2.1).1 (AxisGridSource.span_rounding hr2.2.1).1
      have uh : lo p = hi p := by
        rw [← hw, ← hw']
        change AxisGridSource.double (D.coordinate w) = AxisGridSource.double (D.coordinate w')
        have ew : AxisGridSource.lower (lo p) = D.coordinate w := by
          rw [← hw]
          apply Prod.ext <;> simp [AxisGridSource.lower, AxisGridSource.Drawing.hub, AxisGridSource.double]
        have ew' : AxisGridSource.lower (hi p) = D.coordinate w' := by
          rw [← hw']
          apply Prod.ext <;> simp [AxisGridSource.lower, AxisGridSource.Drawing.hub, AxisGridSource.double]
        rw [← ew, ← ew', eq]
      exact site_not_end D he hi' hil hwe
        (heq.symm.trans ((exact_pitch uh).symm.trans (congrArg pitch hw).symm))
    · rw [hjog, closest_jog D hj] at hv
      exact D.site_ne_ends hf (by decide : 0 < 1)
        (by have h := D.length_pos hf; omega) hvf hv.symm
  · rw [hjog, closest_jog D hj] at hv
    exact D.site_ne_ends he (by decide : 0 < 1)
      (by have h := D.length_pos he; omega) hve hv.symm

/-- A straight integer drawing constructs the labelled odd subdivision. -/
def embedded [DecidableEq V] (leftTee rightTee reverse : (V × V) → Bool) :
    Embedded V Center where
  vertices := D.vertices.toFinset
  edges := D.edges.toFinset
  hub := ⟨hubPoint D, pitch_injective.comp D.hub_injective⟩
  inside := sourceInside D leftTee rightTee reverse
  t := fun e => 17 * D.length e - 1 - skip (leftTee e && rightTee e)
  endpoints := by
    intro e he
    simpa only [List.mem_toFinset] using D.edge_endpoints e (List.mem_toFinset.mp he)
  length := fun e he => placedInternal_even _ _ _ (D.length_pos (List.mem_toFinset.mp he)) _ _ _
  nodup := fun _ _ => placedInternal_nodup _ _ _ _ _ _
  hub_clear := by
    intro e he
    apply Finset.disjoint_left.mpr
    intro p hh hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hh
    exact sourceInside_avoids_hub D _ _ _ (List.mem_toFinset.mp he) (List.mem_toFinset.mp hv)
      (List.mem_toFinset.mp hi)
  route_clear := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact sourceInside_routes_disjoint D _ _ _ (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf)
      hef (List.mem_toFinset.mp hp) (List.mem_toFinset.mp hq)

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.embedded
