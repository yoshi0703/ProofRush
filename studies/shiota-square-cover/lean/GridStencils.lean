import GridGeometry
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval

namespace GridCover

inductive Role
  | empty
  | optional
  | guard
  deriving DecidableEq, Repr

abbrev Roles := Center → Role
abbrev Links := Center → Center → Bool

def box (r : ℤ) (p : Center) : Finset Center :=
  Finset.Icc (p.1 - r) (p.1 + r) ×ˢ Finset.Icc (p.2 - r) (p.2 + r)

@[simp] theorem mem_box {r : ℤ} {p q : Center} : q ∈ box r p ↔ nearby r p q := by
  simp [box, nearby, Finset.mem_product, Finset.mem_Icc, and_assoc]

def seededCoverers (roles : Roles) (edge : GridEdge) : Finset Center :=
  (incidentCenters edge).filter fun q => roles q ≠ .empty

def present (roles : Roles) (edge : GridEdge) : Prop := (seededCoverers roles edge).Nonempty

instance (roles : Roles) (edge : GridEdge) : Decidable (present roles edge) :=
  inferInstanceAs (Decidable ((seededCoverers roles edge).Nonempty))

def geometricEligible (roles : Roles) (p : Center) : Prop :=
  ∀ edge ∈ perimeter p, present roles edge

instance (roles : Roles) (p : Center) : Decidable (geometricEligible roles p) := by
  unfold geometricEligible
  infer_instance

def geometricCoverers (roles : Roles) (edge : GridEdge) : Finset Center :=
  (incidentCenters edge).filter (geometricEligible roles)

def edgeRequirements (coverers : GridEdge → Finset Center) (roles : Roles) (links : Links)
    (p : Center) : Prop :=
  (roles p = .guard → ∃ edge ∈ perimeter p, coverers edge = {p}) ∧
  (roles p = .optional →
    (∀ edge ∈ perimeter p,
      (∃ q ∈ coverers edge, roles q = .guard) ∨
      (∃ q ∈ coverers edge, ∃ s ∈ coverers edge,
        roles q = .optional ∧ roles s = .optional ∧ links q s = true)) ∧
    (∀ q ∈ box 2 p, links p q = true →
      ∃ edge ∈ perimeter p, coverers edge = {p, q}))

instance (coverers : GridEdge → Finset Center) (roles : Roles) (links : Links) (p : Center) :
    Decidable (edgeRequirements coverers roles links p) := by
  unfold edgeRequirements
  infer_instance

def rawCheck (roles : Roles) (links : Links) (p : Center) : Prop :=
  (geometricEligible roles p ↔ roles p ≠ .empty) ∧
  edgeRequirements (seededCoverers roles) roles links p

instance (roles : Roles) (links : Links) (p : Center) :
    Decidable (rawCheck roles links p) := by
  unfold rawCheck
  infer_instance

def geometricCheck (roles : Roles) (links : Links) (p : Center) : Prop :=
  (geometricEligible roles p ↔ roles p ≠ .empty) ∧
  edgeRequirements (geometricCoverers roles) roles links p

theorem geometricCoverers_eq_of_classified {roles : Roles} {p : Center} {edge : GridEdge}
    (he : edge ∈ perimeter p)
    (classified : ∀ q ∈ box 2 p, geometricEligible roles q ↔ roles q ≠ .empty) :
    geometricCoverers roles edge = seededCoverers roles edge := by
  ext q
  simp only [geometricCoverers, seededCoverers, Finset.mem_filter]
  refine and_congr_right fun hq => classified q ?_
  exact mem_box.mpr (sharedEdge_nearby ((mem_incidentCenters edge p).mpr he) hq)

theorem geometricCheck_of_raw {roles : Roles} {links : Links} {p : Center}
    (raw : rawCheck roles links p)
    (neighbor : ∀ q ∈ box 2 p, geometricEligible roles q ↔ roles q ≠ .empty) :
    geometricCheck roles links p := by
  refine ⟨raw.1, ?_, ?_⟩
  · intro hg
    obtain ⟨edge, he, hprivate⟩ := raw.2.1 hg
    exact ⟨edge, he, (geometricCoverers_eq_of_classified he neighbor).trans hprivate⟩
  · intro ho
    obtain ⟨hcover, hpair⟩ := raw.2.2 ho
    refine ⟨?_, ?_⟩
    · intro edge he
      rw [geometricCoverers_eq_of_classified he neighbor]
      exact hcover edge he
    · intro q hq hl
      obtain ⟨edge, he, hprivate⟩ := hpair q hq hl
      exact ⟨edge, he, (geometricCoverers_eq_of_classified he neighbor).trans hprivate⟩

theorem geometric_core_of_checked_collar {roles : Roles} {links : Links} {r : ℤ}
    (checked : ∀ p ∈ box (r + 2) (0, 0), rawCheck roles links p)
    {p : Center} (hp : p ∈ box r (0, 0)) :
    geometricCheck roles links p := by
  have hp' : p ∈ box (r + 2) (0, 0) := by
    have hh := mem_box.mp hp
    apply mem_box.mpr
    unfold nearby at *
    omega
  apply geometricCheck_of_raw (checked p hp')
  intro q hq
  exact (checked q (mem_box.mpr (nearby_trans (mem_box.mp hp) (mem_box.mp hq)))).1

def along (d p : Center) : ℤ := d.1 * p.1 + d.2 * p.2

def transverse (d p : Center) : ℤ := d.1 * p.2 - d.2 * p.1

structure Stencil where
  guards : Finset Center
  optional : Finset Center
  graph : Finset (Center × Center)
  rays : Finset (Center × ℤ)

def inBand (phase t : ℤ) : Prop := (t - phase) % 4 = 0 ∨ (t - phase) % 4 = 1

instance (phase t : ℤ) : Decidable (inBand phase t) := by
  unfold inBand
  infer_instance

def Stencil.roles (S : Stencil) (p : Center) : Role :=
  if p ∈ box 3 (0, 0) then
    if p ∈ S.optional then .optional else if p ∈ S.guards then .guard else .empty
  else if ∃ ray ∈ S.rays, 3 < along ray.1 p ∧ transverse ray.1 p = 0 then .optional
  else if ∃ ray ∈ S.rays, 3 < along ray.1 p ∧
      (transverse ray.1 p = -1 ∨ transverse ray.1 p = 1) ∧ inBand ray.2 (along ray.1 p)
    then .guard else .empty

def unitApart (x y : ℤ) : Prop := x + 1 = y ∨ y + 1 = x

instance (x y : ℤ) : Decidable (unitApart x y) := by
  unfold unitApart
  infer_instance

instance (r : ℤ) (p q : Center) : Decidable (nearby r p q) := by
  unfold nearby
  infer_instance

def Stencil.links (S : Stencil) (p q : Center) : Bool := decide <|
  nearby 2 p q ∧
    ((p, q) ∈ S.graph ∨ (q, p) ∈ S.graph ∨
    ∃ ray ∈ S.rays, 3 ≤ along ray.1 p ∧ 3 ≤ along ray.1 q ∧
      transverse ray.1 p = 0 ∧ transverse ray.1 q = 0 ∧
      unitApart (along ray.1 p) (along ray.1 q))

def Stencil.dataValid (S : Stencil) : Prop :=
  Disjoint S.guards S.optional ∧
  S.guards ⊆ box 3 (0, 0) ∧ S.optional ⊆ box 3 (0, 0) ∧
  (∀ pair ∈ S.graph, pair.1 ∈ S.optional ∧ pair.2 ∈ S.optional ∧
    pair.1 ≠ pair.2 ∧ nearby 2 pair.1 pair.2) ∧
  (∀ ray ∈ S.rays, ray.1 ∈ ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset Center))

instance (S : Stencil) : Decidable S.dataValid := by
  unfold Stencil.dataValid
  infer_instance

theorem Stencil.declared_edge_private {S : Stencil} (data : S.dataValid)
    (checked : ∀ p ∈ box 3 (0, 0), geometricCheck S.roles S.links p)
    {p q : Center} (edge : (p, q) ∈ S.graph) :
    ∃ e ∈ perimeter p, geometricCoverers S.roles e = {p, q} := by
  obtain ⟨hp, _, _, hn⟩ := data.2.2.2.1 (p,q) edge
  have hCore := data.2.2.1 hp
  have hr : S.roles p = .optional := by simp [Stencil.roles, hCore, hp]
  have hl : S.links p q = true := by
    exact decide_eq_true ⟨hn, Or.inl edge⟩
  exact ((checked p hCore).2.2 hr).2 q (mem_box.mpr hn) hl

end GridCover
