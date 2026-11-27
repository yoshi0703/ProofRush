import GridStencils

namespace GridCover

/-- Coordinate relabelling preserves the actual unit square geometry. -/
structure GridIso where
  point : Center ≃ Center
  edge : GridEdge ≃ GridEdge
  perim : ∀ p e, edge e ∈ perimeter (point p) ↔ e ∈ perimeter p
  close : ∀ p q, nearby 2 (point p) (point q) ↔ nearby 2 p q

def shiftPoint (k : ℤ) (p : Center) : Center := (p.1 + k, p.2)

def shiftEdge (k : ℤ) : GridEdge → GridEdge
  | .horizontal x y => .horizontal (x + k) y
  | .vertical x y => .vertical (x + k) y

def horizontalShift (k : ℤ) : GridIso where
  point := {
    toFun := shiftPoint k
    invFun := shiftPoint (-k)
    left_inv := by intro p; simp [shiftPoint]
    right_inv := by intro p; simp [shiftPoint] }
  edge := {
    toFun := shiftEdge k
    invFun := shiftEdge (-k)
    left_inv := by intro e; cases e <;> simp [shiftEdge]
    right_inv := by intro e; cases e <;> simp [shiftEdge] }
  perim := by
    rintro ⟨x,y⟩ e
    cases e <;> simp [shiftPoint, shiftEdge, perimeter] <;> omega
  close := by
    rintro ⟨px,py⟩ ⟨qx,qy⟩
    simp [shiftPoint, nearby]
    omega

def swapCenter (p : Center) : Center := (p.2, p.1)

def swapEdge : GridEdge → GridEdge
  | .horizontal x y => .vertical y x
  | .vertical x y => .horizontal y x

def transposeGrid : GridIso where
  point := {
    toFun := swapCenter
    invFun := swapCenter
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }
  edge := {
    toFun := swapEdge
    invFun := swapEdge
    left_inv := by intro e; cases e <;> rfl
    right_inv := by intro e; cases e <;> rfl }
  perim := by
    rintro ⟨x,y⟩ e
    change swapEdge e ∈ perimeter (y,x) ↔ e ∈ perimeter (x,y)
    cases e <;> simp [swapEdge, perimeter] <;> omega
  close := by
    rintro ⟨px,py⟩ ⟨qx,qy⟩
    change nearby 2 (py,px) (qy,qx) ↔ nearby 2 (px,py) (qx,qy)
    simp [nearby]
    omega

theorem GridIso.seededCoverers_mem (g : GridIso) {P Q : Roles}
    (roles_eq : ∀ p, P p = Q (g.point p)) (e : GridEdge) (p : Center) :
    p ∈ seededCoverers P e ↔ g.point p ∈ seededCoverers Q (g.edge e) := by
  simp only [seededCoverers, Finset.mem_filter, mem_incidentCenters]
  rw [g.perim, roles_eq p]

theorem GridIso.present_iff (g : GridIso) {P Q : Roles}
    (roles_eq : ∀ p, P p = Q (g.point p)) (e : GridEdge) :
    present P e ↔ present Q (g.edge e) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨g.point p, (g.seededCoverers_mem roles_eq e p).mp hp⟩
  · rintro ⟨q, hq⟩
    obtain ⟨p, rfl⟩ := g.point.surjective q
    exact ⟨p, (g.seededCoverers_mem roles_eq e p).mpr hq⟩

theorem GridIso.eligible_iff (g : GridIso) {P Q : Roles}
    (roles_eq : ∀ p, P p = Q (g.point p)) (p : Center) :
    geometricEligible P p ↔ geometricEligible Q (g.point p) := by
  constructor
  · intro h e he
    obtain ⟨f, rfl⟩ := g.edge.surjective e
    exact (g.present_iff roles_eq f).mp (h f ((g.perim p f).mp he))
  · intro h e he
    exact (g.present_iff roles_eq e).mpr (h (g.edge e) ((g.perim p e).mpr he))

theorem GridIso.raw_pullback (g : GridIso) {P Q : Roles} {L K : Links}
    (roles_eq : ∀ p, P p = Q (g.point p))
    (links_eq : ∀ p q, L p q = K (g.point p) (g.point q)) {p : Center}
    (checked : rawCheck Q K (g.point p)) : rawCheck P L p := by
  have transfer := g.seededCoverers_mem roles_eq
  have pullGuard {e} (h : seededCoverers Q (g.edge e) = {g.point p}) :
      seededCoverers P e = {p} := by
    ext q
    rw [transfer e q, h]
    simp [g.point.injective.eq_iff]
  have pullPair {e q} (h : seededCoverers Q (g.edge e) = {g.point p, g.point q}) :
      seededCoverers P e = {p, q} := by
    ext z
    rw [transfer e z, h]
    simp [g.point.injective.eq_iff]
  refine ⟨(g.eligible_iff roles_eq p).trans (checked.1.trans ?_), ?_, ?_⟩
  · rw [roles_eq p]
  · intro hp
    obtain ⟨e, he, hu⟩ := checked.2.1 ((roles_eq p).symm.trans hp)
    obtain ⟨f, rfl⟩ := g.edge.surjective e
    exact ⟨f, (g.perim p f).mp he, pullGuard hu⟩
  · intro hp
    obtain ⟨hcover, hwit⟩ := checked.2.2 ((roles_eq p).symm.trans hp)
    refine ⟨?_, ?_⟩
    · intro e he
      rcases hcover (g.edge e) ((g.perim p e).mpr he) with ⟨q, hq, hg⟩ | ⟨q, hq, s, hs, hqo, hso, hlink⟩
      · obtain ⟨q, rfl⟩ := g.point.surjective q
        exact Or.inl ⟨q, (transfer e q).mpr hq, (roles_eq q).trans hg⟩
      · obtain ⟨q, rfl⟩ := g.point.surjective q
        obtain ⟨s, rfl⟩ := g.point.surjective s
        exact Or.inr ⟨q, (transfer e q).mpr hq, s, (transfer e s).mpr hs,
          (roles_eq q).trans hqo, (roles_eq s).trans hso, (links_eq q s).trans hlink⟩
    · intro q hq hl
      obtain ⟨e, he, hpair⟩ := hwit (g.point q)
        (mem_box.mpr ((g.close p q).mpr (mem_box.mp hq))) ((links_eq p q).symm.trans hl)
      obtain ⟨e, rfl⟩ := g.edge.surjective e
      exact ⟨e, (g.perim p e).mp he, pullPair hpair⟩

def wireRoles (phase : ℤ) (p : Center) : Role :=
  if p.2 = 0 then .optional
  else if (p.2 = -1 ∨ p.2 = 1) ∧ inBand phase p.1 then .guard else .empty

def wireLinks (p q : Center) : Bool := decide (p.2 = 0 ∧ q.2 = 0 ∧ unitApart p.1 q.1)

def wirePeriodSites : Finset Center :=
  Finset.Icc (0 : ℤ) 3 ×ˢ Finset.Icc (-3 : ℤ) 3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wire_period_raw : ∀ p ∈ wirePeriodSites, rawCheck (wireRoles 0) wireLinks p := by decide

theorem raw_empty {P : Roles} {L : Links} {p : Center}
    (empty : ∀ q, nearby 2 p q → P q = .empty) : rawCheck P L p := by
  have hp : P p = .empty := empty p (by unfold nearby; omega)
  have notElig : ¬ geometricEligible P p := by
    intro actual
    let e := GridEdge.horizontal (p.1 - 1) (p.2 - 1)
    have he : e ∈ perimeter p := by rcases p with ⟨x,y⟩; simp [e, perimeter]
    obtain ⟨q, hq⟩ := actual e he
    obtain ⟨hIncident, hOccupied⟩ := Finset.mem_filter.mp hq
    exact hOccupied (empty q (sharedEdge_nearby ((mem_incidentCenters e p).mpr he) hIncident))
  refine ⟨?_, ?_, ?_⟩
  · simp [hp, notElig]
  · simp [hp]
  · simp [hp]

theorem wire_raw (phase : ℤ) (p : Center) : rawCheck (wireRoles phase) wireLinks p := by
  by_cases hy : -3 ≤ p.2 ∧ p.2 ≤ 3
  · let k := -phase - 4 * ((p.1 - phase) / 4)
    let g := horizontalShift k
    have hx : (g.point p).1 = (p.1 - phase) % 4 := by
      change p.1 + k = (p.1 - phase) % 4
      dsimp [k]
      omega
    have hs : g.point p ∈ wirePeriodSites := by
      simp only [wirePeriodSites, Finset.mem_product, Finset.mem_Icc, hx]
      constructor
      · omega
      · exact hy
    apply g.raw_pullback _ _ (wire_period_raw _ hs)
    · rintro ⟨x,y⟩
      change wireRoles phase (x,y) = wireRoles 0 (x + k,y)
      have hMod : (x + k) % 4 = (x - phase) % 4 := by
        dsimp [k]
        omega
      have hBand : inBand phase x ↔ inBand 0 (x + k) := by
        unfold inBand
        rw [Int.sub_zero, hMod]
      by_cases h0 : y = 0
      · simp [wireRoles, h0]
      · by_cases h : (y = -1 ∨ y = 1) ∧ inBand phase x
        · have hr := hBand.mp h.2
          simp [wireRoles, h0, h, hr]
        · have hr : ¬ ((y = -1 ∨ y = 1) ∧ inBand 0 (x + k)) := fun v =>
            h ⟨v.1, hBand.mpr v.2⟩
          simp [wireRoles, h0, h, hr]
    · rintro ⟨x,y⟩ ⟨u,v⟩
      change wireLinks (x,y) (u,v) = wireLinks (x + k,y) (u + k,v)
      have hApart : unitApart (x + k) (u + k) ↔ unitApart x u := by
        unfold unitApart
        omega
      simp [wireLinks, hApart]
  · apply raw_empty
    intro q hq
    unfold wireRoles nearby at *
    have hn : q.2 ≠ 0 ∧ q.2 ≠ -1 ∧ q.2 ≠ 1 := by omega
    simp [hn]

theorem wire_geometry (phase : ℤ) (p : Center) :
    geometricCheck (wireRoles phase) wireLinks p :=
  geometricCheck_of_raw (wire_raw phase p) fun q _ => (wire_raw phase q).1

def verticalWireRoles (phase : ℤ) (p : Center) : Role := wireRoles phase (swapCenter p)

def verticalWireLinks (p q : Center) : Bool := wireLinks (swapCenter p) (swapCenter q)

theorem vertical_wire_raw (phase : ℤ) (p : Center) :
    rawCheck (verticalWireRoles phase) verticalWireLinks p :=
  transposeGrid.raw_pullback (fun _ => rfl) (fun _ _ => rfl)
    (wire_raw phase (swapCenter p))

theorem vertical_wire_geometry (phase : ℤ) (p : Center) :
    geometricCheck (verticalWireRoles phase) verticalWireLinks p :=
  geometricCheck_of_raw (vertical_wire_raw phase p) fun q _ => (vertical_wire_raw phase q).1

end GridCover
