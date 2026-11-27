import GridPlacementModels

namespace GridCover.Placement

namespace Run

theorem tube_near_start {s : Run} {p : Center} (h : s.Tube p) : nearby s.length s.start p := by
  rw [s.near_start_iff]
  unfold Tube Across at h
  omega

theorem eq_port {s : Run} {p : Center} (x : s.alongAt p = 3) (y : s.acrossAt p = 0) :
    p = s.dir.atSite s.start 3 := by
  obtain ⟨⟨a,b⟩,d,L⟩ := s
  obtain ⟨c,e⟩ := p
  cases d <;>
    simp [Direction.atSite, alongAt, acrossAt, sub, Direction.longitudinal,
      Direction.lateral] at x y ⊢ <;> omega

theorem link_symm {s : Run} {p q : Center} (h : s.Link p q) : s.Link q p :=
  ⟨h.2.1, h.1, Or.symm h.2.2⟩

end Run

namespace Layout

def domain (A : Layout) : Finset Center :=
  (A.hubs.biUnion fun h => box 3 h) ∪ (A.runs.biUnion fun s => box s.length s.start)

theorem in_domain_of_core (A : Layout) {h p : Center} (hh : h ∈ A.hubs) (hp : nearby 3 h p) :
    p ∈ A.domain :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨h,hh,mem_box.mpr hp⟩)

theorem in_domain_of_run (A : Layout) {s : Run} {p : Center} (hs : s ∈ A.runs) (hp : s.Tube p) :
    p ∈ A.domain :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s,hs,mem_box.mpr (Run.tube_near_start hp)⟩)

theorem in_domain_of_seed (A : Layout) {p : Center} (hp : A.roles p ≠ .empty) : p ∈ A.domain := by
  have ex : A.IsOptional p ∨ A.IsGuard p := by
    by_contra none
    exact hp (by simp [roles, not_or.mp none])
  rcases ex with (⟨h,hh,hc⟩ | ⟨s,hs,hc⟩) | (⟨h,hh,hc⟩ | ⟨s,hs,hc⟩)
  · exact A.in_domain_of_core hh hc.1
  · exact A.in_domain_of_run hs (Run.optional_tube hc)
  · exact A.in_domain_of_core hh hc.1
  · exact A.in_domain_of_run hs (Run.guard_tube hc)

theorem strip_port_optional (A : Layout) {s : Run} (hs : Oriented A.runs s) :
    A.IsOptional (s.dir.atSite s.start 3) := by
  have hh : s.start ∈ A.hubs := by
    rcases hs with h | h
    · exact A.startHub s h
    · have h' := A.finishHub s.reverse h
      simpa using h'
  have hd := (A.port s.start hh s.dir).mpr ⟨s, hs, rfl, rfl⟩
  exact Or.inl ⟨s.start, hh, (A.model s.start).portOptional s.dir hd⟩

theorem strip_link_endpoint (A : Layout) {s : Run} (hs : s ∈ A.runs) {p : Center}
    (hx : 3 ≤ s.alongAt p) (hy : s.alongAt p ≤ s.length - 3) (hz : s.acrossAt p = 0) :
    A.IsOptional p := by
  by_cases hStart : s.alongAt p = 3
  · rw [Run.eq_port hStart hz]
    exact A.strip_port_optional (Or.inl hs)
  by_cases hFinish : s.alongAt p = s.length - 3
  · have hfin : s.reverse.alongAt p = 3 := by rw [Run.reverse_along]; omega
    have hlat : s.reverse.acrossAt p = 0 := by rwa [Run.reverse_across]
    rw [Run.eq_port hfin hlat]
    exact A.strip_port_optional (s := s.reverse) (Or.inr (by simpa using hs))
  exact Or.inr ⟨s, hs, by exact ⟨by omega, by omega, hz⟩⟩

theorem link_data (A : Layout) {p q : Center} (hp : A.IsLink p q) :
    A.IsOptional p ∧ A.IsOptional q ∧ p ≠ q ∧ nearby 2 p q := by
  rcases hp with ⟨h,hh,⟨ph,qh,hpq⟩⟩ | ⟨s,hs,hsLink⟩
  · let M := A.model h
    rcases hpq with fwd | rev
    · obtain ⟨a,b,ne,close⟩ := M.valid.2.2.2.1 _ fwd
      exact ⟨Or.inl ⟨h,hh,ph,a⟩, Or.inl ⟨h,hh,qh,b⟩,
        fun eq => ne (congrArg M.localize.point eq), (M.localize.close p q).mp close⟩
    · obtain ⟨a,b,ne,close⟩ := M.valid.2.2.2.1 _ rev
      exact ⟨Or.inl ⟨h,hh,ph,b⟩, Or.inl ⟨h,hh,qh,a⟩,
        fun eq => ne (congrArg M.localize.point eq.symm), (M.localize.close p q).mp (nearby_symm.mp close)⟩
  · exact ⟨A.strip_link_endpoint hs hsLink.1.1 hsLink.1.2.1 hsLink.1.2.2,
      A.strip_link_endpoint hs hsLink.2.1.1 hsLink.2.1.2.1 hsLink.2.1.2.2,
      Run.link_ne hsLink, Run.link_nearby hsLink⟩

theorem link_comm (A : Layout) {p q : Center} (hp : A.IsLink p q) : A.IsLink q p := by
  rcases hp with ⟨h,hh,a,b,c⟩ | ⟨s,hs,link⟩
  · exact Or.inl ⟨h,hh,b,a,c.symm⟩
  · exact Or.inr ⟨s,hs,Run.link_symm link⟩

def guardSet (A : Layout) : Finset Center := A.domain.filter fun p => A.roles p = .guard

def optionalSet (A : Layout) : Finset Center := A.domain.filter fun p => A.roles p = .optional

def linkSet (A : Layout) : Finset (Center × Center) :=
  (A.domain ×ˢ A.domain).filter fun pair => A.IsLink pair.1 pair.2

@[simp] theorem mem_guardSet (A : Layout) (p : Center) : p ∈ A.guardSet ↔ A.roles p = .guard := by
  simp only [guardSet, Finset.mem_filter]
  exact ⟨And.right, fun hp => ⟨A.in_domain_of_seed (by simp [hp]),hp⟩⟩

@[simp] theorem mem_optionalSet (A : Layout) (p : Center) : p ∈ A.optionalSet ↔ A.roles p = .optional := by
  simp only [optionalSet, Finset.mem_filter]
  exact ⟨And.right, fun hp => ⟨A.in_domain_of_seed (by simp [hp]),hp⟩⟩

theorem optional_role (A : Layout) {p : Center} (hp : A.IsOptional p) : A.roles p = .optional := by
  simp [roles, hp]

theorem roles_disjoint (A : Layout) {p : Center} (ho : A.IsOptional p) (hg : A.IsGuard p) : False := by
  classical
  by_cases existsHub : ∃ h ∈ A.hubs, nearby 5 h p
  · obtain ⟨h,hh,hnear⟩ := existsHub
    have nearby7 := nearby_mono (by decide : (5 : ℤ) ≤ 7) hnear
    have a := (A.collar_optional hh nearby7).mp ho
    have b := (A.collar_guard hh nearby7).mp hg
    cases a.symm.trans b
  · have away : A.AwayFromHubs p := fun h hh near => existsHub ⟨h,hh,near⟩
    have hpp := nearby_refl (by decide : (0 : ℤ) ≤ 2) p
    obtain ⟨s,hs,sq⟩ := A.exists_strip_of_seed away hpp (by simp [A.optional_role ho])
    have a := (A.patch_optional away hs sq hpp hpp).mp ho
    have b := (A.patch_guard away hs sq hpp hpp).mp hg
    unfold Run.Optional at a
    unfold Run.Guard at b
    omega

theorem mem_optional_iff (A : Layout) (p : Center) : p ∈ A.optionalSet ↔ A.IsOptional p := by
  rw [A.mem_optionalSet]
  by_cases hp : A.IsOptional p
  · simp [roles, hp]
  · simp only [roles, hp, ite_false]
    split_ifs <;> decide

theorem mem_guard_iff (A : Layout) (p : Center) : p ∈ A.guardSet ↔ A.IsGuard p := by
  rw [A.mem_guardSet]
  by_cases hp : A.IsGuard p
  · have hn : ¬ A.IsOptional p := fun h => A.roles_disjoint h hp
    simp [roles, hn, hp]
  · simp only [roles, hp, ite_false]
    split_ifs <;> decide

@[simp] theorem mem_linkSet (A : Layout) (p q : Center) : (p,q) ∈ A.linkSet ↔ A.IsLink p q := by
  simp only [linkSet, Finset.mem_filter, Finset.mem_product]
  refine ⟨And.right, fun hp => ?_⟩
  obtain ⟨a,b,_,_⟩ := A.link_data hp
  exact ⟨⟨A.in_domain_of_seed (by simp [A.optional_role a]),
     A.in_domain_of_seed (by simp [A.optional_role b])⟩, hp⟩

theorem guard_optional_disjoint (A : Layout) : Disjoint A.guardSet A.optionalSet := by
  rw [Finset.disjoint_left]
  intro p hG hO
  have eq := ((A.mem_guardSet p).mp hG).symm.trans ((A.mem_optionalSet p).mp hO)
  cases eq

theorem finite_graph_ok (A : Layout) : AssemblyGraphOK A.optionalSet A.linkSet := by
  rintro ⟨p,q⟩ h
  obtain ⟨a,b,ne,c⟩ := A.link_data ((A.mem_linkSet p q).mp h)
  exact ⟨(A.mem_optionalSet p).mpr (A.optional_role a),
    (A.mem_optionalSet q).mpr (A.optional_role b),ne,c⟩

theorem finite_roles (A : Layout) : assemblyRoles A.guardSet A.optionalSet = A.roles := by
  funext p
  cases h : A.roles p <;> simp [assemblyRoles, h]

theorem finite_links (A : Layout) : assemblyLinks A.linkSet = A.links := by
  funext p q
  apply Bool.eq_iff_iff.mpr
  simp only [assemblyLinks, links, decide_eq_true_eq, A.mem_linkSet]
  exact ⟨fun h => h.elim id A.link_comm, Or.inl⟩

theorem finite_patches (A : Layout) :
    HasCertifiedPatches (assemblyRoles A.guardSet A.optionalSet) (assemblyLinks A.linkSet) := by
  rw [A.finite_roles, A.finite_links]
  exact A.hasCertifiedPatches

theorem exact_budget (A : Layout) (k : ℕ) :
    (∃ selected : Finset Center, physicalCover (seedEdges (A.guardSet ∪ A.optionalSet)) selected ∧
      selected.card = min (A.guardSet ∪ A.optionalSet).card (A.guardSet.card + k)) ↔
    (∃ selected : Finset Center,
      (gridLayout A.guardSet A.optionalSet (seedEdges (A.guardSet ∪ A.optionalSet)) A.linkSet).vertexCover selected ∧
      selected.card ≤ k) :=
  assembled_exact_budget A.guard_optional_disjoint A.finite_graph_ok A.finite_patches k

end Layout

end GridCover.Placement
