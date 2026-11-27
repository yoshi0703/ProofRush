import GridFixedStencils
import GridSeams
import SubdivisionCost

namespace GridCover

def assemblyRoles (guards optional : Finset Center) (p : Center) : Role :=
  if p ∈ guards then .guard else if p ∈ optional then .optional else .empty

def assemblyLinks (graph : Finset (Center × Center)) (p q : Center) : Bool :=
  decide ((p,q) ∈ graph ∨ (q,p) ∈ graph)

def AssemblyGraphOK (optional : Finset Center) (graph : Finset (Center × Center)) : Prop :=
  ∀ pair ∈ graph, pair.1 ∈ optional ∧ pair.2 ∈ optional ∧
    pair.1 ≠ pair.2 ∧ nearby 2 pair.1 pair.2

@[simp] theorem assemblyRoles_seed {guards optional : Finset Center} {p : Center} :
    assemblyRoles guards optional p ≠ .empty ↔ p ∈ guards ∪ optional := by
  by_cases hg : p ∈ guards <;> by_cases ho : p ∈ optional <;>
    simp [assemblyRoles, hg, ho]

@[simp] theorem assemblyRoles_guard {guards optional : Finset Center} {p : Center} :
    assemblyRoles guards optional p = .guard ↔ p ∈ guards := by
  by_cases hg : p ∈ guards <;> by_cases ho : p ∈ optional <;>
    simp [assemblyRoles, hg, ho]

theorem assemblyRoles_optional {guards optional : Finset Center} {p : Center}
    (disjoint : Disjoint guards optional) :
    assemblyRoles guards optional p = .optional ↔ p ∈ optional := by
  by_cases ho : p ∈ optional
  · have hg : p ∉ guards := fun hg => Finset.disjoint_left.mp disjoint hg ho
    simp [assemblyRoles, hg, ho]
  · by_cases hg : p ∈ guards <;> simp [assemblyRoles, hg, ho]

theorem assembly_present {guards optional : Finset Center} {e : GridEdge} :
    present (assemblyRoles guards optional) e ↔ e ∈ seedEdges (guards ∪ optional) := by
  simp [present, seededCoverers, Finset.Nonempty, mem_seedEdges]

theorem assembly_eligible {guards optional : Finset Center} {p : Center} :
    geometricEligible (assemblyRoles guards optional) p ↔
      p ∈ admissible (seedEdges (guards ∪ optional)) := by
  rw [mem_admissible]
  exact forall₂_congr fun _ _ => assembly_present

theorem assembly_covered {guards optional : Finset Center} {graph : Finset (Center × Center)}
    {e : GridEdge} (he : e ∈ seedEdges (guards ∪ optional)) {p : Center} :
    (gridLayout guards optional (seedEdges (guards ∪ optional)) graph).covered p e ↔
      p ∈ seededCoverers (assemblyRoles guards optional) e := by
  simp [gridCovered_iff, seededCoverers, mem_incidentCenters, he, and_comm]

/-- A radius-two patch can be aligned with a certified patch by any square-grid
isometry; no role or link agreement beyond the patch is used. -/
theorem raw_of_isometric_patch {P Q : Roles} {L K : Links} {p : Center} (g : GridIso)
    (roles : ∀ q ∈ box 2 p, P q = Q (g.point q))
    (links : ∀ q ∈ box 2 p, ∀ r ∈ box 2 p, L q r = K (g.point q) (g.point r))
    (certified : rawCheck Q K (g.point p)) : rawCheck P L p :=
  rawCheck_of_local_agreement roles links (g.raw_pullback (fun _ => rfl) (fun _ _ => rfl) certified)

/-- A seed-free patch verifies automatically.  Every other anchor can use
an isometric stencil, periodic wire, or another independently checked patch. -/
def HasCertifiedPatches (P : Roles) (L : Links) : Prop :=
  ∀ p : Center, (∃ q ∈ box 2 p, P q ≠ .empty) →
    ∃ (Q : Roles) (K : Links) (g : GridIso),
      (∀ q ∈ box 2 p, P q = Q (g.point q)) ∧
      (∀ q ∈ box 2 p, ∀ r ∈ box 2 p, L q r = K (g.point q) (g.point r)) ∧
      rawCheck Q K (g.point p)

theorem assembled_raw {P : Roles} {L : Links} (patches : HasCertifiedPatches P L) :
    ∀ p, rawCheck P L p := by
  intro p
  by_cases hn : ∃ q ∈ box 2 p, P q ≠ .empty
  · obtain ⟨Q, K, g, hr, hl, hp⟩ := patches p hn
    exact raw_of_isometric_patch g hr hl hp
  · apply raw_empty
    intro q hq
    exact not_not.mp (fun h => hn ⟨q, mem_box.mpr hq, h⟩)

/-- The local tests imply the exact physical guard/option graph certificate. -/
theorem gridValid_of_raw {guards optional : Finset Center}
    {graph : Finset (Center × Center)}
    (disjoint : Disjoint guards optional)
    (graphOK : AssemblyGraphOK optional graph)
    (checked : ∀ p, rawCheck (assemblyRoles guards optional) (assemblyLinks graph) p) :
    gridValid guards optional (seedEdges (guards ∪ optional)) graph := by
  refine ⟨?_, disjoint, ?_, ?_, ?_, ?_⟩
  · ext p
    exact assembly_eligible.symm.trans ((checked p).1.trans assemblyRoles_seed)
  · intro pair hp
    exact ⟨(graphOK pair hp).1, (graphOK pair hp).2.1, (graphOK pair hp).2.2.1⟩
  · intro p hp
    obtain ⟨e, he, privateEdge⟩ :=
      (checked p).2.1 (assemblyRoles_guard.mpr hp)
    have hreq : e ∈ seedEdges (guards ∪ optional) :=
      (mem_seedEdges _ _).mpr ⟨p, (mem_incidentCenters _ _).mpr he, Finset.mem_union_left _ hp⟩
    refine ⟨e, hreq, fun q _ => ?_⟩
    rw [assembly_covered hreq, privateEdge, Finset.mem_singleton]
  · intro e he
    obtain ⟨p, hpi, hp⟩ := (mem_seedEdges _ _).mp he
    by_cases hg : p ∈ guards
    · exact Or.inl ⟨p, hg, gridCovered_iff.mpr ⟨hp, he, (mem_incidentCenters _ _).mp hpi⟩⟩
    · have ho := (Finset.mem_union.mp hp).resolve_left hg
      rcases ((checked p).2.2 ((assemblyRoles_optional disjoint).mpr ho)).1 e
        ((mem_incidentCenters _ _).mp hpi) with ⟨q, hq, hqg⟩ | ⟨q, hq, r, hr, _, _, hl⟩
      · exact Or.inl ⟨q, assemblyRoles_guard.mp hqg, (assembly_covered he).mpr hq⟩
      · have pair : (q,r) ∈ graph ∨ (r,q) ∈ graph := of_decide_eq_true hl
        rcases pair with h | h
        · exact Or.inr ⟨(q,r), h, (assembly_covered he).mpr hq, (assembly_covered he).mpr hr⟩
        · exact Or.inr ⟨(r,q), h, (assembly_covered he).mpr hr, (assembly_covered he).mpr hq⟩
  · rintro ⟨p,q⟩ hpq
    obtain ⟨hp, _, _, hn⟩ := graphOK (p,q) hpq
    have hl : assemblyLinks graph p q = true := decide_eq_true (Or.inl hpq)
    obtain ⟨e, he, privatePair⟩ := ((checked p).2.2 ((assemblyRoles_optional disjoint).mpr hp)).2
      q (mem_box.mpr hn) hl
    have hreq : e ∈ seedEdges (guards ∪ optional) :=
      (mem_seedEdges _ _).mpr ⟨p, (mem_incidentCenters _ _).mpr he, Finset.mem_union_right _ hp⟩
    refine ⟨e, hreq, fun z _ => ?_⟩
    rw [assembly_covered hreq, privatePair, Finset.mem_insert, Finset.mem_singleton]

theorem gridValid_of_patches {guards optional : Finset Center} {graph : Finset (Center × Center)}
    (disjoint : Disjoint guards optional)
    (graphOK : AssemblyGraphOK optional graph)
    (patches : HasCertifiedPatches (assemblyRoles guards optional) (assemblyLinks graph)) :
    gridValid guards optional (seedEdges (guards ∪ optional)) graph :=
  gridValid_of_raw disjoint graphOK (assembled_raw patches)

theorem assembled_exact_budget {guards optional : Finset Center}
    {graph : Finset (Center × Center)} (disjoint : Disjoint guards optional)
    (graphOK : AssemblyGraphOK optional graph)
    (patches : HasCertifiedPatches (assemblyRoles guards optional) (assemblyLinks graph)) (k : ℕ) :
    (∃ selected : Finset Center, physicalCover (seedEdges (guards ∪ optional)) selected ∧
      selected.card = min (guards ∪ optional).card (guards.card + k)) ↔
    (∃ selected : Finset Center,
      (gridLayout guards optional (seedEdges (guards ∪ optional)) graph).vertexCover selected ∧
      selected.card ≤ k) := by
  have valid := gridValid_of_patches disjoint graphOK patches
  simpa only [valid.1] using physicalExactBudget_iff valid k

end GridCover
