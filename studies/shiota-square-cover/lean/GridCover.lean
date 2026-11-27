import Mathlib.Data.Finset.Card

namespace GridCover

/-- An edge-cover instance carried by selectable tiles. A relation entry
`(tile, edge)` means that this tile covers this required inventory edge. -/
structure Layout (T E : Type*) where
  guards : Finset T
  optional : Finset T
  required : Finset E
  graph : Finset (T × T)
  incidence : Finset (T × E)

variable {T E : Type*} [DecidableEq T]

def Layout.covered (L : Layout T E) (tile : T) (edge : E) : Prop :=
  (tile, edge) ∈ L.incidence

instance [DecidableEq E] (L : Layout T E) (tile : T) (edge : E) : Decidable (L.covered tile edge) :=
  inferInstanceAs (Decidable ((tile, edge) ∈ L.incidence))

def Layout.eligible (L : Layout T E) : Finset T := L.guards ∪ L.optional

def Layout.cover (L : Layout T E) (selected : Finset T) : Prop :=
  selected ⊆ L.eligible ∧
    ∀ edge ∈ L.required, ∃ tile ∈ selected, L.covered tile edge

def Layout.vertexCover (L : Layout T E) (selected : Finset T) : Prop :=
  selected ⊆ L.optional ∧
    ∀ pair ∈ L.graph, pair.1 ∈ selected ∨ pair.2 ∈ selected

/-- Every candidate tile is accounted for by the supplied eligibility list.
The four bounded tests are decidable without enumerating the ambient types. -/
def Layout.valid (L : Layout T E) : Prop :=
  Disjoint L.guards L.optional ∧
  (∀ pair ∈ L.graph, pair.1 ∈ L.optional ∧ pair.2 ∈ L.optional ∧ pair.1 ≠ pair.2) ∧
  (∀ guard ∈ L.guards, ∃ edge ∈ L.required,
    ∀ tile ∈ L.eligible, L.covered tile edge ↔ tile = guard) ∧
  (∀ edge ∈ L.required,
    (∃ guard ∈ L.guards, L.covered guard edge) ∨
    (∃ pair ∈ L.graph, L.covered pair.1 edge ∧ L.covered pair.2 edge)) ∧
  (∀ pair ∈ L.graph, ∃ edge ∈ L.required,
    ∀ tile ∈ L.eligible, L.covered tile edge ↔ tile = pair.1 ∨ tile = pair.2)

instance [DecidableEq E] (L : Layout T E) : Decidable L.valid := by
  unfold Layout.valid
  infer_instance

theorem Layout.guards_forced {L : Layout T E} (valid : L.valid) {selected : Finset T}
    (cover : L.cover selected) : L.guards ⊆ selected := by
  intro guard hg
  obtain ⟨edge, he, private_edge⟩ := valid.2.2.1 guard hg
  obtain ⟨tile, ht, hc⟩ := cover.2 edge he
  have eq := (private_edge tile (cover.1 ht)).mp hc
  simpa [eq] using ht

theorem Layout.vertexCover_of_cover {L : Layout T E} (valid : L.valid)
    {selected : Finset T} (cover : L.cover selected) :
    L.vertexCover (selected \ L.guards) := by
  constructor
  · intro tile ht
    obtain ⟨hs, hng⟩ := Finset.mem_sdiff.mp ht
    have he := cover.1 hs
    exact (Finset.mem_union.mp he).resolve_left hng
  · intro pair hp
    obtain ⟨edge, he, private_pair⟩ := valid.2.2.2.2 pair hp
    obtain ⟨tile, ht, hc⟩ := cover.2 edge he
    have point := (private_pair tile (cover.1 ht)).mp hc
    have ends := valid.2.1 pair hp
    rcases point with eq | eq
    · exact Or.inl (Finset.mem_sdiff.mpr
        ⟨eq ▸ ht, fun hg => Finset.disjoint_left.mp valid.1 hg ends.1⟩)
    · exact Or.inr (Finset.mem_sdiff.mpr
        ⟨eq ▸ ht, fun hg => Finset.disjoint_left.mp valid.1 hg ends.2.1⟩)

theorem Layout.cover_of_vertexCover {L : Layout T E} (valid : L.valid)
    {selected : Finset T} (cover : L.vertexCover selected) :
    L.cover (L.guards ∪ selected) := by
  constructor
  · intro tile ht
    rcases Finset.mem_union.mp ht with hg | hs
    · exact Finset.mem_union_left _ hg
    · exact Finset.mem_union_right _ (cover.1 hs)
  · intro edge he
    rcases valid.2.2.2.1 edge he with ⟨guard, hg, hc⟩ | ⟨pair, hp, h₁, h₂⟩
    · exact ⟨guard, Finset.mem_union_left _ hg, hc⟩
    · rcases cover.2 pair hp with h | h
      · exact ⟨pair.1, Finset.mem_union_right _ h, h₁⟩
      · exact ⟨pair.2, Finset.mem_union_right _ h, h₂⟩

theorem Layout.forced_card {L : Layout T E} (valid : L.valid)
    {selected : Finset T} (cover : L.cover selected) :
    selected.card = L.guards.card + (selected \ L.guards).card := by
  rw [Nat.add_comm]
  exact (Finset.card_sdiff_add_card_eq_card (L.guards_forced valid cover)).symm

theorem Layout.extended_card {L : Layout T E} (valid : L.valid)
    {selected : Finset T} (cover : L.vertexCover selected) :
    (L.guards ∪ selected).card = L.guards.card + selected.card :=
  Finset.card_union_of_disjoint (valid.1.mono_right cover.1)

theorem Layout.budget_iff {L : Layout T E} (valid : L.valid) (k : ℕ) :
    (∃ selected : Finset T, L.cover selected ∧ selected.card ≤ L.guards.card + k) ↔
    (∃ selected : Finset T, L.vertexCover selected ∧ selected.card ≤ k) := by
  constructor
  · rintro ⟨selected, cover, card⟩
    rw [L.forced_card valid cover] at card
    exact ⟨selected \ L.guards, L.vertexCover_of_cover valid cover, Nat.le_of_add_le_add_left card⟩
  · rintro ⟨selected, cover, card⟩
    exact ⟨L.guards ∪ selected, L.cover_of_vertexCover valid cover,
      (L.extended_card valid cover).trans_le (Nat.add_le_add_left card _)⟩

theorem Layout.cover_mono {L : Layout T E} {s t : Finset T}
    (cover : L.cover s) (hst : s ⊆ t) (allowed : t ⊆ L.eligible) : L.cover t := by
  refine ⟨allowed, ?_⟩
  intro edge he
  obtain ⟨tile, ht, hc⟩ := cover.2 edge he
  exact ⟨tile, hst ht, hc⟩

theorem Layout.exact_budget_iff {L : Layout T E} (valid : L.valid) (k : ℕ) :
    (∃ selected : Finset T, L.cover selected ∧
      selected.card = min L.eligible.card (L.guards.card + k)) ↔
    (∃ selected : Finset T, L.vertexCover selected ∧ selected.card ≤ k) := by
  rw [← L.budget_iff valid]
  constructor
  · rintro ⟨s, hc, hs⟩
    exact ⟨s, hc, hs.trans_le (min_le_right _ _)⟩
  · rintro ⟨s, hc, hs⟩
    have lower := le_min (Finset.card_le_card hc.1) hs
    obtain ⟨t, hst, ht, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hc.1 lower (min_le_left _ _)
    exact ⟨t, L.cover_mono hc hst ht, hcard⟩

def Layout.minimumCover (L : Layout T E) (k : ℕ) : Prop :=
  (∃ s, L.cover s ∧ s.card = k) ∧ ∀ s, L.cover s → k ≤ s.card

def Layout.minimumVertexCover (L : Layout T E) (k : ℕ) : Prop :=
  (∃ s, L.vertexCover s ∧ s.card = k) ∧ ∀ s, L.vertexCover s → k ≤ s.card

theorem Layout.minimum_iff {L : Layout T E} (valid : L.valid) (k : ℕ) :
    L.minimumCover (L.guards.card + k) ↔ L.minimumVertexCover k := by
  constructor
  · rintro ⟨⟨tiles, hc, hk⟩, hlo⟩
    refine ⟨⟨tiles \ L.guards, L.vertexCover_of_cover valid hc, ?_⟩, ?_⟩
    · exact Nat.add_left_cancel ((L.forced_card valid hc).symm.trans hk)
    · intro selected hvc
      have h := hlo _ (L.cover_of_vertexCover valid hvc)
      rw [L.extended_card valid hvc] at h
      exact Nat.le_of_add_le_add_left h
  · rintro ⟨⟨selected, hvc, hk⟩, hlo⟩
    refine ⟨⟨L.guards ∪ selected, L.cover_of_vertexCover valid hvc, ?_⟩, ?_⟩
    · simpa [hk] using L.extended_card valid hvc
    · intro tiles hc
      rw [L.forced_card valid hc]
      exact Nat.add_le_add_left (hlo _ (L.vertexCover_of_cover valid hc)) _

end GridCover
