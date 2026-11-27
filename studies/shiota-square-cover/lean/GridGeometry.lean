import GridCover
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Basic

namespace GridCover

abbrev Center := ℤ × ℤ

/-- An undirected unit edge identified by its left or bottom endpoint. -/
inductive GridEdge
  | horizontal (x y : ℤ)
  | vertical (x y : ℤ)
  deriving DecidableEq, Repr

def perimeter (center : Center) : Finset GridEdge :=
  let (x, y) := center
  { .horizontal (x - 1) (y - 1), .horizontal x (y - 1),
    .horizontal (x - 1) (y + 1), .horizontal x (y + 1),
    .vertical (x - 1) (y - 1), .vertical (x - 1) y,
    .vertical (x + 1) (y - 1), .vertical (x + 1) y }

/-- The four possible centers of a 2 by 2 square with this perimeter edge. -/
def incidentCenters : GridEdge → Finset Center
  | .horizontal x y => {(x, y - 1), (x, y + 1), (x + 1, y - 1), (x + 1, y + 1)}
  | .vertical x y => {(x - 1, y), (x + 1, y), (x - 1, y + 1), (x + 1, y + 1)}

theorem mem_incidentCenters (edge : GridEdge) (center : Center) :
    center ∈ incidentCenters edge ↔ edge ∈ perimeter center := by
  rcases center with ⟨x, y⟩
  cases edge <;> simp [incidentCenters, perimeter, Prod.mk.injEq] <;> omega

/-- Enumerate all admissible square centers from the input edge list itself. -/
def admissible (required : Finset GridEdge) : Finset Center :=
  (required.biUnion incidentCenters).filter fun p => perimeter p ⊆ required

theorem mem_admissible (required : Finset GridEdge) (center : Center) :
    center ∈ admissible required ↔ perimeter center ⊆ required := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    let edge := GridEdge.horizontal (center.1 - 1) (center.2 - 1)
    have he : edge ∈ perimeter center := by
      rcases center with ⟨x, y⟩
      simp [edge, perimeter]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨edge, h he, (mem_incidentCenters edge center).mpr he⟩, h⟩

def seedEdges (seeds : Finset Center) : Finset GridEdge := seeds.biUnion perimeter

theorem mem_seedEdges (seeds : Finset Center) (edge : GridEdge) :
    edge ∈ seedEdges seeds ↔ ∃ seed ∈ incidentCenters edge, seed ∈ seeds := by
  simp only [seedEdges, Finset.mem_biUnion, mem_incidentCenters]
  exact exists_congr fun _ => and_comm

def nearby (radius : ℤ) (p q : Center) : Prop :=
  p.1 - radius ≤ q.1 ∧ q.1 ≤ p.1 + radius ∧
  p.2 - radius ≤ q.2 ∧ q.2 ≤ p.2 + radius

theorem nearby_trans {a b c : Center} {r s : ℤ}
    (hab : nearby r a b) (hbc : nearby s b c) : nearby (r + s) a c := by
  unfold nearby at *
  omega

theorem sharedEdge_nearby {edge : GridEdge} {p q : Center}
    (hp : p ∈ incidentCenters edge) (hq : q ∈ incidentCenters edge) : nearby 2 p q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  cases edge <;>
    simp [incidentCenters, Prod.mk.injEq, nearby] at hp hq ⊢ <;> omega

theorem seedEdge_local {seeds other : Finset Center} {edge : GridEdge} {p : Center}
    (hp : p ∈ incidentCenters edge)
    (same : ∀ q, nearby 2 p q → (q ∈ seeds ↔ q ∈ other)) :
    edge ∈ seedEdges seeds ↔ edge ∈ seedEdges other := by
  rw [mem_seedEdges, mem_seedEdges]
  refine exists_congr fun q => and_congr_right fun hq => ?_
  exact same q (sharedEdge_nearby hp hq)

theorem admissible_local {seeds other : Finset Center} {p : Center}
    (same : ∀ q, nearby 2 p q → (q ∈ seeds ↔ q ∈ other)) :
    p ∈ admissible (seedEdges seeds) ↔ p ∈ admissible (seedEdges other) := by
  rw [mem_admissible, mem_admissible]
  exact forall₂_congr fun edge he =>
    seedEdge_local ((mem_incidentCenters edge p).mpr he) same

/-- A size-four collar around any incident center determines every admissible
tile capable of covering the edge under consideration. -/
theorem edgeCoverers_local {seeds other : Finset Center} {edge : GridEdge} {p : Center}
    (hp : p ∈ incidentCenters edge)
    (same : ∀ q, nearby 4 p q → (q ∈ seeds ↔ q ∈ other)) :
    (incidentCenters edge).filter (· ∈ admissible (seedEdges seeds)) =
      (incidentCenters edge).filter (· ∈ admissible (seedEdges other)) := by
  ext tile
  simp only [Finset.mem_filter]
  refine and_congr_right fun ht => admissible_local fun q hq => same q ?_
  exact nearby_trans (sharedEdge_nearby hp ht) hq

def physicalCover (required : Finset GridEdge) (selected : Finset Center) : Prop :=
  (∀ center ∈ selected, perimeter center ⊆ required) ∧
  ∀ edge ∈ required, ∃ center ∈ selected, edge ∈ perimeter center

def gridLayout (guards optional : Finset Center) (required : Finset GridEdge)
    (graph : Finset (Center × Center)) : Layout Center GridEdge where
  guards := guards
  optional := optional
  required := required
  graph := graph
  incidence := (guards ∪ optional).biUnion fun center =>
    ((perimeter center).filter (· ∈ required)).image (Prod.mk center)

theorem gridCovered_iff {guards optional : Finset Center} {required : Finset GridEdge}
    {graph : Finset (Center × Center)} {center : Center} {edge : GridEdge} :
    (gridLayout guards optional required graph).covered center edge ↔
      center ∈ guards ∪ optional ∧ edge ∈ required ∧ edge ∈ perimeter center := by
  unfold Layout.covered gridLayout
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨p, hpo, e, ⟨hp, hr⟩, rfl, rfl⟩
    exact ⟨hpo, hr, hp⟩
  · rintro ⟨hp, hr, he⟩
    exact ⟨center, hp, edge, ⟨he, hr⟩, rfl, rfl⟩

def gridValid (guards optional : Finset Center) (required : Finset GridEdge)
    (graph : Finset (Center × Center)) : Prop :=
  admissible required = guards ∪ optional ∧ (gridLayout guards optional required graph).valid

instance (guards optional : Finset Center) (required : Finset GridEdge)
    (graph : Finset (Center × Center)) : Decidable (gridValid guards optional required graph) := by
  unfold gridValid
  infer_instance

theorem physicalCover_iff {guards optional : Finset Center} {required : Finset GridEdge}
    {graph : Finset (Center × Center)} (valid : gridValid guards optional required graph)
    (selected : Finset Center) :
    physicalCover required selected ↔ (gridLayout guards optional required graph).cover selected := by
  let L := gridLayout guards optional required graph
  constructor
  · rintro ⟨tiles, edges⟩
    have hm : selected ⊆ L.eligible := by
      intro center hc
      change center ∈ guards ∪ optional
      rw [← valid.1]
      exact (mem_admissible required center).mpr (tiles center hc)
    refine ⟨hm, ?_⟩
    intro edge he
    obtain ⟨center, hc, hp⟩ := edges edge he
    exact ⟨center, hc, gridCovered_iff.mpr ⟨hm hc, he, hp⟩⟩
  · rintro ⟨tiles, edges⟩
    constructor
    · intro center hc
      apply (mem_admissible required center).mp
      rw [valid.1]
      exact tiles hc
    · intro edge he
      obtain ⟨center, hc, hi⟩ := edges edge he
      exact ⟨center, hc, (gridCovered_iff.mp hi).2.2⟩

theorem physicalBudget_iff {guards optional : Finset Center} {required : Finset GridEdge}
    {graph : Finset (Center × Center)} (valid : gridValid guards optional required graph) (k : ℕ) :
    (∃ selected : Finset Center, physicalCover required selected ∧ selected.card ≤ guards.card + k) ↔
    (∃ selected : Finset Center,
      (gridLayout guards optional required graph).vertexCover selected ∧ selected.card ≤ k) := by
  have h := Layout.budget_iff valid.2 k
  simpa only [physicalCover_iff valid, gridLayout] using h

theorem physicalExactBudget_iff {guards optional : Finset Center} {required : Finset GridEdge}
    {graph : Finset (Center × Center)} (valid : gridValid guards optional required graph) (k : ℕ) :
    (∃ selected : Finset Center, physicalCover required selected ∧
      selected.card = min (admissible required).card (guards.card + k)) ↔
    (∃ selected : Finset Center,
      (gridLayout guards optional required graph).vertexCover selected ∧ selected.card ≤ k) := by
  have h := Layout.exact_budget_iff valid.2 k
  simpa only [physicalCover_iff valid, valid.1, Layout.eligible, gridLayout] using h

end GridCover
