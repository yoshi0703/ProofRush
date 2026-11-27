import GridGlobal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Union

namespace GridCover
namespace PathEmbedding

open scoped BigOperators

variable {V P E : Type*} [DecidableEq V] [DecidableEq P]

/-- Consecutive oriented pairs of the path with the two endpoint hubs. -/
def pairs (left : P) : List P → P → List (P × P)
  | [], right => [(left, right)]
  | first :: rest, right => (left, first) :: pairs first rest right

omit [DecidableEq P] in
theorem covers_iff_pairs (flag : P → Bool) (left : P) (inside : List P) (right : P) :
    OddPath.covers (flag left) (inside.map flag) (flag right) ↔
      ∀ pair ∈ pairs left inside right, OddPath.touches (flag pair.1) (flag pair.2) := by
  induction inside generalizing left with
  | nil => simp [pairs, OddPath.covers]
  | cons first rest ih =>
    simp only [pairs, List.map_cons, OddPath.covers, List.forall_mem_cons, ih]

/-- The selected centers obtained by assigning one bit to each internal path center. -/
def marked : List P → List Bool → Finset P
  | p :: ps, b :: bs => if b then insert p (marked ps bs) else marked ps bs
  | _, _ => ∅

theorem marked_subset (ps : List P) (bs : List Bool) :
    marked ps bs ⊆ ps.toFinset := by
  induction ps generalizing bs with
  | nil => simp [marked]
  | cons p ps ih =>
    cases bs with
    | nil => simp [marked]
    | cons b bs =>
      cases b <;> simp only [marked, Bool.false_eq_true, ite_false, ite_true, List.toFinset_cons]
      · exact (ih bs).trans (Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert _ (ih bs)

theorem map_marked (ps : List P) (bs : List Bool)
    (hlen : bs.length = ps.length) (hd : ps.Nodup) :
    ps.map (OddPath.chosenBool (marked ps bs)) = bs := by
  induction ps generalizing bs with
  | nil => cases bs <;> simp_all
  | cons p ps ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : bs.length = ps.length := Nat.succ.inj hlen
      obtain ⟨fresh, hnd⟩ := List.nodup_cons.mp hd
      have hp : p ∉ marked ps bs := fun hm => fresh (List.mem_toFinset.mp (marked_subset ps bs hm))
      have tail : ps.map (OddPath.chosenBool (marked ps bs)) = bs := ih bs htail hnd
      cases b with
      | false => simpa [marked, OddPath.chosenBool, hp] using tail
      | true =>
        simp only [marked, ite_true, List.map_cons, List.cons.injEq]
        refine ⟨by simp [OddPath.chosenBool], ?_⟩
        calc
          _ = ps.map (OddPath.chosenBool (marked ps bs)) := by
            apply List.map_congr_left
            intro q hq
            have hne : q ≠ p := fun h => fresh (h ▸ hq)
            simp [OddPath.chosenBool, hne]
          _ = bs := tail

theorem card_marked (ps : List P) (bs : List Bool)
    (hlen : bs.length = ps.length) (hd : ps.Nodup) :
    (marked ps bs).card = OddPath.cost bs := by
  induction ps generalizing bs with
  | nil => cases bs <;> simp_all [marked, OddPath.cost]
  | cons p ps ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : bs.length = ps.length := Nat.succ.inj hlen
      obtain ⟨fresh, hnd⟩ := List.nodup_cons.mp hd
      have hp : p ∉ marked ps bs := fun hm => fresh (List.mem_toFinset.mp (marked_subset ps bs hm))
      cases b <;> simp [marked, OddPath.cost, OddPath.paid, hp, ih bs htail hnd, Nat.add_comm]

theorem marked_map (ps : List P) (s : Finset P) :
    marked ps (ps.map (OddPath.chosenBool s)) = ps.toFinset.filter (· ∈ s) := by
  induction ps with
  | nil => simp [marked]
  | cons p ps ih =>
    ext q
    by_cases h : p ∈ s <;> simp [marked, OddPath.chosenBool, ih, h] <;> aesop

structure Embedded (V P : Type*) [DecidableEq V] [DecidableEq P] where
  vertices : Finset V
  edges : Finset (V × V)
  hub : V ↪ P
  inside : (V × V) → List P
  t : (V × V) → ℕ
  endpoints : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices
  length : ∀ e ∈ edges, (inside e).length = 2 * t e
  nodup : ∀ e ∈ edges, (inside e).Nodup
  hub_clear : ∀ e ∈ edges, Disjoint (vertices.map hub) (inside e).toFinset
  route_clear : ∀ e ∈ edges, ∀ f ∈ edges, e ≠ f →
    Disjoint (inside e).toFinset (inside f).toFinset

namespace Embedded
variable (A : Embedded V P)

def points : Finset P :=
  A.vertices.map A.hub ∪ A.edges.biUnion (fun e => (A.inside e).toFinset)

def allPairs : Finset (P × P) :=
  A.edges.biUnion (fun e => (pairs (A.hub e.1) (A.inside e) (A.hub e.2)).toFinset)

def represents (L : Layout P E) : Prop :=
  A.points ⊆ L.optional ∧
    ∀ p q, ((p,q) ∈ L.graph ∨ (q,p) ∈ L.graph) ↔
      ((p,q) ∈ A.allPairs ∨ (q,p) ∈ A.allPairs)

theorem coverPairs_iff {L : Layout P E} (h : A.represents L) (s : Finset P) :
    OddPath.vertexCover L.graph s ↔ OddPath.vertexCover A.allPairs s := by
  constructor
  · intro hs
    rintro ⟨p,q⟩ hpq
    rcases (h.2 p q).mpr (Or.inl hpq) with he | he
    · exact hs (p,q) he
    · exact (hs (q,p) he).symm
  · intro hs
    rintro ⟨p,q⟩ hpq
    rcases (h.2 p q).mp (Or.inl hpq) with he | he
    · exact hs (p,q) he
    · exact (hs (q,p) he).symm

def extractHubs (s : Finset P) : Finset V := A.vertices.filter (fun v => A.hub v ∈ s)

def extractBits (s : Finset P) (e : V × V) : List Bool :=
  (A.inside e).map (OddPath.chosenBool s)

def realize (s : Finset V) (b : (V × V) → List Bool) : Finset P :=
  ((A.vertices ∩ s).map A.hub) ∪ A.edges.biUnion (fun e => marked (A.inside e) (b e))

theorem realize_subset (s : Finset V) (b : (V × V) → List Bool) :
    A.realize s b ⊆ A.points := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · have hm := Finset.mem_map.mp hp
    obtain ⟨v,hv,rfl⟩ := hm
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩)
  · obtain ⟨e,he,hm⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, marked_subset _ _ hm⟩)

theorem hub_mem_realize (s : Finset V) (b : (V × V) → List Bool) {v : V}
    (hv : v ∈ A.vertices) : A.hub v ∈ A.realize s b ↔ v ∈ s := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hm | hi
    · exact (Finset.mem_inter.mp (Finset.mem_map.mp hm |>.elim
        (fun v' h' => A.hub.injective h'.2 ▸ h'.1))).2
    · obtain ⟨e,he,hm⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.disjoint_left.mp (A.hub_clear e he) (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
        (marked_subset _ _ hm)).elim
  · intro hs
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨v, Finset.mem_inter.mpr ⟨hv,hs⟩, rfl⟩)

theorem inside_mem_realize (s : Finset V) (b : (V × V) → List Bool) {e : V × V}
    (he : e ∈ A.edges) {p : P} (hp : p ∈ A.inside e) :
    p ∈ A.realize s b ↔ p ∈ marked (A.inside e) (b e) := by
  have hp' : p ∈ (A.inside e).toFinset := List.mem_toFinset.mpr hp
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hm | hi
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hm
      exact (Finset.disjoint_left.mp (A.hub_clear e he)
        (Finset.mem_map.mpr ⟨v, (Finset.mem_inter.mp hv).1, rfl⟩) hp').elim
    · obtain ⟨f,hf,hm⟩ := Finset.mem_biUnion.mp hi
      by_cases hef : e = f
      · simpa [hef] using hm
      · exact (Finset.disjoint_left.mp (A.route_clear e he f hf hef) hp'
          (marked_subset _ _ hm)).elim
  · intro hm
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e,he,hm⟩)

theorem extract_cover (s : Finset P) (hs : OddPath.vertexCover A.allPairs s) :
    OddPath.subdividedCover A.edges A.t (A.extractHubs s) (A.extractBits s) := by
  intro e he
  have hv := A.endpoints e he
  have flag (v : V) (h : v ∈ A.vertices) :
      OddPath.chosenBool (A.extractHubs s) v = OddPath.chosenBool s (A.hub v) := by
    simp [OddPath.chosenBool, extractHubs, h]
  refine ⟨by simp [extractBits, A.length e he], ?_⟩
  rw [flag _ hv.1, flag _ hv.2]
  apply (covers_iff_pairs _ _ _ _).mpr
  intro pair hpair
  exact OddPath.touches_chosenBool.mpr
    (hs pair (Finset.mem_biUnion.mpr ⟨e, he, List.mem_toFinset.mpr hpair⟩))

theorem realize_cover (s : Finset V) (b : (V × V) → List Bool)
    (h : OddPath.subdividedCover A.edges A.t s b) :
    OddPath.vertexCover A.allPairs (A.realize s b) := by
  intro pair hpair
  obtain ⟨e,he,hp⟩ := Finset.mem_biUnion.mp hpair
  have hv := A.endpoints e he
  let flag := OddPath.chosenBool (A.realize s b)
  have endpoint (v : V) (hv : v ∈ A.vertices) :
      flag (A.hub v) = OddPath.chosenBool s v := by
    simp [flag, OddPath.chosenBool, A.hub_mem_realize s b hv]
  have marks : (A.inside e).map flag = b e := by
    rw [← map_marked (A.inside e) (b e) ((h e he).1.trans (A.length e he).symm) (A.nodup e he)]
    apply List.map_congr_left
    intro p hp
    simp [flag, OddPath.chosenBool, A.inside_mem_realize s b he hp]
  have hc : OddPath.covers (flag (A.hub e.1)) ((A.inside e).map flag) (flag (A.hub e.2)) := by
    rw [endpoint _ hv.1, endpoint _ hv.2, marks]
    exact (h e he).2
  exact OddPath.touches_chosenBool.mp
    ((covers_iff_pairs _ _ _ _).mp hc pair (List.mem_toFinset.mp hp))

theorem realize_card (s : Finset V) (b : (V × V) → List Bool)
    (h : OddPath.subdividedCover A.edges A.t s b) :
    (A.realize s b).card = (A.vertices ∩ s).card + ∑ e ∈ A.edges, OddPath.cost (b e) := by
  have dh : Disjoint ((A.vertices ∩ s).map A.hub)
      (A.edges.biUnion (fun e => marked (A.inside e) (b e))) := by
    apply Finset.disjoint_left.mpr
    intro p hm hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨e,he,hp⟩ := Finset.mem_biUnion.mp hi
    exact Finset.disjoint_left.mp (A.hub_clear e he)
      (Finset.mem_map.mpr ⟨v,(Finset.mem_inter.mp hv).1,rfl⟩) (marked_subset _ _ hp)
  have dp : (A.edges : Set (V × V)).PairwiseDisjoint (fun e => marked (A.inside e) (b e)) := by
    intro e he f hf hef
    exact (A.route_clear e he f hf hef).mono (marked_subset _ _) (marked_subset _ _)
  unfold realize
  rw [Finset.card_union_of_disjoint dh, Finset.card_map, Finset.card_biUnion dp]
  congr 1
  exact Finset.sum_congr rfl (fun e he =>
    card_marked _ _ ((h e he).1.trans (A.length e he).symm) (A.nodup e he))

theorem realize_extract (s : Finset P) :
    A.realize (A.extractHubs s) (A.extractBits s) = A.points.filter (· ∈ s) := by
  ext p
  constructor
  · intro h
    refine Finset.mem_filter.mpr ⟨A.realize_subset _ _ h, ?_⟩
    rcases Finset.mem_union.mp h with hm | hi
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hm
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
    · obtain ⟨e,he,hm⟩ := Finset.mem_biUnion.mp hi
      rw [extractBits, marked_map] at hm
      exact (Finset.mem_filter.mp hm).2
  · intro h
    obtain ⟨hp,hs⟩ := Finset.mem_filter.mp h
    rcases Finset.mem_union.mp hp with hm | hi
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hm
      exact (A.hub_mem_realize _ _ hv).mpr (Finset.mem_filter.mpr ⟨hv, hs⟩)
    · obtain ⟨e,he,hm⟩ := Finset.mem_biUnion.mp hi
      apply (A.inside_mem_realize _ _ he (List.mem_toFinset.mp hm)).mpr
      rw [extractBits, marked_map]
      exact Finset.mem_filter.mpr ⟨hm, hs⟩

/-- Transfer an arbitrary cost bound between a layout's geometric optional graph
and the existing labelled odd-subdivision model. Extra optional isolated sites
(and irrelevant original labels) can be discarded. -/
theorem budget_iff_subdivided {L : Layout P E} (h : A.represents L) (k : ℕ) :
    (∃ s : Finset P, L.vertexCover s ∧ s.card ≤ k) ↔
    (∃ (s : Finset V) (b : (V × V) → List Bool),
      OddPath.subdividedCover A.edges A.t s b ∧ OddPath.subdivisionCost A.edges s b ≤ k) := by
  constructor
  · rintro ⟨s,hcov,hcard⟩
    have hex := A.extract_cover s ((A.coverPairs_iff h s).mp hcov.2)
    refine ⟨A.extractHubs s, A.extractBits s, hex, ?_⟩
    have hcost := A.realize_card _ _ hex
    have hsub : A.extractHubs s ⊆ A.vertices := Finset.filter_subset _ _
    rw [Finset.inter_eq_right.mpr hsub, A.realize_extract] at hcost
    rw [OddPath.subdivisionCost, ← hcost]
    exact (Finset.card_le_card (show (A.points.filter (· ∈ s)) ⊆ s from fun _ hp =>
      (Finset.mem_filter.mp hp).2)).trans hcard
  · rintro ⟨s,b,hcov,hcard⟩
    refine ⟨A.realize s b, ⟨(A.realize_subset _ _).trans h.1,
      (A.coverPairs_iff h _).mpr (A.realize_cover _ _ hcov)⟩, ?_⟩
    rw [A.realize_card _ _ hcov]
    exact (Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_right) _).trans hcard

/-- The full cost bridge starts with an assembled geometry that already
passes all local patch tests and represents independently embedded odd paths. -/
theorem assembled_path_budget_iff (A : Embedded V Center)
    {guards optional : Finset Center} {graph : Finset (Center × Center)}
    (disjoint : Disjoint guards optional) (graphOK : AssemblyGraphOK optional graph)
    (patches : HasCertifiedPatches (assemblyRoles guards optional) (assemblyLinks graph))
    (h : A.represents (gridLayout guards optional (seedEdges (guards ∪ optional)) graph)) (k : ℕ) :
    (∃ s : Finset Center, physicalCover (seedEdges (guards ∪ optional)) s ∧
      s.card = min (guards ∪ optional).card ((guards.card + (∑ e ∈ A.edges, A.t e)) + k)) ↔
    (∃ s : Finset V, OddPath.vertexCover A.edges s ∧ s.card ≤ k) := by
  rw [Nat.add_assoc, assembled_exact_budget disjoint graphOK patches,
    A.budget_iff_subdivided h]
  exact (OddPath.subdivision_budget_iff A.edges A.t k).symm

omit [DecidableEq P] in
@[simp] theorem pairs_length (left : P) (inside : List P) (right : P) :
    (pairs left inside right).length = inside.length + 1 := by
  induction inside generalizing left with
  | nil => rfl
  | cons first rest ih => simp [pairs, ih, Nat.add_assoc]

end Embedded
end PathEmbedding
end GridCover

#print axioms GridCover.PathEmbedding.Embedded.assembled_path_budget_iff
