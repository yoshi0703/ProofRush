import GridPlacementFinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GridCover.Placement

open scoped BigOperators

theorem card_box (r : ℤ) (p : Center) :
    (box r p).card = ((2*r+1).toNat)^2 := by
  rw [box, Finset.card_product, Int.card_Icc, Int.card_Icc, pow_two]
  have e1 : p.1 + r + 1 - (p.1 - r) = 2*r+1 := by omega
  have e2 : p.2 + r + 1 - (p.2 - r) = 2*r+1 := by omega
  rw [e1, e2]

theorem perimeter_card (p : Center) : (perimeter p).card = 8 := by
  let g := shiftGrid p
  have center : g.point (0,0) = p := by simp [g, add]
  have map_eq : (perimeter (0,0)).map g.edge.toEmbedding = perimeter p := by
    ext e
    obtain ⟨f,rfl⟩ := g.edge.surjective e
    rw [← center, g.perim]
    simp
  rw [← map_eq, Finset.card_map]
  decide

theorem Layout.domain_bound (A : Layout) (length : ∀ s ∈ A.runs, s.length = 17) :
    A.domain.card ≤ 49*A.hubs.card + 1225*A.runs.card := by
  unfold domain
  have H : (A.hubs.biUnion (box 3)).card ≤ 49*A.hubs.card := by
    calc
      _ ≤ ∑ h ∈ A.hubs, (box 3 h).card := Finset.card_biUnion_le
      _ = 49*A.hubs.card := by simp [card_box, Nat.mul_comm]
  have R : (A.runs.biUnion fun s => box s.length s.start).card ≤ 1225*A.runs.card := by
    calc
      _ ≤ ∑ s ∈ A.runs, (box s.length s.start).card := Finset.card_biUnion_le
      _ = ∑ _s ∈ A.runs, 1225 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [length s hs, card_box]
        decide
      _ = 1225*A.runs.card := by simp [Nat.mul_comm]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add H R)

theorem Layout.seed_count (A : Layout) : (A.guardSet ∪ A.optionalSet).card ≤ A.domain.card := by
  apply Finset.card_le_card
  exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem Layout.edge_count (A : Layout) :
    (seedEdges (A.guardSet ∪ A.optionalSet)).card ≤ 8*A.domain.card := by
  calc
    _ ≤ ∑ p ∈ A.guardSet ∪ A.optionalSet, (perimeter p).card := Finset.card_biUnion_le
    _ = 8*(A.guardSet ∪ A.optionalSet).card := by simp [perimeter_card, Nat.mul_comm]
    _ ≤ 8*A.domain.card := Nat.mul_le_mul_left _ A.seed_count

theorem CoarseDrawing.output_size (D : CoarseDrawing) (switch : Center → Bool)
    (hv : ∀ h ∈ D.shapeHubs, ValidPorts (switch h) (portsOf D.shapeRuns h)) :
    let A := D.concrete switch hv
    (seedEdges (A.guardSet ∪ A.optionalSet)).card ≤ 8*(49*D.hubs.card+1225*D.runs.card) := by
  dsimp only
  let A := D.concrete switch hv
  have HB : A.hubs.card ≤ D.hubs.card := Finset.card_image_le
  have RB : A.runs.card ≤ D.runs.card := Finset.card_image_le
  have RL : ∀ s ∈ A.runs, s.length = 17 := by
    intro s hs
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (show s ∈ D.shapeRuns from hs)
    change 17*u.length = 17
    rw [D.lengthOne u hu]
    decide
  exact A.edge_count.trans (Nat.mul_le_mul_left _ ((A.domain_bound RL).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ HB) (Nat.mul_le_mul_left _ RB))))

theorem CoarseDrawing.output_coordinate_bound (D : CoarseDrawing) (switch : Center → Bool)
    (hv : ∀ h ∈ D.shapeHubs, ValidPorts (switch h) (portsOf D.shapeRuns h)) (B : ℤ)
    (hB : ∀ h ∈ D.hubs, nearby B (0,0) h) :
    ∀ p ∈ (D.concrete switch hv).domain, nearby (17*B+17) (0,0) p := by
  intro p hp
  let A := D.concrete switch hv
  have hubBound : ∀ h ∈ A.hubs, nearby (17*B) (0,0) h := by
    intro h hh
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp (show h ∈ D.shapeHubs from hh)
    have hb := hB t ht
    unfold nearby at hb
    unfold nearby scalePoint
    simp at hb ⊢
    omega
  change p ∈ (A.hubs.biUnion fun h => box 3 h) ∪ (A.runs.biUnion fun s => box s.length s.start) at hp
  rcases Finset.mem_union.mp hp with hCore | hStrip
  · obtain ⟨h,hh,near⟩ := Finset.mem_biUnion.mp hCore
    exact nearby_mono (by omega) (nearby_trans (hubBound h hh) (mem_box.mp near))
  · obtain ⟨s,hs,near⟩ := Finset.mem_biUnion.mp hStrip
    have L : s.length = 17 := by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp (show s ∈ D.shapeRuns from hs)
      change 17*u.length = 17
      rw [D.lengthOne u hu]
      decide
    have hn := mem_box.mp near
    rw [L] at hn
    exact nearby_trans (hubBound _ (A.startHub s hs)) hn

end GridCover.Placement
