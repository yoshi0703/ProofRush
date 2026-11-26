import CliqueCoverStatement
import Mathlib.Data.Fin.VecNotation

/-! A connected cubic graph with diameter eight and vertex clique cover number six. -/
namespace RegularCliqueCover

open CliqueCoverStatement

abbrev V := Fin 14

private def edges : List (V × V) :=
  [(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(4,5),(5,7),(5,8),(6,7),
   (6,8),(6,13),(7,8),(9,11),(9,12),(9,13),(10,11),(10,12),(10,13),(11,12)]

private def adj (u v : V) : Prop := (u, v) ∈ edges ∨ (v, u) ∈ edges
private instance (u v : V) : Decidable (adj u v) := by unfold adj; infer_instance

def graph : SimpleGraph V where
  Adj := adj
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adj u v))

theorem graph_cubic : graph.IsRegularOfDegree 3 := by
  unfold SimpleGraph.IsRegularOfDegree
  simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

/-- Distances from vertex 7, used as decreasing ranks for paths to 7. -/
private def depth : V → ℕ := ![3,3,4,4,2,1,1,0,1,3,3,4,4,2]

private theorem descend : ∀ u : V, u ≠ 7 → ∃ z : V, graph.Adj u z ∧ depth z < depth u := by
  decide +kernel

private theorem center_walk (u : V) : ∃ p : graph.Walk u 7, p.length ≤ depth u := by
  by_cases he : u = 7
  · subst u; exact ⟨.nil, Nat.zero_le _⟩
  · obtain ⟨v, huv, hlt⟩ := descend u he
    obtain ⟨p, hp⟩ := center_walk v
    exact ⟨p.cons huv, Nat.succ_le_of_lt (lt_of_le_of_lt hp hlt)⟩
termination_by depth u

theorem graph_connected : graph.Connected := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨p, _⟩ := center_walk u
  obtain ⟨q, _⟩ := center_walk v
  exact ⟨p.append q.reverse⟩

/-- A level changes by at most one per edge, measuring eight steps from 2 to 11. -/
private def level : V → ℕ := ![1,1,0,1,2,3,5,4,4,7,7,8,8,6]

private theorem edge_level : ∀ u v : V, graph.Adj u v → level v ≤ level u + 1 := by
  decide +kernel

private theorem walk_level {u v : V} (p : graph.Walk u v) :
    level v ≤ level u + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have := edge_level _ _ h
    rw [SimpleGraph.Walk.length_cons]
    omega

theorem graph_diam : graph.diam = 8 := by
  apply le_antisymm
  · obtain ⟨u, v, huv⟩ := graph.exists_dist_eq_diam
    obtain ⟨p, hp⟩ := center_walk u
    obtain ⟨q, hq⟩ := center_walk v
    have h := SimpleGraph.dist_le (p.append q.reverse)
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, huv] at h
    have bounded : ∀ v : V, depth v ≤ 4 := by decide +kernel
    have := bounded u
    have := bounded v
    omega
  · obtain ⟨p, hp⟩ := graph_connected.exists_walk_length_eq_dist (2 : V) (11 : V)
    have h := walk_level p
    change 8 ≤ 0 + p.length at h
    rw [Nat.zero_add, hp] at h
    exact h.trans (SimpleGraph.dist_le_diam (SimpleGraph.connected_iff_ediam_ne_top.mp graph_connected))

/-- The six fibers of this coloring are vertex cliques of the original graph. -/
private def color : V → Fin 6 := ![0,1,0,0,1,2,3,2,2,4,5,4,4,5]

private theorem color_valid : ∀ u v : V, u ≠ v → ¬ graph.Adj u v → color u ≠ color v := by
  decide +kernel

private def sixColoring : graphᶜ.Coloring (Fin 6) :=
  SimpleGraph.Coloring.mk color fun {v w} h => color_valid v w h.1 h.2

private def independent : Fin 6 → V := ![0,1,5,6,9,10]

private theorem distinct_are_complement_adjacent :
    ∀ i j : Fin 6, i ≠ j → graphᶜ.Adj (independent i) (independent j) := by
  change ∀ i j : Fin 6, i ≠ j →
    independent i ≠ independent j ∧ ¬ graph.Adj (independent i) (independent j)
  decide +kernel

theorem graph_cover : vertexCliqueCoverNumber graph = 6 := by
  apply le_antisymm
  · have h : graphᶜ.chromaticNumber ≤ (6 : ℕ) :=
      (show graphᶜ.Colorable 6 from ⟨sixColoring⟩).chromaticNumber_le
    exact ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
  · obtain ⟨c⟩ := graphᶜ.colorable_chromaticNumber_of_fintype
    have hinj : Function.Injective (fun i : Fin 6 => c (independent i)) := by
      intro i j hij
      by_contra hne
      exact c.valid (distinct_are_complement_adjacent i j hne) hij
    simpa [vertexCliqueCoverNumber] using Fintype.card_le_of_injective _ hinj

private theorem violates_bound : ¬ graph.diam ≤ vertexCliqueCoverNumber graph + 1 := by
  rw [graph_diam, graph_cover]
  decide

/-- Negation of the universal claim printed in the catalogue. -/
theorem refutes_5ed263d5 : ¬ Pastorek5ed263d5 := by
  intro h
  exact violates_bound (h V graph (by decide) ⟨3, graph_cubic⟩)

/-- Negation with connectedness made an explicit evaluation-domain hypothesis. -/
theorem refutes_5ed263d5_on_domain : ¬ Pastorek5ed263d5OnDomain := by
  intro h
  exact violates_bound (h V graph (by decide) ⟨3, graph_cubic⟩ graph_connected)

#print axioms refutes_5ed263d5
#print axioms refutes_5ed263d5_on_domain

end RegularCliqueCover
