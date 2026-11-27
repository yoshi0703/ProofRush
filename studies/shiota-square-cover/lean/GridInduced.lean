import GridGeometry

namespace GridCover

def boundaryOrder (c : Center) : List Center :=
  let (x,y) := c
  [(x-1,y-1), (x,y-1), (x+1,y-1), (x+1,y), (x+1,y+1), (x,y+1), (x-1,y+1), (x-1,y)]

def edgeEnds : GridEdge → Center × Center
  | .horizontal x y => ((x,y),(x+1,y))
  | .vertical x y => ((x,y),(x,y+1))

theorem boundary_eight (c : Center) :
    (boundaryOrder c).length = 8 ∧ (boundaryOrder c).Nodup := by
  rcases c with ⟨x,y⟩
  simp [boundaryOrder, List.Nodup, Prod.mk.injEq]
  omega

/-- Every ambient unit edge between two of the eight perimeter vertices
belongs to the prescribed square boundary. -/
theorem induced_unit_edges (p : Center) (e : GridEdge) :
    (edgeEnds e).1 ∈ boundaryOrder p ∧ (edgeEnds e).2 ∈ boundaryOrder p ↔ e ∈ perimeter p := by
  rcases p with ⟨x,y⟩
  cases e <;> simp [boundaryOrder, edgeEnds, perimeter, Prod.mk.injEq] <;> omega

def inducedGridEdges (input : Finset GridEdge) (p : Center) : Finset GridEdge :=
  input.filter fun e => (edgeEnds e).1 ∈ boundaryOrder p ∧ (edgeEnds e).2 ∈ boundaryOrder p

theorem induced_eq_inter (input : Finset GridEdge) (p : Center) :
    inducedGridEdges input p = input ∩ perimeter p := by
  ext e
  simp [inducedGridEdges, induced_unit_edges]

theorem legal_square_iff_induced (input : Finset GridEdge) (p : Center) :
    p ∈ admissible input ↔ inducedGridEdges input p = perimeter p := by
  rw [mem_admissible, induced_eq_inter, Finset.inter_eq_right]

end GridCover
