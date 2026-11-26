import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Independent statement of AutoGraphForge survivor 5ed263d5, line 2530 of
`results/survivors_by_touch_normalised.txt` at commit
`4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. GraphCalc defines the vertex
clique cover number to be the chromatic number of the complement. The graph
class is finite simple undirected regular graphs with at least two vertices. -/
namespace CliqueCoverStatement

/-- On a finite graph the complement has a finite chromatic number. -/
noncomputable def vertexCliqueCoverNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  Gᶜ.chromaticNumber.toNat

def Pastorek5ed263d5 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V → (∃ d : ℕ, G.IsRegularOfDegree d) →
    G.diam ≤ vertexCliqueCoverNumber G + 1

/-- The same catalogue inequality on the numerical diameter's evaluation
domain. AutoGraphForge's GraphCalc wrapper treats diameter as undefined
on disconnected graphs. -/
def Pastorek5ed263d5OnDomain : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V → (∃ d : ℕ, G.IsRegularOfDegree d) → G.Connected →
    G.diam ≤ vertexCliqueCoverNumber G + 1

end CliqueCoverStatement
