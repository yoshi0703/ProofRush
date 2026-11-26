import WorstRate
import MergeForest
import ForestMass
import ForestCounts
import ForestArithmetic
import ForestChronoCount
import ForestShortMass

/-! Matching square-root upper and lower rates for the public replacement-
and overlapping-count greedy runs on ambiguous string-identified inputs. -/

namespace SpellingUniversalRate

open SpellingBPE SpellingMatching SpellingWorstRate DiamondLimit BPEForest

variable {α : Type} [DecidableEq α]

private theorem selected_count_bound {k G t count : ℕ} {w : Word α}
    {labels : Finset (Pair α)} (hk : 0 < k) (covered : count ≤ mass labels w)
    (few : labels.card ≤ t*k)
    (greedy : k*mass labels w ≤ (3*k+2*labels.card)*G) :
    count ≤ (3+2*t)*G := by
  apply Nat.le_of_mul_le_mul_left _ hk
  calc
    k*count ≤ k*mass labels w := Nat.mul_le_mul_left _ covered
    _ ≤ (3*k+2*labels.card)*G := greedy
    _ ≤ (3*k+2*(t*k))*G :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2 few) _)
    _ = k*((3+2*t)*G) := by ring

omit [DecidableEq α] in
private theorem forest_nodes_bound (trees : List (MergeTree α)) :
    (trees.map MergeTree.nodes).sum ≤
      2*(trees.map MergeTree.cherries).sum + (trees.map MergeTree.unary).sum := by
  induction trees with
  | nil => simp
  | cons t trees ih =>
    have hb := t.binary_le_cherries
    have head : t.nodes ≤ 2*t.cherries+t.unary := by
      rw [t.split_nodes]
      omega
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem feasible_rate_of_forest {k j : ℕ} {w u v : Word α}
    (hk : 0 < k) (leBudget : j ≤ k) (feasible : Feasible j w u)
    (greedy : ∀ labels : Finset (Pair α),
      k*mass labels w ≤ (3*k+2*labels.card)*(w.length-v.length))
    (forest : ∀ (rules : List (Pair α)) (trees : List (MergeTree α)), rules.length = j →
      (∀ t ∈ trees, t.Valid rules j) →
      ∃ (labels : Finset (Pair α)) (shortCount : ℕ),
        labels.card ≤ (2*scale k)*j ∧ shortCount ≤ mass labels (trees.flatMap MergeTree.leaves) ∧
        scale k * (trees.map MergeTree.unary).sum ≤
          scale k * shortCount + 4*scale k*(trees.map MergeTree.cherries).sum +
            4*j*(trees.map MergeTree.cherries).sum) :
    w.length-u.length ≤ 57*scale k*(w.length-v.length) := by
  obtain ⟨rules, numRules, trees, original, _, valid, used⟩ := comparator_forest feasible
  let C := (trees.map MergeTree.cherries).sum
  let U := (trees.map MergeTree.unary).sum
  let G := w.length-v.length
  let s := scale k
  have divided := forest_nodes_bound trees
  rw [used] at divided
  have cherryMass := forest_cherries_le_mass rules trees valid
  rw [original] at cherryMass
  have cherryLabels : rules.toFinset.card ≤ 1*k := by
    rw [one_mul]
    exact (cherry_labels_card_le rules).trans (numRules.le.trans leBudget)
  have cherry : C ≤ 5*G := selected_count_bound hk cherryMass cherryLabels (greedy _)
  obtain ⟨labels,E,few,shortMass,unaryCost⟩ := forest rules trees numRules valid
  rw [original] at shortMass
  have shortLabels : labels.card ≤ (2*s)*k := few.trans (Nat.mul_le_mul_left _ leBudget)
  have edges : E ≤ (3+4*s)*G := by
    have small := selected_count_bound hk shortMass shortLabels (greedy _)
    simpa only [← Nat.mul_assoc] using small
  have increaseCost : 4*j*C ≤ 4*k*C :=
    Nat.mul_le_mul_right C (Nat.mul_le_mul_left 4 leBudget)
  have charge : s*U ≤ s*E+4*s*C+4*k*C := unaryCost.trans (Nat.add_le_add_left increaseCost _)
  exact sqrt_budget_arithmetic s k C U E (w.length-u.length) G (scale_pos k)
    (budget_le_scale_sq k) divided cherry edges charge

private theorem feasible_rate {k j : ℕ} {w u v : Word α}
    (hk : 0 < k) (leBudget : j ≤ k) (feasible : Feasible j w u)
    (greedy : ∀ labels : Finset (Pair α),
      k*mass labels w ≤ (3*k+2*labels.card)*(w.length-v.length)) :
    w.length-u.length ≤ 57*scale k*(w.length-v.length) := by
  apply feasible_rate_of_forest hk leBudget feasible greedy
  intro rules trees numRules valid
  let s := scale k
  have valid' : ∀ t ∈ trees, t.Valid rules rules.length := by rw [numRules]; exact valid
  refine ⟨BPEForest.shortLabels rules s,(trees.map (selectedCount (shortAt s))).sum,?_,?_,?_⟩
  · have h := shortLabels_card rules s
    rw [numRules] at h
    calc
      _ ≤ 2*j*s := h
      _ = (2*s)*j := by ring
  · exact forest_short_count_le_mass rules s trees valid'
  · have cost := forest_unary_cost rules trees valid' s
    simpa only [numRules] using cost

/-- Universal lower estimate on every completed replacement-count greedy run. -/
theorem replacement_run_bound {k : ℕ} {w v : Word α} (hk : 0 < k) (run : Greedy k w v) :
    optimum w k ≤ 57*scale k*(w.length-v.length) := by
  obtain ⟨j,small,u,comparator,value⟩ := optimum_attained w k
  rw [← value]
  exact feasible_rate hk small comparator (fun labels => greedy_mass_bound labels run)

/-- Universal lower estimate on every completed overlapping-count greedy run. -/
theorem overlapping_run_bound {k : ℕ} {w v : Word α} (hk : 0 < k)
    (run : RawDiamond.RawGreedy k w v) : optimum w k ≤ 57*scale k*(w.length-v.length) := by
  obtain ⟨j,small,u,comparator,value⟩ := optimum_attained w k
  rw [← value]
  exact feasible_rate hk small comparator (fun labels => raw_greedy_mass_bound labels run)

/-- Sharp order of the worst best-tie ratio for the public replacement-count rule. -/
theorem replacement_worst_rate {k : ℕ} (hk : 8 ≤ k) :
    (1 : ℝ)/114 ≤ worst Greedy k * Real.sqrt (k : ℝ) ∧
      worst Greedy k * Real.sqrt (k : ℝ) ≤ 24 := by
  have positive : 0 < k := by omega
  obtain ⟨nonempty,upper⟩ := replacement_diamond hk
  have lower := lower_57_of_runs Greedy (scale_pos k) nonempty
    (fun _ _ _ _ run => replacement_run_bound positive run)
  exact sqrt_bounds Greedy positive lower upper

/-- Sharp order of the worst best-tie ratio for the public overlapping-count rule. -/
theorem overlapping_worst_rate {k : ℕ} (hk : 8 ≤ k) :
    (1 : ℝ)/114 ≤ worst RawDiamond.RawGreedy k * Real.sqrt (k : ℝ) ∧
      worst RawDiamond.RawGreedy k * Real.sqrt (k : ℝ) ≤ 24 := by
  have positive : 0 < k := by omega
  obtain ⟨nonempty,upper⟩ := overlapping_diamond hk
  have lower := lower_57_of_runs RawDiamond.RawGreedy (scale_pos k) nonempty
    (fun _ _ _ _ run => overlapping_run_bound positive run)
  exact sqrt_bounds RawDiamond.RawGreedy positive lower upper

end SpellingUniversalRate

#print axioms SpellingUniversalRate.replacement_run_bound
#print axioms SpellingUniversalRate.overlapping_run_bound
#print axioms SpellingUniversalRate.replacement_worst_rate
#print axioms SpellingUniversalRate.overlapping_worst_rate
