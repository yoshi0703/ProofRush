import ForestChronology
import ForestEdges

/-! Charge every unary-node attachment to a selected short gap, the start
of a side path, or its chain's bounded time interval. -/
namespace BPEForest
open MergeTree SpellingBPE
variable {α : Type}

private def extractionShort (s : ℕ) (e : Extraction α) : ℕ :=
  shortCount s e.1 + (e.2.map (shortCount s)).sum

private theorem short_nil (s : ℕ) : shortCount s ([] : Chain α) = 0 := rfl

private theorem close_short (s : ℕ) (e : Extraction α) :
    ((close e).map (shortCount s)).sum=extractionShort s e := by
  rcases e with ⟨xs,rest⟩
  cases xs <;> simp [close,extractionShort,short_nil]

private theorem extend_short (s : ℕ) (a : Attachment α) (e : Extraction α) :
    extractionShort s (extend a e) =
      (shortAhead s a.1 a.2.1 e.1).toNat+extractionShort s e := by
  simp [extractionShort,extend,shortCount_cons,Nat.add_assoc]

private theorem toNat_ite (v : Bool) : v.toNat = if v then 1 else 0 := by cases v <;> rfl

theorem selected_eq_short (s : ℕ) (t : MergeTree α) :
    ((close (extract t)).map (shortCount s)).sum = selectedCount (shortAt s) t := by
  rw [close_short]
  induction t with
  | leaf a => rfl
  | node i l r il ir =>
    cases l with
    | leaf a =>
      cases r with
      | leaf b => rfl
      | node j x y =>
        change extractionShort s (extend (false,i,a) (extract (.node j x y))) =
          0 + selectedCount (shortAt s) (.node j x y) +
            (if shortAhead s false i (extract (.node j x y)).1 then 1 else 0)
        rw [extend_short,ir,toNat_ite]
        rw [Nat.zero_add]
        exact Nat.add_comm ..
    | node j x y =>
      cases r with
      | leaf a =>
        change extractionShort s (extend (true,i,a) (extract (.node j x y))) =
          selectedCount (shortAt s) (.node j x y) + 0 +
            (if shortAhead s true i (extract (.node j x y)).1 then 1 else 0)
        rw [extend_short,il,toNat_ite]
        rw [Nat.add_zero]
        exact Nat.add_comm ..
      | node k z w =>
        change extractionShort s ([], close (extract (.node j x y)) ++ close (extract (.node k z w))) =
          selectedCount (shortAt s) (.node j x y) + selectedCount (shortAt s) (.node k z w) + 0
        change 0+((close (extract (.node j x y)) ++ close (extract (.node k z w))).map
          (shortCount s)).sum = _
        rw [zero_add,List.map_append,List.sum_append,close_short,close_short,il,ir,add_zero]

private theorem costs_add {rules : List (Pair α)} {k : ℕ} (ps : List (Chain α)) (s : ℕ)
    (valid : ∀ p∈ps, ChainValid rules k p) :
    s*(ps.map List.length).sum ≤ s*(ps.map (shortCount s)).sum + (2*s+2*k)*ps.length := by
  induction ps with
  | nil => simp
  | cons c tail ih =>
    have here := chain_cost s (valid c (by simp))
    have rest := ih (fun p hp => valid p (by simp [hp]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_succ]
    omega

theorem tree_unary_cost {rules : List (Pair α)} {k : ℕ} (t : MergeTree α)
    (valid : t.Valid rules k) (s : ℕ) :
    s*t.unary ≤ s*selectedCount (shortAt s) t + 4*s*t.cherries+4*k*t.cherries := by
  have cost := costs_add (close (extract t)) s (fun _ h => extracted_valid valid h)
  rw [selected_eq_short,attachmentCount_close,extract_counts_unary] at cost
  have number := chain_count_bound t
  have bound : (close (extract t)).length ≤ 2*t.cherries := by
    change chainNumber (extract t) ≤ _
    omega
  have prod := Nat.mul_le_mul_left (2*s+2*k) bound
  calc
    _ ≤ _ := cost
    _ ≤ _ := Nat.add_le_add_left prod _
    _ = _ := by ring

theorem forest_unary_cost (rules : List (Pair α)) (trees : List (MergeTree α))
    (valid : ∀ t∈trees, t.Valid rules rules.length) (s : ℕ) :
    s*(trees.map MergeTree.unary).sum ≤ s*(trees.map (selectedCount (shortAt s))).sum +
      4*s*(trees.map MergeTree.cherries).sum + 4*rules.length*(trees.map MergeTree.cherries).sum := by
  induction trees with
  | nil => simp
  | cons t ts ih =>
    have first := tree_unary_cost t (valid t (by simp)) s
    have rest := ih (fun tree ht => valid tree (by simp [ht]))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    omega

#print axioms forest_unary_cost
end BPEForest
