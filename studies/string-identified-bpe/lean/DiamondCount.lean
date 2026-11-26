import DistinctRows
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The initial replacement count is at most m over the entire m³-row
table, preserving multiplicities of identical rows. -/
namespace DiamondCount

open Diamond SpellingBPE SpellingDecoy
open scoped BigOperators

abbrev Rows (m : Nat) := Fin m × Fin m × Fin m

def rowAt {m : Nat} (i : Rows m) : Word Nat := row m i.1.val i.2.1.val i.2.2.val

def seedProjection {m : Nat} (s : Nat) (i : Rows m) : Fin m :=
  if s%2=0 then i.2.2 else i.2.1

def EdgeCase.projection {m : Nat} : EdgeCase → Rows m → Fin m
  | .seedL s _ | .seedR s _ => seedProjection s
  | .layerL .. | .layerR .. => Prod.fst

private theorem seed_projection_injective {m s label : Nat} {i j : Rows m}
    (first : i.1.val=s ∧ variant s i.2.1.val i.2.2.val=label)
    (second : j.1.val=s ∧ variant s j.2.1.val j.2.2.val=label)
    (eq : seedProjection s i=seedProjection s j) : i=j := by
  have seed : i.1=j.1 := Fin.ext (first.1.trans second.1.symm)
  have fixed := first.2.trans second.2.symm
  by_cases parity : s%2=0
  · have x : i.2.1=j.2.1 := Fin.ext (by simpa [variant,parity] using fixed)
    have y : i.2.2=j.2.2 := by simpa [seedProjection,parity] using eq
    exact Prod.ext seed (Prod.ext x y)
  · have x : i.2.1=j.2.1 := by simpa [seedProjection,parity] using eq
    have y : i.2.2=j.2.2 := Fin.ext (by simpa [variant,parity] using fixed)
    exact Prod.ext seed (Prod.ext x y)

private theorem layer_projection_injective {m s a b : Nat} {i j : Rows m}
    (first : i.1.val≤s ∧ variant s i.2.1.val i.2.2.val=a ∧
      variant (s+1) i.2.1.val i.2.2.val=b)
    (second : j.1.val≤s ∧ variant s j.2.1.val j.2.2.val=a ∧
      variant (s+1) j.2.1.val j.2.2.val=b)
    (sameSeed : i.1=j.1) : i=j := by
  obtain ⟨x,y⟩ := variant_pair_injective (first.2.1.trans second.2.1.symm)
    (first.2.2.trans second.2.2.symm)
  exact Prod.ext sameSeed (Prod.ext (Fin.ext x) (Fin.ext y))

theorem EdgeCase.projection_injective {m : Nat} (edge : EdgeCase) {i j : Rows m}
    (first : edge.fits i.1.val i.2.1.val i.2.2.val)
    (second : edge.fits j.1.val j.2.1.val j.2.2.val)
    (same : edge.projection i=edge.projection j) : i=j := by
  cases edge
  · exact seed_projection_injective first second same
  · exact seed_projection_injective first second same
  · exact layer_projection_injective first second same
  · exact layer_projection_injective first second same

private theorem value_flatMap {I : Type} (ids : List I) (blocks : I → Table Nat) (q : Pair Nat) :
    value (ids.flatMap blocks) q = (ids.map fun i => value (blocks i) q).sum := by
  induction ids with
  | nil => simp [value]
  | cons i tail ih => simp [List.flatMap_cons, value_append, ih]

private theorem sum_range_fin (m : Nat) (f : Nat → Nat) :
    ((List.range m).map f).sum = ∑ i : Fin m, f i.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Fin.sum_univ_castSucc]
    simpa using congrArg (fun n => n+f m) ih

theorem coreTable_value (m : Nat) (q : Pair Nat) :
    value (coreTable m) q = ∑ i : Rows m, gain q (rowAt i) := by
  unfold coreTable
  simp only [value_flatMap]
  simp only [value, List.map_map, Function.comp_def, one_mul]
  simp only [sum_range_fin, Fintype.sum_prod_type, rowAt]

theorem value_coreTable_le (m : Nat) (q : Pair Nat) : value (coreTable m) q ≤ m := by
  classical
  let good (i : Rows m) := q ∈ candidates (rowAt i)
  let active := Finset.univ.filter good
  have total : value (coreTable m) q ≤ active.card := by
    rw [coreTable_value]
    calc
      _ ≤ ∑ i : Rows m, if good i then 1 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hit : good i
        · rw [ite_eq_left hit]
          change gain q (row m i.1.val i.2.1.val i.2.2.val) ≤ 1
          exact row_gain_le_one i.1.isLt i.2.1.isLt i.2.2.isLt q
        · rw [ite_eq_right hit]
          exact (CombIncidence.gain_eq_zero_of_absent hit).le
      _ = active.card := Finset.sum_boole good _
  apply total.trans
  by_cases live : active.Nonempty
  · obtain ⟨i, hi⟩ := live
    have listed : good i := (Finset.mem_filter.mp hi).2
    obtain ⟨edge, valid, code, _⟩ := candidate_row_case
      i.1.isLt i.2.1.isLt i.2.2.isLt listed
    have fits (j : Rows m) (inside : j ∈ active) : edge.fits j.1.val j.2.1.val j.2.2.val := by
      have occurs : good j := (Finset.mem_filter.mp inside).2
      obtain ⟨data, dataValid, same, fit⟩ := candidate_row_case
        j.1.isLt j.2.1.isLt j.2.2.isLt occurs
      have equality := EdgeCase.pair_injective valid dataValid (code.symm.trans same)
      exact equality.symm ▸ fit
    have injective : (↑active : Set (Rows m)).InjOn edge.projection := by
      intro a ha b hb eq
      exact edge.projection_injective (fits a ha) (fits b hb) eq
    have bound := Finset.card_le_card_of_injOn edge.projection
      (s := active) (t := Finset.univ)
      (fun j _ => Finset.mem_univ (edge.projection j)) injective
    simpa using bound
  · simp [Finset.not_nonempty_iff_eq_empty.mp live]

#print axioms coreTable_value
#print axioms value_coreTable_le

end DiamondCount
