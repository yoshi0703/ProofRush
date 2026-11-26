import ForestTypes
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Lift each actual partial comparator to occurrence trees without identifying
two occurrences merely because their final token spellings agree. -/
namespace BPEForest
open SpellingBPE
variable {α : Type}
abbrev Forest (α : Type) := List (MergeTree α)

namespace MergeTree
theorem valid_mono {rules : List (Pair α)} {i j : ℕ} {t : MergeTree α}
    (h : t.Valid rules i) (le : i ≤ j) : t.Valid rules j := by
  cases t with
  | leaf => trivial
  | node _ _ _ => exact ⟨lt_of_lt_of_le h.1 le,h.2⟩

theorem valid_append {rules : List (Pair α)} (suffix : List (Pair α)) (t : MergeTree α)
    {b : ℕ} (good : t.Valid rules b) : t.Valid (rules ++ suffix) b := by
  induction t generalizing b with
  | leaf => trivial
  | node i l r il ir =>
    obtain ⟨lt,idx,hl,hr⟩ := good
    have small : i < rules.length := List.getElem?_eq_some_iff.mp idx |>.1
    exact ⟨lt,by simpa only [List.getElem?_append_left small] using idx,il hl,ir hr⟩

theorem leaves_length (t : MergeTree α) : t.leaves.length = t.nodes+1 := by
  induction t with
  | leaf a => rfl
  | node _ l r hl hr => simp only [leaves,List.length_append,hl,hr,nodes]; omega
end MergeTree

private theorem partial_lift {p : Pair α} {w v : Word α} (step : Partial p w v)
    (rules : List (Pair α)) (b : ℕ) (idx : rules[b]?=some p)
    (f : Forest α) (current : f.map MergeTree.spell=w) (valid : ∀ t∈f, t.Valid rules b) :
    ∃ g : Forest α, g.map MergeTree.spell=v ∧
      g.flatMap MergeTree.leaves=f.flatMap MergeTree.leaves ∧ ∀ t∈g, t.Valid rules (b+1) := by
  induction step generalizing f with
  | nil =>
    cases f <;> simp_all
  | keep x s ih =>
    cases f with
    | nil => simp at current
    | cons a tail =>
      obtain ⟨hx,rest⟩ := List.cons.inj current
      obtain ⟨g,hg,leaves,vg⟩ := ih tail rest (fun t h => valid t (List.mem_cons_of_mem _ h))
      refine ⟨a::g,by simp [hx,hg],by simp [leaves],?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | mem
      · exact MergeTree.valid_mono (valid t (List.mem_cons_self ..)) (by omega)
      · exact vg t mem
  | replace s ih =>
    cases f with
    | nil => simp at current
    | cons a tail =>
      cases tail with
      | nil => simp at current
      | cons c rest =>
        obtain ⟨ha,restEq⟩ := List.cons.inj current
        obtain ⟨hc,eq⟩ := List.cons.inj restEq
        obtain ⟨g,hg,leaves,vg⟩ := ih rest eq (fun t h => valid t (by simp [h]))
        refine ⟨.node b a c :: g,by simp [MergeTree.spell,ha,hc,hg],?_,?_⟩
        · simp [MergeTree.leaves,leaves,List.append_assoc]
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | mem
          · exact ⟨by omega,by simpa [ha,hc] using idx,valid a (by simp),valid c (by simp)⟩
          · exact vg t mem

private theorem extend_forest {k : ℕ} {w v : Word α} (run : Feasible k w v)
    (rules : List (Pair α)) (f : Forest α) (current : f.map MergeTree.spell=w)
    (valid : ∀ t∈f, t.Valid rules rules.length) :
    ∃ newRules : List (Pair α), newRules.length=rules.length+k ∧
    ∃ g : Forest α, g.map MergeTree.spell=v ∧
      g.flatMap MergeTree.leaves=f.flatMap MergeTree.leaves ∧
      ∀ t∈g, t.Valid newRules newRules.length := by
  induction run generalizing rules f with
  | nil => exact ⟨rules,by simp,f,current,rfl,valid⟩
  | @cons k w u v p step tail ih =>
    let next := rules ++ [p]
    have len : next.length=rules.length+1 := by simp [next]
    have idx : next[rules.length]?=some p := by simp [next]
    obtain ⟨g,hg,gl,gv⟩ := partial_lift step next rules.length idx f current
      (fun t ht => (t.valid_append [p] (valid t ht)))
    obtain ⟨rs,rl,out,ov,ol,good⟩ := ih next g hg (by simpa only [len] using gv)
    exact ⟨rs,by omega,out,ov,ol.trans gl,good⟩

theorem forest_length (f : Forest α) :
    (f.flatMap MergeTree.leaves).length=(f.map MergeTree.nodes).sum+f.length := by
  induction f with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.flatMap_cons,List.length_append,MergeTree.leaves_length,ih,
      List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem comparator_forest {k : ℕ} {w v : Word α} (run : Feasible k w v) :
    ∃ rules : List (Pair α), rules.length=k ∧
    ∃ trees : Forest α, trees.flatMap MergeTree.leaves=w ∧ trees.map MergeTree.spell=v ∧
      (∀ t∈trees, t.Valid rules k) ∧ (trees.map MergeTree.nodes).sum=w.length-v.length := by
  let start : Forest α := w.map MergeTree.leaf
  have spells : start.map MergeTree.spell = w := by simp [start,List.map_map,Function.comp_def,MergeTree.spell]
  have origin : start.flatMap MergeTree.leaves=w := by simp [start,List.flatMap_map,MergeTree.leaves]
  obtain ⟨rules,hr,f,hf,lf,valid⟩ := extend_forest run [] start spells (by
    intro t ht
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
    trivial)
  have size : rules.length=k := by simpa using hr
  have leaves := lf.trans origin
  have nodes := forest_length f
  have outLength := congrArg List.length hf
  simp only [List.length_map] at outLength
  rw [leaves] at nodes
  exact ⟨rules,size,f,leaves,hf,by simpa only [←size] using valid,by omega⟩

#print axioms comparator_forest
end BPEForest
