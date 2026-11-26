import Common
import CombComparator
import Mathlib.Algebra.BigOperators.Ring.List

import Mathlib.Tactic.Linarith

/-! A synchronized partial-merge comparator for diamond rows. -/
namespace DiamondComparator
open SpellingBPE Diamond
noncomputable section

def PartialPlay {α : Type} [DecidableEq α] : Word α → List (Pair α) → Word α → Prop
  | w, [], v => w=v
  | w, p::ps, v => ∃ u, Partial p w u ∧ PartialPlay u ps v

theorem partial_id {α : Type} [DecidableEq α] (p : Pair α) (w : Word α) : Partial p w w := by
  induction w with
  | nil => exact .nil
  | cons x xs ih => exact .keep x ih

theorem partial_append {α : Type} [DecidableEq α] {p : Pair α} {w u : Word α}
    (h : Partial p w u) (v : Word α) : Partial p (w++v) (u++v) := by
  induction h with
  | nil => simpa using partial_id p v
  | keep x _ ih => simpa using Partial.keep x ih
  | replace _ ih => simpa using Partial.replace ih

theorem partial_inside {α : Type} [DecidableEq α] (p : Pair α) (left right : Word α) :
    Partial p (left ++ [p.1,p.2] ++ right) (left ++ [p.1++p.2] ++ right) := by
  induction left with
  | nil => simpa using Partial.replace (p:=p) (partial_id p right)
  | cons x xs ih => simpa using Partial.keep x ih

theorem play_append {α : Type} [DecidableEq α] {w u v : Word α} {a b : List (Pair α)}
    (h : PartialPlay w a u) (g : PartialPlay u b v) : PartialPlay w (a++b) v := by
  induction a generalizing w with
  | nil => simpa [PartialPlay] using h ▸ g
  | cons p tail ih =>
    obtain ⟨next, first,rest⟩ := h
    exact ⟨next,first, ih rest⟩

theorem play_skip {α : Type} [DecidableEq α] (w : Word α) (script : List (Pair α)) :
    PartialPlay w script w := by
  induction script with
  | nil => rfl
  | cons p tail ih => exact ⟨w,partial_id p w,ih⟩

theorem wrap_first (m x y start count : Nat) (center : List Nat) :
    wrap m x y start (count+1) center =
      wrap m x y (start+1) count
        (U m start (variant start x y) :: center ++ [V m start (variant start x y)]) := by
  unfold wrap
  rw [List.range_succ_eq_map]
  simp [List.foldl_map, Nat.add_comm, Nat.add_left_comm]

/-- Outer wrapping preserves a contiguous center, with contexts independent
of the center contents. -/
theorem wrap_context (m x y start count : Nat) :
    ∃ left right : List Nat, ∀ center,
      wrap m x y start count center = left ++ center ++ right := by
  induction count generalizing start with
  | zero => exact ⟨[],[],by intro center; simp [wrap]⟩
  | succ n ih =>
    obtain ⟨left,right,h⟩ := ih (start+1)
    refine ⟨left ++ [U m start (variant start x y)],
      V m start (variant start x y) :: right, ?_⟩
    intro center
    rw [wrap_first, h]
    simp [List.append_assoc]

theorem layer_split (m j i : Nat) (hi : i<m) :
    ∃ pre post, layerRules m j = pre ++ [leftRule m j i,rightRule m j i] ++ post := by
  obtain ⟨a,b,hab⟩ := List.append_of_mem (List.mem_range.mpr hi)
  refine ⟨a.flatMap (fun t => [leftRule m j t,rightRule m j t]),
    b.flatMap (fun t => [leftRule m j t,rightRule m j t]), ?_⟩
  unfold layerRules
  rw [hab]
  simp

/-- Two chosen rules act inside an arbitrary context; all other potential
matches are intentionally kept, which is allowed for the partial optimum. -/
theorem selected_pair (m j i : Nat) (hj : j<m) (hi : i<m) (left right : Word Nat) :
    PartialPlay (left ++ [spell (U m j i),spell (hub m j),spell (V m j i)] ++ right)
      [leftRule m j i,rightRule m j i] (left ++ [spell (hub m (j+1))] ++ right) := by
  refine ⟨left ++ [spell (U m j i) ++ spell (hub m j),spell (V m j i)] ++ right, ?_, ?_⟩
  · simpa [leftRule] using partial_inside (leftRule m j i) left
      (spell (V m j i) :: right)
  · refine ⟨left ++ [spell (hub m (j+1))] ++ right, ?_, rfl⟩
    have one := partial_inside (rightRule m j i) left right
    have firstJoin : spell (U m j i) ++ spell (hub m j) = spell (hub m j + U m j i) := by
      rw [spelling_join, Nat.add_comm]
    simpa only [rightRule, Prod.fst, Prod.snd, firstJoin, completion hj hi] using one

def state (m x y j : Nat) : Word Nat :=
  (wrap m x y j (m-j) [hub m j]).map spell

theorem one_layer (m x y j : Nat) (hj : j<m) (hx : x<m) (hy : y<m) :
    PartialPlay (state m x y j) (layerRules m j) (state m x y (j+1)) := by
  have hi : variant j x y < m := by unfold variant; split <;> assumption
  obtain ⟨left,right,context⟩ := wrap_context m x y (j+1) (m-(j+1))
  have hlen : m-j = (m-(j+1))+1 := by omega
  have before : state m x y j = left.map spell ++
      [spell (U m j (variant j x y)),spell (hub m j),spell (V m j (variant j x y))] ++ right.map spell := by
    unfold state
    rw [hlen, wrap_first, context]
    simp
  have after : state m x y (j+1) = left.map spell ++ [spell (hub m (j+1))] ++ right.map spell := by
    unfold state
    rw [context]
    simp
  obtain ⟨pre,post,script⟩ := layer_split m j (variant j x y) hi
  rw [before, after, script]
  have h0 := play_skip (left.map spell ++
      [spell (U m j (variant j x y)),spell (hub m j),spell (V m j (variant j x y))] ++ right.map spell) pre
  have h1 := selected_pair m j (variant j x y) hj hi (left.map spell) (right.map spell)
  have h2 := play_skip (left.map spell ++ [spell (hub m (j+1))] ++ right.map spell) post
  have all := play_append h0 (play_append h1 h2)
  simpa [List.append_assoc] using all

def layers (m start count : Nat) : List (Pair Nat) :=
  (List.range count).flatMap fun a => layerRules m (start+a)

theorem layers_first (m start count : Nat) :
    layers m start (count+1) = layerRules m start ++ layers m (start+1) count := by
  unfold layers
  rw [List.range_succ_eq_map]
  simp [List.flatMap_map, Nat.add_comm, Nat.add_left_comm]

theorem advance (m x y start count : Nat) (hx : x<m) (hy : y<m)
    (valid : start+count ≤ m) :
    PartialPlay (state m x y start) (layers m start count) (state m x y (start+count)) := by
  induction count generalizing start with
  | zero => simp [layers, PartialPlay]
  | succ n ih =>
    rw [layers_first]
    have hfirst := one_layer m x y start (by omega) hx hy
    have hrest := ih (start+1) (by omega)
    have sum : start+1+n = start+(n+1) := by omega
    rw [sum] at hrest
    exact play_append hfirst hrest

theorem seed_run (m s x y : Nat) (hs : s≤m) (hx : x<m) (hy : y<m) :
    PartialPlay (row m s x y) (layers m s (m-s)) [spell (hub m m)] := by
  have run := advance m x y s (m-s) hx hy (by omega)
  have he : s+(m-s)=m := by omega
  rw [he] at run
  simpa [row, rowLengths, state, wrap] using run

theorem layers_add (m start left right : Nat) :
    layers m start (left+right) = layers m start left ++ layers m (start+left) right := by
  induction left generalizing start with
  | zero => simp [layers]
  | succ n ih =>
    rw [show n+1+right = (n+right)+1 by omega, layers_first, layers_first, ih]
    simp [List.append_assoc, Nat.add_comm, Nat.add_left_comm]

theorem comparator_layers (m : Nat) : comparator m = layers m 0 m := by
  simp [comparator, layers]

theorem seed_full_run (m s x y : Nat) (hs : s≤m) (hx : x<m) (hy : y<m) :
    PartialPlay (row m s x y) (comparator m) [spell (hub m m)] := by
  have eq : comparator m = layers m 0 s ++ layers m s (m-s) := by
    rw [comparator_layers]
    have h := layers_add m 0 s (m-s)
    simpa [Nat.add_sub_of_le hs] using h
  rw [eq]
  exact play_append (play_skip _ _) (seed_run m s x y hs hx hy)

theorem partial_cat {α : Type} [DecidableEq α] {p : Pair α}
    {w u x y : Word α} (h : Partial p w u) (g : Partial p x y) :
    Partial p (w++x) (u++y) := by
  induction h with
  | nil => simpa using g
  | keep z _ ih => simpa using Partial.keep z ih
  | replace _ ih => simpa using Partial.replace ih

theorem play_cat {α : Type} [DecidableEq α] {w u x y : Word α} {script : List (Pair α)}
    (h : PartialPlay w script u) (g : PartialPlay x script y) :
    PartialPlay (w++x) script (u++y) := by
  induction script generalizing w x with
  | nil => simp only [PartialPlay] at h g ⊢; subst w; subst x; rfl
  | cons p tail ih =>
    obtain ⟨a,ha,hta⟩ := h
    obtain ⟨b,hb,htb⟩ := g
    exact ⟨a++b,partial_cat ha hb,ih hta htb⟩

theorem wrap_length (m x y start count : Nat) (center : List Nat) :
    (wrap m x y start count center).length = center.length + 2*count := by
  induction count generalizing start center with
  | zero => simp [wrap]
  | succ n ih =>
    rw [wrap_first, ih]
    simp
    omega

theorem row_length (m s x y : Nat) : (row m s x y).length = 1+2*(m-s) := by
  simp [row, rowLengths, wrap_length]

def rows (m : Nat) : List (Word Nat) :=
  (List.range m).flatMap fun s => (List.range m).flatMap fun x =>
    (List.range m).map fun y => row m s x y

theorem every_row_runs (m : Nat) {w : Word Nat} (hw : w ∈ rows m) :
    PartialPlay w (comparator m) [spell (hub m m)] := by
  simp only [rows, List.mem_flatMap, List.mem_map, List.mem_range] at hw
  obtain ⟨s,hs,x,hx,y,hy,rfl⟩ := hw
  exact seed_full_run m s x y (by omega) hx hy

theorem plays_flatten {α : Type} [DecidableEq α] (ws : List (Word α))
    (script : List (Pair α)) (target : Word α)
    (h : ∀ w ∈ ws, PartialPlay w script target) :
    PartialPlay ws.flatten script ((ws.map fun _ => target).flatten) := by
  induction ws with
  | nil => exact play_skip [] script
  | cons w ws ih =>
    simp only [List.flatten_cons, List.map_cons]
    exact play_cat (h w (by simp)) (ih (fun v hv => h v (by simp [hv])))

theorem full_comparator (m : Nat) :
    PartialPlay (rows m).flatten (comparator m)
      (((rows m).map fun _ => [spell (hub m m)]).flatten) :=
  plays_flatten (rows m) (comparator m) [spell (hub m m)] (fun _ h => every_row_runs m h)

theorem rows_length (m : Nat) : (rows m).length = m*m*m := by
  simp [rows, List.length_flatMap]
  ring


theorem row_lengths_fixed (m s x : Nat) :
    (((List.range m).map fun y => (row m s x y).length).sum) = m*(1+2*(m-s)) := by
  simp [row_length]


theorem rows_flatten_length (m : Nat) :
    (rows m).flatten.length = m*m*m + 2*m*m*((List.range m).map fun s => m-s).sum := by
  simp [rows, List.length_flatten, List.map_map, List.flatMap, List.sum_flatten,
    Function.comp_def, row_length, Nat.mul_add, List.sum_map_add, List.sum_map_mul_left]
  ring

theorem core_total_length (m : Nat) :
    (rows m).flatten.length = m*m*m + m*m*m*(m+1) := by
  rw [rows_flatten_length]
  have h := CombComparator.twice_savings_sum (k:=m) (seeds:=m) (by omega)
  have h' : 2 * ((List.range m).map fun s => m-s).sum = m*(m+1) := by
    have eq : 2*m+1-m = m+1 := by omega
    simpa only [eq] using h
  calc
    m*m*m + 2*m*m*((List.range m).map fun s => m-s).sum =
        m*m*m + m*m*(2*((List.range m).map fun s => m-s).sum) := by ring
    _ = m*m*m + m*m*m*(m+1) := by rw [h']; ring

end
end DiamondComparator
