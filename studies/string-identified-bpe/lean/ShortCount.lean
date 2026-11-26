import BoundedInitial
import FinitePairs
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace BoundedInitial

open SpellingBPE
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
def shortCandidates (M : Nat) : Blocks α → List (Pair α)
  | [] | [_] => []
  | x::y::rest =>
    if x.length+y.length ≤ M then
      (x.flatten,y.flatten) :: shortCandidates M (y::rest)
    else shortCandidates M (y::rest)

omit [DecidableEq α] in
theorem shortCandidates_sublist (M : Nat) (bs : Blocks α) :
    List.Sublist (shortCandidates M bs) (candidates (bs.map List.flatten)) := by
  induction bs using List.twoStepInduction with
  | nil => exact List.Sublist.slnil
  | singleton x => exact List.Sublist.slnil
  | cons_cons x y rest _ ih =>
    simp only [shortCandidates,candidates,List.map_cons]
    split
    · exact List.Sublist.cons_cons _ (ih y)
    · exact List.Sublist.cons _ (ih y)

omit [DecidableEq α] in
theorem shortCandidates_factor (M : Nat) (bs : Blocks α) (q : Pair α)
    (hq : q ∈ shortCandidates M bs) :
    ∃ l r : Blocks α, ∃ x y : Word α, bs = l ++ [x,y] ++ r ∧
      x.length+y.length ≤ M ∧ q = (x.flatten,y.flatten) := by
  induction bs using List.twoStepInduction with
  | nil => simp [shortCandidates] at hq
  | singleton x => simp [shortCandidates] at hq
  | cons_cons x y rest _ ih =>
    simp only [shortCandidates] at hq
    by_cases near : x.length+y.length ≤ M
    · rw [ite_eq_left near] at hq
      rcases List.mem_cons.mp hq with same | next
      · exact ⟨[],rest,x,y,rfl,near,same⟩
      · obtain ⟨l,r,a,b,hl,ha,hb⟩ := ih y next
        exact ⟨x::l,r,a,b,congrArg (List.cons x) hl,ha,hb⟩
    · rw [ite_eq_right near] at hq
      obtain ⟨l,r,a,b,hl,ha,hb⟩ := ih y hq
      exact ⟨x::l,r,a,b,congrArg (List.cons x) hl,ha,hb⟩

omit [DecidableEq α] in
theorem short_long_count (M : Nat) (bs : Blocks α) :
    (shortCandidates M bs).length + longBoundaries M (bs.map List.length) = bs.length - 1 := by
  induction bs using List.twoStepInduction with
  | nil => rfl
  | singleton x => rfl
  | cons_cons x y rest _ ih =>
    specialize ih y
    simp only [List.map_cons,List.length_cons,Nat.add_sub_cancel] at ih
    simp only [shortCandidates,longBoundaries,List.map_cons,List.length_cons,Nat.add_sub_cancel]
    by_cases near : x.length+y.length ≤ M
    · simp [near,not_lt_of_ge near]; omega
    · simp [near,Nat.lt_of_not_ge near]; omega

theorem traceStep_nonempty (p : Pair α) (bs : Blocks α)
    (nonempty : ∀ b ∈ bs, b ≠ []) :
    ∀ b ∈ traceStep p bs, b ≠ [] := by
  intro b hb
  obtain ⟨group, hGroup,rfl⟩ := List.mem_map.mp hb
  obtain ⟨head, tail,rfl⟩ := List.exists_cons_of_ne_nil (groups_nonempty _ _ _ _ hGroup)
  have hhead : head ∈ bs := by
    rw [← groups_flatten List.flatten p bs]
    exact List.mem_flatten.mpr ⟨head::tail, hGroup, by simp⟩
  simp [nonempty head hhead]

theorem traceRun_nonempty (rules : List (Pair α)) (w : Word α) :
    ∀ b ∈ traceRun rules w, b ≠ [] := by
  induction rules using List.reverseRecOn with
  | nil =>
    intro b hb
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
    simp
  | append_singleton ps p ih =>
    have step : traceRun (ps ++ [p]) w = traceStep p (traceRun ps w) := by
      simp [traceRun,List.foldl_append]
    rw [step]
    exact traceStep_nonempty _ _ ih

theorem traceRun_short_mem (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat)
    (w : Word α) (all : ∀ a ∈ w, a ∈ atoms) :
    ∀ q ∈ shortCandidates M (traceRun rules w), q ∈ shortPairs rules atoms M := by
  intro q hq
  obtain ⟨l,r,x,y,factor,hi,pairEq⟩ := shortCandidates_factor _ _ _ hq
  have live := traceRun_nonempty rules w
  rw [factor] at live
  have hx := List.length_pos_of_ne_nil (live x (by simp))
  have hy := List.length_pos_of_ne_nil (live y (by simp))
  rw [pairEq]
  exact pair_mem_shortPairs _ _ _ _ _ _ _ _ all factor (by omega) hi

section Counting
variable {β : Type} [DecidableEq β]

private theorem covered_count (xs cover : List β) (bound : Nat)
    (covered : ∀ q ∈ xs, q ∈ cover)
    (counts : ∀ q, xs.count q ≤ bound) : xs.length ≤ cover.length * bound := by
  have len := (List.nodup_dedup xs).length_le_of_subset
    (show xs.dedup ⊆ cover by
      intro b hb
      exact covered b (List.mem_dedup.mp hb))
  have total : (xs.dedup.map xs.count).sum = xs.length := by
    simpa using List.sum_map_count_dedup_filter_eq_countP (fun _ : β => true) xs
  have sumBound := List.sum_le_length_nsmul (xs.dedup.map xs.count) bound (by
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact counts q)
  rw [total,List.length_map,nsmul_eq_mul] at sumBound
  exact sumBound.trans (Nat.mul_le_mul_right _ len)

end Counting

theorem short_count (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat)
    (w : Word α) (all : ∀ a ∈ w, a ∈ atoms) (B : Nat)
    (rawBound : ∀ q, rawCount q (play w rules) ≤ B) :
    (shortCandidates M (traceRun rules w)).length ≤ shortTypeBound atoms.length M * B := by
  have present := traceRun_short_mem rules atoms M w all
  have inclus := shortCandidates_sublist M (traceRun rules w)
  rw [traceRun_visible] at inclus
  have agree (a b : Pair α) : @BEq.beq _ instBEqOfDecidableEq a b = (a == b) := by
    by_cases eq : a = b <;> simp [eq]
  have shortBound (q : Pair α) :
      @List.count _ instBEqOfDecidableEq q (shortCandidates M (traceRun rules w)) ≤ B := by
    have cnt := (inclus.count_le q).trans (rawBound q)
    simpa only [List.count_eq_length_filter,agree] using cnt
  exact (covered_count _ _ B present shortBound).trans
    (Nat.mul_le_mul_right B (shortPairs_length ..))

#print axioms traceRun_short_mem
#print axioms short_count

end BoundedInitial
