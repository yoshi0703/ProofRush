import DecoyRows
import Mathlib.Data.List.Count

/-! A weighted token table can be simulated in one word, with a distinct
ordinary new character after each copy of a row. The terminal delimiter is
also unique. Every rule that involves a delimiter has at most one replacement. -/
namespace SpellingSeparators
open SpellingBPE SpellingDecoy
variable {α : Type}

def embed (t : Token α) : Token (α ⊕ ℕ) := t.map Sum.inl

def liftWord (w : Word α) : Word (α ⊕ ℕ) := w.map embed

def liftPair (p : Pair α) : Pair (α ⊕ ℕ) := (embed p.1,embed p.2)

def marker (n : ℕ) : Token (α ⊕ ℕ) := [.inr n]

theorem embed_inj : Function.Injective (embed (α := α)) :=
  List.map_injective_iff.2 (fun _ _ h => Sum.inl.inj h)

@[simp] theorem embed_eq {a b : Token α} : embed a = embed b ↔ a = b := embed_inj.eq_iff
@[simp] theorem embed_mark (t : Token α) (n : ℕ) : embed t ≠ marker n := by
  cases t <;> simp [embed,marker]
@[simp] theorem mark_embed (t : Token α) (n : ℕ) : marker n ≠ embed t := Ne.symm (embed_mark t n)
@[simp] theorem embed_append (a b : Token α) : embed (a++b) = embed a ++ embed b := List.map_append
@[simp] theorem mark_eq {i j : ℕ} : marker (α := α) i = marker j ↔ i = j := by simp [marker]
@[simp] theorem pair_eq (a b : Token α) (p : Pair α) :
    (embed a,embed b) = liftPair p ↔ (a,b) = p := by
  rcases p with ⟨x,y⟩
  simp [liftPair,Prod.mk.injEq]

variable [DecidableEq α]

theorem push_marker (p : Pair α) (n : ℕ) (tail : Word (α ⊕ ℕ)) :
    full (liftPair p) (marker n :: tail) = marker n :: full (liftPair p) tail := by
  cases tail <;> simp [full,liftPair,Prod.mk.injEq]

theorem push_row (p : Pair α) (w : Word α) (n : ℕ) (tail : Word (α ⊕ ℕ)) :
    full (liftPair p) (liftWord w ++ marker n :: tail) =
      liftWord (full p w) ++ marker n :: full (liftPair p) tail := by
  induction w using List.twoStepInduction with
  | nil => simpa [liftWord,full] using push_marker p n tail
  | singleton x =>
    change full (liftPair p) (embed x :: marker n :: tail) = embed x :: marker n :: full _ tail
    have ne : (embed x,marker n) ≠ liftPair p := by simp [liftPair,Prod.mk.injEq]
    rw [full,ite_eq_right ne,push_marker]
  | cons_cons x y xs two one =>
    by_cases h : (x,y)=p
    · subst p
      simpa [liftWord,full] using congrArg (List.cons (embed (x++y))) two
    · simpa [liftWord,full,h] using congrArg (List.cons (embed x)) (one y)

def blocks (start : ℕ) : List (Word α) → Word (α ⊕ ℕ)
  | [] => []
  | w::ws => liftWord w ++ marker start :: blocks (start+1) ws

theorem full_blocks (p : Pair α) (ws : List (Word α)) (start : ℕ) :
    full (liftPair p) (blocks start ws) = blocks start (ws.map (full p)) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp only [blocks, List.map_cons, push_row, ih]

def weightedRows : Table α → List (Word α)
  | [] => []
  | (n,w)::rs => List.replicate n w ++ weightedRows rs

def single (w : Table α) : Word (α ⊕ ℕ) := blocks 0 (weightedRows w)

theorem row_step (t : Table α) (p : Pair α) :
    weightedRows (step t p) = (weightedRows t).map (full p) := by
  induction t with
  | nil => rfl
  | cons row t ih =>
    rcases row with ⟨n,w⟩
    simp [weightedRows,step,List.map_replicate] at ih ⊢
    exact ih

theorem full_single (t : Table α) (p : Pair α) :
    full (liftPair p) (single t) = single (step t p) := by
  rw [single,full_blocks,single,row_step]

theorem gain_blocks (p : Pair α) (ws : List (Word α)) (start : ℕ) :
    gain (liftPair p) (blocks start ws) = (ws.map (gain p)).sum := by
  induction ws generalizing start with
  | nil => simp [blocks,gain,full]
  | cons w ws ih =>
    have tail := ih (start+1)
    have a := full_nonincrease p w
    have b := full_nonincrease (liftPair p) (blocks (start+1) ws)
    change (liftWord w ++ marker start :: blocks (start+1) ws).length -
      (full (liftPair p) (liftWord w ++ marker start :: blocks (start+1) ws)).length = _
    rw [push_row]
    simp only [gain,liftWord,List.length_append,List.length_map,List.length_cons,
      List.map_cons,List.sum_cons] at tail ⊢
    omega

theorem weighted_value (t : Table α) (p : Pair α) :
    ((weightedRows t).map (gain p)).sum = value t p := by
  induction t with
  | nil => rfl
  | cons row t ih =>
    rcases row with ⟨n,w⟩
    simp [weightedRows,value] at ih ⊢
    exact ih

theorem gain_single (t : Table α) (p : Pair α) :
    gain (liftPair p) (single t) = value t p := (gain_blocks ..).trans (weighted_value t p)

theorem operand_counts [BEq α] [LawfulBEq α] (p : Pair α) (w : Word α) :
    gain p w ≤ w.count p.1 ∧ gain p w ≤ w.count p.2 := by
  induction w using List.twoStepInduction with
  | nil => simp [gain,full]
  | singleton x => simp [gain,full]
  | cons_cons x y xs two one =>
    by_cases hit : (x,y) = p
    · subst p
      have le := full_nonincrease (x,y) xs
      simp only [gain] at two
      simp only [gain,full,↓reduceIte,List.length_cons,List.count_cons,
        beq_self_eq_true] at *
      split_ifs <;> omega
    · have eq : gain p (x::y::xs) = gain p (y::xs) := by
        change ((y::xs).length+1) - (full p (x::y::xs)).length = _
        rw [full,ite_eq_right hit]
        simp [gain]
      rw [eq]
      have extend (a : Token α) : (y::xs).count a ≤ (x::y::xs).count a := by
        conv_rhs => rw [List.count_cons]
        exact Nat.le_add_right ..
      exact ⟨(one y).1.trans (extend _),(one y).2.trans (extend _)⟩

omit [DecidableEq α] in
theorem marker_absent (ws : List (Word α)) {j start : ℕ} (before : j < start) :
    marker j ∉ blocks start ws := by
  induction ws generalizing start with
  | nil => simp [blocks]
  | cons w ws ih =>
    have ne : j ≠ start := Nat.ne_of_lt before
    have tail := ih (show j < start+1 by omega)
    simp [blocks,liftWord,ne,tail]

theorem foreign_count (ws : List (Word α)) (start : ℕ) (t : Token (α ⊕ ℕ))
    (foreign : ∀ x, embed x ≠ t) : (blocks start ws).count t ≤ 1 := by
  induction ws generalizing start with
  | nil => simp [blocks]
  | cons w ws ih =>
    have no : t ∉ liftWord w := by simpa [liftWord,List.mem_map] using
      (show ¬ ∃ a ∈ w, embed a = t from fun ⟨a,_,h⟩ => foreign a h)
    rw [blocks,List.count_append,List.count_eq_zero.mpr no,Nat.zero_add]
    by_cases e : t = marker start
    · subst t
      have tail := marker_absent ws (Nat.lt_succ_self start)
      simp [List.count_eq_zero.mpr tail]
    · simpa [List.count_cons,Ne.symm e] using ih (start+1)

theorem high_is_lift (t : Table α) (q : Pair (α ⊕ ℕ)) (high : 1 < gain q (single t)) :
    ∃ p : Pair α, q = liftPair p := by
  have bounds := operand_counts q (single t)
  have left : ∃ x, embed x = q.1 := by
    by_contra! no
    have small := foreign_count (weightedRows t) 0 q.1 no
    change (single t).count q.1 ≤ 1 at small
    exact (Nat.not_lt_of_ge (bounds.1.trans small)) high
  have right : ∃ x, embed x = q.2 := by
    by_contra! no
    have small := foreign_count (weightedRows t) 0 q.2 no
    change (single t).count q.2 ≤ 1 at small
    exact (Nat.not_lt_of_ge (bounds.2.trans small)) high
  obtain ⟨x,hx⟩ := left
  obtain ⟨y,hy⟩ := right
  exact ⟨(x,y),Prod.ext hx.symm hy.symm⟩

end SpellingSeparators
