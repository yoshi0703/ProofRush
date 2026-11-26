import SpellingBPE
import Mathlib.Data.Finset.Card

/-! A forcing construction for a weighted BPE corpus. Each additional rule
has its own two-token row. When its weight exceeds every pair count in the
core and its pair never occurs there, every possible tie resolution consumes
one previously unused added row per step. -/
namespace SpellingDecoy
open SpellingBPE
variable {α : Type} [DecidableEq α]

abbrev Table (α : Type) := List (ℕ × Word α)

def step (w : Table α) (p : Pair α) : Table α := w.map (fun row => (row.1, full p row.2))

def value (w : Table α) (p : Pair α) : ℕ := (w.map (fun row => row.1 * gain p row.2)).sum

def extra (m : ℕ) (p : Pair α) (spent : List (Pair α)) : ℕ × Word α :=
  (m, if p ∈ spent then [p.1++p.2] else [p.1,p.2])

def augmented (core : Table α) (m : ℕ) (ps spent : List (Pair α)) : Table α :=
  core ++ ps.map (fun p => extra m p spent)

def legal (w : Table α) : List (Pair α) → Prop
  | [] => True
  | p::ps => (∀ q : Pair α, value w q ≤ value w p) ∧ 0 < value w p ∧ legal (step w p) ps

def utility (w : Table α) : List (Pair α) → ℕ
  | [] => 0
  | p::ps => value w p + utility (step w p) ps

theorem value_append (x y : Table α) (p : Pair α) :
    value (x++y) p = value x p + value y p := by
  simp [value,List.map_append]

theorem extra_score (p q : Pair α) (m : ℕ) (spent : List (Pair α)) :
    (extra m q spent).1 * gain p (extra m q spent).2 = if p=q ∧ q ∉ spent then m else 0 := by
  rcases q with ⟨l,r⟩
  by_cases eq : (l,r) = p
  · subst p
    by_cases mem : (l,r) ∈ spent <;> simp [extra,mem,gain,full]
  · by_cases mem : (l,r) ∈ spent <;> simp [extra,mem,gain,full,eq,Ne.symm eq]

theorem extras_score (p : Pair α) (m : ℕ) (ps spent : List (Pair α)) (distinct : ps.Nodup) :
    value (ps.map (fun q => extra m q spent)) p = if p∈ps ∧ p∉spent then m else 0 := by
  induction ps with
  | nil => simp [value]
  | cons q qs ih =>
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp distinct
    change (extra m q spent).1 * gain p (extra m q spent).2 +
      value (qs.map (fun t => extra m t spent)) p = _
    rw [extra_score, ih unique]
    by_cases eq : p=q
    · subst p
      simp [fresh]
    · simp [eq]

theorem core_fixed {core : Table α} {p : Pair α} (absent : ∀ row ∈ core, p ∉ candidates row.2) :
    step core p = core ∧ value core p = 0 := by
  induction core with
  | nil => simp [step,value]
  | cons row rs ih =>
    have eq := no_occurrence row.2 (absent row (by simp))
    obtain ⟨st,sc⟩ := ih (fun y hy => absent y (List.mem_cons_of_mem _ hy))
    change (row.1, full p row.2)::step rs p = row::rs ∧ row.1*gain p row.2 + value rs p = 0
    simp [eq,st,sc,gain]

theorem step_extra (p q : Pair α) (spent : List (Pair α)) (m : ℕ) :
    ((extra m q spent).1, full p (extra m q spent).2) = extra m q (p::spent) := by
  rcases q with ⟨l,r⟩
  by_cases eq : (l,r)=p
  · subst p
    by_cases mem : (l,r) ∈ spent <;> simp [extra,mem,full]
  · by_cases mem : (l,r) ∈ spent <;> simp [extra,mem,full,eq]

theorem step_augmented (core : Table α) (m : ℕ) (ps spent : List (Pair α)) (p : Pair α)
    (absent : ∀ row ∈ core, p ∉ candidates row.2) :
    step (augmented core m ps spent) p = augmented core m ps (p::spent) := by
  have h := (core_fixed absent).1
  change (core ++ _).map _ = _
  rw [List.map_append]
  change step core p ++ _ = _
  rw [h]
  simp only [augmented,List.map_map]
  congr 1
  exact List.map_congr_left (fun q _ => step_extra p q spent m)

theorem has_unused {ps used : List (Pair α)} (unique : ps.Nodup) (room : used.length < ps.length) :
    ∃ q ∈ ps, q ∉ used := by
  by_contra! h
  have sub : ps.toFinset ⊆ used.toFinset := by
    intro q hq
    exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))
  have bound := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup unique] at bound
  have other := List.toFinset_card_le (l := used)
  omega

/-- Exact utility against every tie order for any positive prefix of the
forcing construction. The core may be any finite weighted corpus. -/
theorem force (core : Table α) (m : ℕ) (ps : List (Pair α)) (unique : ps.Nodup)
    (bounded : ∀ q : Pair α, value core q < m)
    (isolated : ∀ q ∈ ps, ∀ row ∈ core, q ∉ candidates row.2)
    (used choices : List (Pair α)) (room : used.length + choices.length ≤ ps.length)
    (ok : legal (augmented core m ps used) choices) :
    utility (augmented core m ps used) choices = choices.length*m := by
  induction choices generalizing used with
  | nil => simp [utility]
  | cons p tail ih =>
    have rem : used.length < ps.length := by simp only [List.length_cons] at room; omega
    obtain ⟨q,hq,unused⟩ := has_unused unique rem
    have eval (x : Pair α) : value (augmented core m ps used) x =
        value core x + (if x∈ps ∧ x∉used then m else 0) := by
      rw [augmented, value_append, extras_score _ _ _ _ unique]
    have big := ok.1 q
    rw [eval q, ite_eq_left ⟨hq,unused⟩, (core_fixed (isolated q hq)).2, Nat.zero_add] at big
    have selected : p∈ps ∧ p∉used := by
      by_contra h
      rw [eval p, ite_eq_right h, Nat.add_zero] at big
      exact (Nat.not_lt_of_ge big) (bounded p)
    have dst := step_augmented core m ps used p (isolated p selected.1)
    have rest := ok.2.2
    rw [dst] at rest
    have room' : (p::used).length + tail.length ≤ ps.length := by
      simp only [List.length_cons] at room ⊢
      omega
    have restUtility := ih (p::used) room' rest
    simp only [utility, dst, restUtility, List.length_cons, Nat.add_mul, Nat.one_mul, eval,
      ite_eq_left selected, (core_fixed (isolated p selected.1)).2]
    omega

theorem pick_list (core : Table α) (m : ℕ) (ps : List (Pair α)) (unique : ps.Nodup)
    (bounded : ∀ q : Pair α, value core q < m)
    (isolated : ∀ q ∈ ps, ∀ row ∈ core, q ∉ candidates row.2)
    (used choices : List (Pair α)) (free : ∀ q ∈ choices, q ∈ ps ∧ q ∉ used)
    (distinct : choices.Nodup) : legal (augmented core m ps used) choices := by
  induction choices generalizing used with
  | nil => trivial
  | cons p tail ih =>
    obtain ⟨mem,fresh⟩ := free p (by simp)
    have ev (q : Pair α) : value (augmented core m ps used) q =
        value core q + (if q∈ps ∧ q∉used then m else 0) := by
      rw [augmented, value_append, extras_score _ _ _ _ unique]
    have chosen : value (augmented core m ps used) p = m := by
      rw [ev, ite_eq_left ⟨mem,fresh⟩, (core_fixed (isolated p mem)).2, Nat.zero_add]
    refine ⟨?_, ?_, ?_⟩
    · intro q
      rw [chosen,ev]
      by_cases live : q∈ps ∧ q∉used
      · rw [ite_eq_left live,(core_fixed (isolated q live.1)).2,Nat.zero_add]
      · rw [ite_eq_right live,Nat.add_zero]
        exact (bounded q).le
    · rw [chosen]
      exact Nat.lt_of_le_of_lt (Nat.zero_le _) (bounded p)
    · rw [step_augmented core m ps used p (isolated p mem)]
      apply ih _ _ (List.nodup_cons.mp distinct).2
      intro q hq
      obtain ⟨inP,nused⟩ := free q (List.mem_cons_of_mem _ hq)
      refine ⟨inP,?_⟩
      have ne : q ≠ p := fun eq => (List.nodup_cons.mp distinct).1 (eq ▸ hq)
      simp [ne,nused]

theorem utility_append (xs ys : Table α) (choices : List (Pair α)) :
    utility (xs++ys) choices = utility xs choices + utility ys choices := by
  induction choices generalizing xs ys with
  | nil => rfl
  | cons p ps ih =>
    have st : step (xs++ys) p = step xs p ++ step ys p := List.map_append
    simp only [utility, value_append, st, ih]
    omega

def uniform (n : ℕ) (rows : List (Word α)) : Table α := rows.map (fun w => (n,w))

theorem uniform_value (n : ℕ) (rows : List (Word α)) (p : Pair α) :
    value (uniform n rows) p = n * value (uniform 1 rows) p := by
  induction rows with
  | nil => simp [value,uniform]
  | cons w ws ih =>
    change n * gain p w + value (uniform n ws) p = n * (1 * gain p w + value (uniform 1 ws) p)
    rw [ih,Nat.one_mul,Nat.mul_add]

theorem step_uniform (n : ℕ) (rows : List (Word α)) (p : Pair α) :
    step (uniform n rows) p = uniform n (rows.map (full p)) := by
  simp [step,uniform,List.map_map]

theorem uniform_utility (n : ℕ) (rows : List (Word α)) (ps : List (Pair α)) :
    utility (uniform n rows) ps = n * utility (uniform 1 rows) ps := by
  induction ps generalizing rows with
  | nil => simp [utility]
  | cons p ps ih =>
    simp only [utility,step_uniform,uniform_value n, ih, Nat.mul_add]

#print axioms force

end SpellingDecoy
