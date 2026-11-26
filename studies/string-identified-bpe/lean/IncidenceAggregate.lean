import Incidence

/-! Aggregate phase incidence into the uniform initial core-score bound. -/
namespace CombIncidenceAggregate
open SpellingBPE SpellingDecoy CombComparator CombIncidence
noncomputable section

theorem list_sum_le_filter {α : Type} (xs : List α) (f : α → Nat) (p : α → Bool)
    (h : ∀ x ∈ xs, f x ≤ if p x then 1 else 0) :
    (xs.map f).sum ≤ (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    cases hp : p x <;> simp [hp] at hx ⊢ <;> omega

def oldOK (i gap : Nat) (right : Bool) (p : Fin 6) : Bool :=
  CombPhases.side p i == right && CombPhases.side p (i+gap) == right &&
    (List.range (gap-1)).all (fun a => CombPhases.side p (i+a+1) != right)

def seedOK (i gap : Nat) (right : Bool) (p : Fin 6) : Bool :=
  CombPhases.side p (i+gap) == right &&
    (List.range (gap-1)).all (fun a => CombPhases.side p (i+a+1) != right)

theorem attached_seedOK {side : Nat → Bool} {seed i j : Nat} {right : Bool}
    (hij : i<j) (h : Attached side seed right i j) :
    side j = right ∧ ∀ a ∈ List.range (j-i-1), side (i+a+1) ≠ right := by
  refine ⟨h.2.2.1, ?_⟩
  intro a ha
  have ha' := List.mem_range.mp ha
  apply h.2.2.2.2
  · omega
  · omega

theorem phaseSum_old (k seed i j : Nat) (right : Bool) (hs : seed<i) (hij : i<j) :
    phaseSum k (orientedPair right i j) seed ≤ CombPhases.count i (j-i) right := by
  unfold phaseSum CombPhases.count
  apply list_sum_le_filter
  intro p _
  by_cases present : orientedPair right i j ∈ candidates (core (CombPhases.side p) seed (k-seed-1))
  · have att := (candidate_oriented_attachment (CombPhases.side p) seed (k-seed-1) hij present).2
    have core := core_gain_le_one (CombPhases.side p) seed (k-seed-1) (orientedPair right i j)
    have sides : CombPhases.side p i = right := att.2.2.2.1 hs
    have rest := attached_seedOK hij att
    have hj : i+(j-i)=j := by omega
    have hok : oldOK i (j-i) right p = true := by
      simp only [oldOK, Bool.and_eq_true, beq_iff_eq, sides, rest.1, hj, true_and,
        List.all_eq_true, bne_iff_ne]
      exact rest.2
    change gain _ _ ≤ if oldOK i (j-i) right p then 1 else 0
    simpa [hok] using core
  · have zero := gain_eq_zero_of_absent present
    simp [zero]

theorem phaseSum_seed (k i j : Nat) (right : Bool) (hij : i<j) :
    phaseSum k (orientedPair right i j) i ≤ CombPhases.firstCount i (j-i) right := by
  unfold phaseSum CombPhases.firstCount
  apply list_sum_le_filter
  intro p _
  by_cases present : orientedPair right i j ∈ candidates (core (CombPhases.side p) i (k-i-1))
  · have att := (candidate_oriented_attachment (CombPhases.side p) i (k-i-1) hij present).2
    have core := core_gain_le_one (CombPhases.side p) i (k-i-1) (orientedPair right i j)
    have rest := attached_seedOK hij att
    have hj : i+(j-i)=j := by omega
    have hok : seedOK i (j-i) right p = true := by
      simp only [seedOK, Bool.and_eq_true, beq_iff_eq, hj, rest.1, true_and,
        List.all_eq_true, bne_iff_ne]
      exact rest.2
    change gain _ _ ≤ if seedOK i (j-i) right p then 1 else 0
    simpa [hok] using core
  · have zero := gain_eq_zero_of_absent present
    simp [zero]

theorem phaseSum_above (k seed i j : Nat) (right : Bool) (hs : i<seed) (hij : i<j) :
    phaseSum k (orientedPair right i j) seed = 0 := by
  have hz : ∀ p : Fin 6, gain (orientedPair right i j)
      (core (CombPhases.side p) seed (k-seed-1)) = 0 := by
    intro p
    apply gain_eq_zero_of_absent
    intro present
    have att := (candidate_oriented_attachment (CombPhases.side p) seed (k-seed-1) hij present).2
    have := att.1
    omega
  simp [phaseSum, hz]

theorem phaseSum_distinct_bound (k seed i j : Nat) (right : Bool) (hij : i<j) :
    phaseSum k (orientedPair right i j) seed ≤ if seed=i then 3 else 1 := by
  by_cases eq : seed=i
  · subst seed
    have h := phaseSum_seed k i j right hij
    have b := (CombPhases.bounded_every_gap i (j-i) right (by omega)).2
    simpa using h.trans b
  · have sne : seed ≠ i := eq
    simp only [sne, ite_false]
    rcases lt_or_gt_of_ne eq with before | after
    · have h := phaseSum_old k seed i j right before hij
      exact h.trans ((CombPhases.bounded_every_gap i (j-i) right (by omega)).1)
    · simp [phaseSum_above k seed i j right after hij]

theorem sum_le_length {α : Type} (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ 1) : (xs.map f).sum ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have rest := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem sum_one_special {α : Type} [DecidableEq α] (xs : List α) (distinct : xs.Nodup)
    (f : α → Nat) (special : α)
    (h : ∀ x ∈ xs, f x ≤ if x=special then 3 else 1) :
    (xs.map f).sum ≤ xs.length+2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp distinct
    by_cases eq : x=special
    · subst x
      have hx := h special (by simp)
      have rest := sum_le_length xs f (by
        intro y hy
        have ne : y ≠ special := by intro e; subst y; exact fresh hy
        simpa [ne] using h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp at hx
      omega
    · have hx := h x (by simp)
      have rest := ih unique (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      simp [eq] at hx
      omega

theorem oriented_value_bound (k L i j : Nat) (right : Bool) (hij : i<j) :
    value (sixCore k L) (orientedPair right i j) ≤ L+2 := by
  rw [sixCore_value]
  have h := sum_one_special (List.range L) List.nodup_range
    (phaseSum k (orientedPair right i j)) i (by
      intro seed _
      exact phaseSum_distinct_bound k seed i j right hij)
  simpa using h

theorem phaseSum_at_most_six (k seed : Nat) (q : Pair Nat) : phaseSum k q seed ≤ 6 := by
  unfold phaseSum
  have h := sum_le_length (List.finRange 6)
    (fun p => gain q (core (CombPhases.side p) seed (k-seed-1)))
    (fun p _ => core_gain_le_one (CombPhases.side p) seed (k-seed-1) q)
  simpa using h

theorem phaseSum_loop_absent (k seed i : Nat) (hne : seed ≠ i) :
    phaseSum k (pair i) seed = 0 := by
  have hz : ∀ p : Fin 6, gain (pair i) (core (CombPhases.side p) seed (k-seed-1)) = 0 := by
    intro p
    apply gain_eq_zero_of_absent
    intro present
    have h := candidate_loop_seed (CombPhases.side p) seed (k-seed-1) (by simpa [pair] using present)
    have same : i=seed := level_injective h
    exact hne same.symm
  simp [phaseSum,hz]

theorem sum_map_zero {α : Type} (xs : List α) (f : α → Nat)
    (h : ∀ x ∈ xs, f x = 0) : (xs.map f).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem sum_one_six {α : Type} [DecidableEq α] (xs : List α) (distinct : xs.Nodup)
    (f : α → Nat) (special : α)
    (h : ∀ x ∈ xs, f x ≤ if x=special then 6 else 0) :
    (xs.map f).sum ≤ 6 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,unique⟩ := List.nodup_cons.mp distinct
    by_cases eq : x=special
    · subst x
      have hx := h special (by simp)
      have rest : (xs.map f).sum = 0 := by
        apply sum_map_zero
        intro y hy
        have hn : y ≠ special := by intro e; subst y; exact fresh hy
        have bound := h y (by simp [hy])
        simp [hn] at bound
        omega
      simp only [List.map_cons, List.sum_cons]
      simp at hx
      omega
    · have hx := h x (by simp)
      have rest := ih unique (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons]
      simp [eq] at hx
      omega

theorem loop_value_bound (k L i : Nat) : value (sixCore k L) (pair i) ≤ 6 := by
  rw [sixCore_value]
  exact sum_one_six (List.range L) List.nodup_range (phaseSum k (pair i)) i (by
    intro seed _
    by_cases h : seed=i
    · simp [h,phaseSum_at_most_six]
    · simp [h,phaseSum_loop_absent k seed i h])

theorem nonlevel_value_zero (k L : Nat) (q : Pair Nat)
    (h : ¬ ∃ a b, q = (level a,level b)) : value (sixCore k L) q = 0 := by
  rw [sixCore_value]
  apply sum_map_zero
  intro seed _
  unfold phaseSum
  apply sum_map_zero
  intro p _
  apply gain_eq_zero_of_absent
  intro present
  obtain ⟨a,b,_,_,eq⟩ := candidate_levels (CombPhases.side p) seed (k-seed-1) present
  exact h ⟨a,b,eq⟩

theorem sixCore_uniform_bound (k L : Nat) (q : Pair Nat) :
    value (sixCore k L) q ≤ max 6 (L+2) := by
  by_cases levels : ∃ a b, q = (level a,level b)
  · obtain ⟨a,b,rfl⟩ := levels
    rcases lt_trichotomy a b with lt | eq | gt
    · have h := oriented_value_bound k L a b true lt
      exact h.trans (le_max_right ..)
    · subst b
      have h := loop_value_bound k L a
      exact h.trans (le_max_left ..)
    · have h := oriented_value_bound k L b a false gt
      exact h.trans (le_max_right ..)
  · rw [nonlevel_value_zero k L q levels]
    exact Nat.zero_le _

end
end CombIncidenceAggregate
