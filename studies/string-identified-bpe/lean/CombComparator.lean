import DecoyRows

/-! The doubling comparator for arbitrary-depth unary comb rows. The side
schedule is entirely unconstrained. -/
namespace CombComparator

open SpellingBPE

def level (j : Nat) : Token Nat := List.replicate (2^j) 0

def pair (j : Nat) : Pair Nat := (level j, level j)

theorem level_ne_of_lt {i j : Nat} (h : i < j) : level j ≠ level i := by
  intro eq
  have lengths : 2^j = 2^i := by simpa [level] using congrArg List.length eq
  exact (Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) h)) lengths.symm

theorem level_double (j : Nat) : level j ++ level j = level (j+1) := by
  unfold level
  rw [← List.replicate_add, Nat.pow_succ, Nat.mul_two]

def put (right : Bool) (tile : Token Nat) (row : Word Nat) : Word Nat :=
  if right then row ++ [tile] else tile :: row

def wrap (side : Nat → Bool) (start : Nat) (center : Word Nat) : Nat → Word Nat
  | 0 => center
  | steps + 1 => wrap side (start+1) (put (side start) (level start) center) steps

def core (side : Nat → Bool) (seed depth : Nat) : Word Nat :=
  wrap side (seed+1) [level seed, level seed] depth

def rules (start : Nat) : Nat → List (Pair Nat)
  | 0 => []
  | steps + 1 => pair start :: rules (start+1) steps

theorem full_avoid_cons (operand fresh : Token Nat) (suffix : Word Nat)
    (avoid : fresh ≠ operand) :
    full (operand, operand) (fresh :: suffix) = fresh :: full (operand, operand) suffix := by
  cases suffix <;> simp [full, Prod.mk.injEq, avoid]

theorem full_avoid_snoc (operand fresh : Token Nat) (initial : Word Nat)
    (avoid : fresh ≠ operand) :
    full (operand, operand) (initial ++ [fresh]) = full (operand, operand) initial ++ [fresh] := by
  induction initial using List.twoStepInduction with
  | nil => rfl
  | singleton x => simp [full, Prod.mk.injEq, avoid]
  | cons_cons x y rest shorter tail =>
    by_cases hit : (x,y) = (operand,operand)
    · simp only [List.cons_append, full, ite_eq_left hit, shorter]
    · simp only [List.cons_append, full, ite_eq_right hit]
      exact congrArg (List.cons x) (tail y)

theorem full_put (operand fresh : Token Nat) (row : Word Nat)
    (side : Bool) (avoid : fresh ≠ operand) :
    full (operand, operand) (put side fresh row) = put side fresh (full (operand, operand) row) := by
  cases side
  · exact full_avoid_cons _ _ _ avoid
  · exact full_avoid_snoc _ _ _ avoid

theorem full_wrap (side : Nat → Bool) {index start : Nat} (lt : index < start)
    (center : Word Nat) (depth : Nat) :
    full (pair index) (wrap side start center depth) =
      wrap side start (full (pair index) center) depth := by
  induction depth generalizing start center with
  | zero => rfl
  | succ n ih =>
    simp only [wrap]
    rw [ih (by omega), pair, full_put _ _ _ _ (level_ne_of_lt lt)]

theorem full_core_early (side : Nat → Bool) {index seed : Nat} (lt : index < seed) (depth : Nat) :
    full (pair index) (core side seed depth) = core side seed depth := by
  unfold core
  rw [full_wrap side (by omega : index < seed+1)]
  have different := level_ne_of_lt lt
  simp [pair, full, different]

theorem full_core_base (side : Nat → Bool) (seed : Nat) :
    full (pair seed) (core side seed 0) = [level (seed+1)] := by
  simp [core, wrap, pair, full, level_double]

theorem full_core_next (side : Nat → Bool) (seed depth : Nat) :
    full (pair seed) (core side seed (depth+1)) = core side (seed+1) depth := by
  unfold core
  rw [full_wrap side (Nat.lt_succ_self seed)]
  simp only [wrap, pair, full, ite_true, level_double]
  have equal : put (side (seed+1)) (level (seed+1)) [level (seed+1)] =
      [level (seed+1), level (seed+1)] := by
    cases side (seed+1) <;> rfl
  rw [equal]

theorem wrap_length (side : Nat → Bool) (start : Nat) (center : Word Nat) (depth : Nat) :
    (wrap side start center depth).length = center.length + depth := by
  induction depth generalizing start center with
  | zero => simp [wrap]
  | succ n ih =>
    simp only [wrap, ih]
    have addOne : (put (side start) (level start) center).length = center.length + 1 := by
      cases side start <;> simp [put]
    omega

theorem core_length (side : Nat → Bool) (seed depth : Nat) :
    (core side seed depth).length = depth+2 := by
  simp [core, wrap_length, Nat.add_comm]

theorem rules_length (start n : Nat) : (rules start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [rules, ih]

theorem rules_add (start left right : Nat) :
    rules start (left+right) = rules start left ++ rules (start+left) right := by
  induction left generalizing start with
  | zero => simp [rules]
  | succ n ih =>
    rw [show n+1+right = n+right+1 by omega]
    simp only [rules, List.cons_append, List.cons.injEq, true_and]
    rw [ih, show start+1+n = start+(n+1) by omega]

theorem play_append (row : Word Nat) (first last : List (Pair Nat)) :
    play row (first ++ last) = play (play row first) last := by
  induction first generalizing row with
  | nil => rfl
  | cons head tail ih =>
    exact ih (full head row)

theorem play_early (side : Nat → Bool) (seed depth start count : Nat) (bound : start+count ≤ seed) :
    play (core side seed depth) (rules start count) = core side seed depth := by
  induction count generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [rules, play]
    rw [full_core_early side (by omega : start < seed)]
    exact ih _ (by omega)

theorem play_from_seed (side : Nat → Bool) (seed depth : Nat) :
    play (core side seed depth) (rules seed (depth+1)) = [level (seed+depth+1)] := by
  induction depth generalizing seed with
  | zero => exact full_core_base side seed
  | succ n ih =>
    rw [show rules seed (n+1+1) = pair seed :: rules (seed+1) (n+1) from rfl,
      play, full_core_next, ih]
    rw [show seed+1+n+1 = seed+(n+1)+1 by omega]

theorem play_after_seed (side : Nat → Bool) (seed depth count : Nat) (within : count ≤ depth) :
    play (core side seed depth) (rules seed count) = core side (seed+count) (depth-count) := by
  induction count generalizing seed depth with
  | zero => simp [rules, play]
  | succ n ih =>
    obtain ⟨d, rfl⟩ : ∃ d, depth = d+1 := ⟨depth-1, by omega⟩
    rw [show rules seed (n+1) = pair seed :: rules (seed+1) n from rfl,
      play, full_core_next, ih _ _ (by omega)]
    congr 1 <;> omega

/-- The level-j rule saves zero before the row's seed and one afterwards. -/
theorem doubling_step (side : Nat → Bool) {seed k j : Nat} (hs : seed < k) (hj : j < k) :
    gain (pair j) (play (core side seed (k-seed-1)) (rules 0 j)) =
      if seed ≤ j then 1 else 0 := by
  by_cases active : seed ≤ j
  · have split : j = seed + (j-seed) := by omega
    have rulesSplit : rules 0 j = rules 0 seed ++ rules seed (j-seed) := by
      have h := rules_add 0 seed (j-seed)
      simpa [← split] using h
    have hdepth : j-seed ≤ k-seed-1 := by omega
    rw [rulesSplit, play_append, play_early side seed _ 0 seed (by omega),
      play_after_seed side seed _ _ hdepth, ← split]
    simp only [ite_eq_left active]
    cases d : k-seed-1-(j-seed) with
    | zero => simp [gain, core_length, full_core_base]
    | succ d => simp [gain, full_core_next, core_length]
  · rw [play_early side seed _ 0 j (by omega)]
    simp [gain, full_core_early side (show j < seed by omega), active]

/-- The doubling rules from level zero to level k−1 leave one level-k token.
The comparator therefore saves exactly one token per step from seed onward. -/
theorem doubling_single_row (side : Nat → Bool) {seed k : Nat} (below : seed < k) :
    play (core side seed (k-seed-1)) (rules 0 k) = [level k] ∧
      (core side seed (k-seed-1)).length -
        (play (core side seed (k-seed-1)) (rules 0 k)).length = k-seed := by
  have split : k = seed + (k-seed-1+1) := by omega
  have result := play_from_seed side seed (k-seed-1)
  have endLevel : seed+(k-seed-1)+1 = k := by omega
  rw [endLevel] at result
  have after : play (core side seed (k-seed-1)) (rules 0 k) = [level k] := by
    conv_lhs => rw [show rules 0 k = rules 0 seed ++ rules seed (k-seed-1+1) by
      have h := rules_add 0 seed (k-seed-1+1)
      simpa [← split] using h]
    rw [play_append, play_early side seed _ 0 seed (by omega)]
    exact result
  refine ⟨after, ?_⟩
  rw [after, core_length]
  simp
  omega

theorem doubling_single_row_feasible (side : Nat → Bool) {seed k : Nat} (below : seed < k) :
    Feasible k (core side seed (k-seed-1)) [level k] := by
  have feasible := plays_feasible (core side seed (k-seed-1)) (rules 0 k)
  rwa [rules_length, (doubling_single_row side below).1] at feasible

open SpellingDecoy

theorem play_length_le (row : Word Nat) (script : List (Pair Nat)) :
    (play row script).length ≤ row.length := by
  induction script generalizing row with
  | nil => rfl
  | cons p tail ih => exact (ih (full p row)).trans (full_nonincrease p row)

theorem utility_single_row (weight : Nat) (row : Word Nat) (script : List (Pair Nat)) :
    utility [(weight,row)] script = weight * (row.length - (play row script).length) := by
  induction script generalizing row with
  | nil => simp [utility, play]
  | cons p tail ih =>
    simp only [utility, value, gain, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      step, play, ih, ← Nat.mul_add]
    have h := full_nonincrease p row
    have ht := play_length_le (full p row) tail
    congr 1
    omega

theorem utility_append_rows (x y : Table Nat) (script : List (Pair Nat)) :
    utility (x ++ y) script = utility x script + utility y script := by
  induction script generalizing x y with
  | nil => simp [utility]
  | cons p tail ih =>
    have expanded : step (x ++ y) p = step x p ++ step y p := by
      simp [step, List.map_append]
    simp only [utility, value_append, expanded, ih]
    omega

theorem utility_of_table (rows : Table Nat) (script : List (Pair Nat)) :
    utility rows script =
      (rows.map fun (weight,row) => weight * (row.length-(play row script).length)).sum := by
  induction rows with
  | nil => induction script <;> simp [utility, value, step, *]
  | cons head tail ih =>
    cases head with
    | mk weight row =>
      change utility ([(weight,row)] ++ tail) script = _
      rw [utility_append_rows, utility_single_row, ih]
      rfl

def coreTable (schedules : List (Nat → Bool)) (k seeds : Nat) : Table Nat :=
  (List.range seeds).flatMap fun s => schedules.map fun side => (1, core side s (k-s-1))

theorem utility_for_one_seed (schedules : List (Nat → Bool)) {seed k : Nat} (below : seed < k) :
    utility (schedules.map fun side => (1,core side seed (k-seed-1))) (rules 0 k) =
      schedules.length * (k-seed) := by
  induction schedules with
  | nil => simp [utility_of_table]
  | cons side tail ih =>
    change utility ([(1,core side seed (k-seed-1))] ++ _) (rules 0 k) = _
    rw [utility_append_rows, utility_single_row, (doubling_single_row side below).2, ih]
    simp [Nat.add_comm, Nat.add_mul]

/-- The exact saving for any list of schedules, including repeated schedules.
The six alternating/RRLL rows per seed are the length-six specialization. -/
theorem doubling_table (schedules : List (Nat → Bool)) {k seeds : Nat} (count : seeds ≤ k) :
    utility (coreTable schedules k seeds) (rules 0 k) =
      schedules.length * ((List.range seeds).map fun s => k-s).sum := by
  induction seeds with
  | zero => simp [coreTable, utility_of_table]
  | succ n ih =>
    have smaller : n ≤ k := by omega
    have active : n < k := by omega
    rw [show coreTable schedules k (n+1) = coreTable schedules k n ++
      (schedules.map fun side => (1,core side n (k-n-1))) by
        simp [coreTable, List.range_succ, List.flatMap_append]]
    rw [utility_append_rows, ih smaller, utility_for_one_seed schedules active]
    simp [List.range_succ, List.map_append, Nat.mul_add]

theorem twice_savings_sum {k seeds : Nat} (bound : seeds ≤ k) :
    2 * ((List.range seeds).map fun s => k-s).sum = seeds * (2*k+1-seeds) := by
  induction seeds with
  | zero => simp
  | succ n ih =>
    have smaller : n ≤ k := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_singleton, Nat.mul_add]
    rw [ih smaller]
    have split : 2*k+1-n = (2*k+1-(n+1))+1 := by omega
    rw [split, Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
    omega

/-- Closed form without truncated division. The six-phase specialization is
twice the utility 6 times seeds times (2*k + 1 - seeds). -/
theorem twice_doubling_table (schedules : List (Nat → Bool)) {k seeds : Nat} (count : seeds ≤ k) :
    2 * utility (coreTable schedules k seeds) (rules 0 k) =
      schedules.length * (seeds * (2*k+1-seeds)) := by
  rw [doubling_table schedules count, Nat.mul_left_comm, twice_savings_sum count]

theorem twice_doubling_augmented_lower (schedules : List (Nat → Bool)) (extras : Table Nat)
    {k seeds : Nat} (count : seeds ≤ k) :
    schedules.length * (seeds * (2*k+1-seeds)) ≤
      2 * utility (coreTable schedules k seeds ++ extras) (rules 0 k) := by
  rw [utility_append_rows, Nat.mul_add, twice_doubling_table schedules count]
  exact Nat.le_add_right ..

#print axioms doubling_single_row
#print axioms doubling_step
#print axioms doubling_single_row_feasible
#print axioms doubling_table
#print axioms twice_doubling_table
#print axioms twice_doubling_augmented_lower

end CombComparator
