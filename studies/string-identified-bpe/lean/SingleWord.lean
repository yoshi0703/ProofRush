import ShortCount

namespace BoundedInitial
open SpellingBPE
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem blockExcess_add_length (bs : Blocks α) (live : ∀ b ∈ bs, b ≠ []) :
    blockExcess (bs.map List.length) + bs.length = bs.flatten.length := by
  induction bs with
  | nil => rfl
  | cons x rest ih =>
    have hx := List.length_pos_of_ne_nil (live x (by simp))
    have inductionHyp := ih (fun x hx => live x (by simp [hx]))
    simp [blockExcess] at inductionHyp ⊢
    omega

theorem trace_balance (rules : List (Pair α)) (w : Word α) :
    blockExcess ((traceRun rules w).map List.length) + (play w rules).length = w.length := by
  have h := blockExcess_add_length _ (traceRun_nonempty rules w)
  have len := congrArg List.length (traceRun_visible rules w)
  simp only [traceRun_flatten] at h
  rw [List.length_map] at len
  omega

theorem play_nonempty (rules : List (Pair α)) (w : Word α) (positive : 0 < w.length) :
    0 < (play w rules).length := by
  have len := congrArg List.length (traceRun_visible rules w)
  rw [List.length_map] at len
  rw [← len]
  apply List.length_pos_of_ne_nil
  intro zero
  have h := traceRun_flatten rules w
  rw [zero] at h
  subst w
  exact Nat.not_lt_zero _ positive

/-- The per-state inequality, with an explicit catalogue of initial atom labels. -/
theorem state_bound (rules : List (Pair α)) (atoms : List (Token α)) (M : Nat)
    (w : Word α) (all : ∀ a ∈ w, a ∈ atoms) (B : Nat)
    (rawBound : ∀ q, rawCount q (play w rules) ≤ B) :
    (M-1)*(w.length-1) ≤ (M+1)*(w.length-(play w rules).length) +
      shortTypeBound atoms.length M * (M-1) * B := by
  by_cases threshold : 0 < M
  swap
  · have zero : M = 0 := by omega
    simp [zero]
  let blocks := traceRun rules w
  let current := play w rules
  let n := shortTypeBound atoms.length M
  have len : blocks.length = current.length := by
    have h := congrArg List.length (traceRun_visible rules w)
    simpa only [List.length_map] using h
  have balance := trace_balance rules w
  change blockExcess (blocks.map List.length) + current.length = w.length at balance
  have saving : blockExcess (blocks.map List.length) = w.length - current.length := by omega
  have span : (current.length-1) + (w.length-current.length) = w.length-1 := by
    by_cases positive : 0 < w.length
    · have live := play_nonempty rules w positive
      change 0 < current.length at live
      omega
    · omega
  have split := short_long_count M blocks
  rw [len] at split
  have cap : (shortCandidates M blocks).length ≤ n * B := short_count rules atoms M w all B rawBound
  have charge := long_charge_total M (blocks.map List.length)
  rw [saving] at charge
  have sum := Nat.add_le_add (Nat.mul_le_mul_left (M-1) cap) charge
  rw [← Nat.mul_add, split] at sum
  change (M-1)*(w.length-1) ≤ (M+1)*(w.length-current.length) + n*(M-1)*B
  have telescopic : (M-1)*(w.length-1) =
      (M-1)*(current.length-1) + (M-1)*(w.length-current.length) := by
    rw [← Nat.mul_add,span]
  rw [telescopic]
  have coeff : M-1+2 ≤ M+1 := by omega
  calc
    _ ≤ (M-1)*(n*B) + 2*(w.length-current.length) +
        (M-1)*(w.length-current.length) := Nat.add_le_add_right sum _
    _ = (M-1+2)*(w.length-current.length) + n*(M-1)*B := by ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ coeff) _

/-- The flag selects raw adjacency ranking if true, and replacement ranking
otherwise. Zero-gain steps are admissible when every pair has zero count. -/
def chooses (raw : Bool) (w : Word α) (p : Pair α) : Prop :=
  if raw then ∀ q, rawCount q w ≤ rawCount p w else ∀ q, gain q w ≤ gain p w

theorem rawBound_of_choice {raw : Bool} {w : Word α} {p : Pair α}
    (choose : chooses raw w p) (q : Pair α) : rawCount q w ≤ 2 * gain p w := by
  cases raw
  · exact (raw_le_twice_gain q w).trans (Nat.mul_le_mul_left _ (choose q))
  · exact (choose q).trans (raw_le_twice_gain p w)

inductive CountedRun (raw : Bool) : Word α → List (Pair α) → Word α → Prop
  | nil (w : Word α) : CountedRun raw w [] w
  | next {w v : Word α} {p : Pair α} {tail : List (Pair α)} :
    chooses raw w p → CountedRun raw (full p w) tail v → CountedRun raw w (p::tail) v

theorem run_visible {raw : Bool} {w v : Word α} {rules : List (Pair α)}
    (h : CountedRun raw w rules v) : play w rules = v := by
  induction h with
  | nil => rfl
  | next _ _ ih => exact ih

theorem run_nonincrease {raw : Bool} {w v : Word α} {rules : List (Pair α)}
    (h : CountedRun raw w rules v) : v.length ≤ w.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | next _ _ ih => exact ih.trans (full_nonincrease ..)

theorem append_play (h : List (Pair α)) (p : Pair α) (w : Word α) :
    play w (h ++ [p]) = full p (play w h) := by
  induction h generalizing w with
  | nil => rfl
  | cons q tail ih => exact ih (full q w)

theorem counted_bound_from {raw : Bool} {z v : Word α} {rules : List (Pair α)}
    (h : CountedRun raw z rules v) (w : Word α) (atoms : List (Token α)) (M : Nat)
    (all : ∀ a ∈ w, a ∈ atoms) (history : List (Pair α)) (hz : z = play w history) :
    rules.length*(M-1)*(w.length-1) ≤
      rules.length*(M+1)*(w.length-v.length) +
        2*shortTypeBound atoms.length M*(M-1)*(z.length-v.length) := by
  let n := shortTypeBound atoms.length M
  induction h generalizing history with
  | nil => simp
  | @next current final p tail choose continuation ih =>
    have stepBound := state_bound history atoms M w all (2*gain p current)
      (fun q => hz ▸ (rawBound_of_choice choose q))
    rw [← hz] at stepBound
    have nextLength := full_nonincrease p current
    have endLength := run_nonincrease continuation
    have order : w.length-current.length ≤ w.length-final.length := by omega
    have stepBound' := stepBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ order) _)
    have nextEq : full p current = play w (history++[p]) := by rw [append_play, hz]
    have tailBound := ih (history++[p]) nextEq
    have gains : gain p current + ((full p current).length-final.length) =
        current.length-final.length := by unfold gain; omega
    calc
      _ = tail.length*(M-1)*(w.length-1) + (M-1)*(w.length-1) := by simp; ring
      _ ≤ tail.length*(M+1)*(w.length-final.length) +
          2*n*(M-1)*((full p current).length-final.length) +
          ((M+1)*(w.length-final.length) + n*(M-1)*(2*gain p current)) :=
            Nat.add_le_add tailBound stepBound'
      _ = (p::tail).length*(M+1)*(w.length-final.length) +
          2*n*(M-1)*(gain p current + ((full p current).length-final.length)) := by
            simp; ring
      _ = _ := by rw [gains]

/-- Finite fixed-initial-type bound for either ranking, in the original
literal-spelling single-word semantics, with the boundary potential in
place of the weaker partial-comparator optimum. -/
theorem bounded_initial_word {raw : Bool} {w v : Word α} {rules : List (Pair α)}
    (h : CountedRun raw w rules v) (atoms : List (Token α)) (M : Nat)
    (all : ∀ a ∈ w, a ∈ atoms) :
    rules.length * (M-1) * (w.length-1) ≤
      (rules.length*(M+1)+2*shortTypeBound atoms.length M*(M-1))*(w.length-v.length) := by
  have bound := counted_bound_from h w atoms M all [] rfl
  rw [Nat.add_mul]
  exact bound

omit [DecidableEq α] in
theorem partial_nonempty {w v : Word α} {p : Pair α}
    (step : Partial p w v) (nonempty : w ≠ []) : v ≠ [] := by
  cases step <;> simp_all

omit [DecidableEq α] in
theorem feasible_nonempty {k : Nat} {w v : Word α}
    (h : Feasible k w v) (nonempty : w ≠ []) : v ≠ [] := by
  induction h with
  | nil => exact nonempty
  | cons step _ ih => exact ih (partial_nonempty step nonempty)

omit [DecidableEq α] in
theorem optimum_le_boundaries (w : Word α) (k : Nat) :
    optimum w k ≤ w.length - 1 := by
  obtain ⟨j,_,v,h,gain⟩ := optimum_attained w k
  rw [← gain]
  by_cases live : w = []
  · simp [live]
  · have pos := List.length_pos_of_ne_nil (feasible_nonempty h live)
    omega

theorem bounded_initial_budget {raw : Bool} {w v : Word α} {rules : List (Pair α)}
    (h : CountedRun raw w rules v) (atoms : List (Token α)) (M k : Nat)
    (all : ∀ a ∈ w, a ∈ atoms)
    (finished : rules.length = k ∨ v.length ≤ 1) :
    k * (M-1) * optimum w k ≤
      (k*(M+1)+2*shortTypeBound atoms.length M*(M-1))*(w.length-v.length) := by
  have legalOpt := Nat.mul_le_mul_left (k*(M-1)) (optimum_le_boundaries w k)
  apply legalOpt.trans
  rcases finished with used | exhausted
  · rw [← used]
    exact bounded_initial_word h atoms M all
  · have b : w.length-1 ≤ w.length-v.length := by omega
    have c : k*(M-1) ≤ k*(M+1)+2*shortTypeBound atoms.length M*(M-1) := by
      apply le_trans (Nat.mul_le_mul_left k _)
      · exact Nat.le_add_right ..
      · omega
    exact Nat.mul_le_mul c b

theorem counted_of_greedy {w v : Word α} {k : Nat} (run : Greedy k w v) :
    ∃ rules : List (Pair α), rules.length = k ∧ CountedRun false w rules v := by
  induction run with
  | nil => exact ⟨[],rfl,.nil _⟩
  | @cons k w v p maximal _ ih =>
    obtain ⟨rules,length,history⟩ := ih
    exact ⟨p::rules, by simp [length],.next maximal.2 history⟩

#print axioms state_bound
#print axioms bounded_initial_word
#print axioms bounded_initial_budget
#print axioms counted_of_greedy

end BoundedInitial
