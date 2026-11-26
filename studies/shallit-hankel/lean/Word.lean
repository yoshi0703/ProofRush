import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.BinaryRec
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Elementary properties of Shallit's four-symbol automatic word. Symbols
are represented by `Fin 4` in the order 1,2,3,4. -/
namespace ShallitWord

abbrev Symbol := Fin 4

def left (x : Symbol) : Symbol := if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 0 else 2
def right (x : Symbol) : Symbol := if x = 0 then 1 else if x = 1 then 2 else if x = 2 then 3 else 1

def word : ℕ → Symbol :=
  Nat.binaryRec 0 (fun b _ a => if b then right a else left a)

@[simp] theorem word_zero : word 0 = 0 := by
  rfl

@[simp] theorem word_even (n : ℕ) : word (2 * n) = left (word n) := by
  unfold word
  have h := Nat.binaryRec_eq (zero := (0 : Symbol))
    (bit := fun b _ a => if b then right a else left a) false n (Or.inl rfl)
  simpa [Nat.bit_false] using h

@[simp] theorem word_odd (n : ℕ) : word (2 * n + 1) = right (word n) := by
  unfold word
  have h := Nat.binaryRec_eq (zero := (0 : Symbol))
    (bit := fun b _ a => if b then right a else left a) true n (Or.inl rfl)
  simpa [Nat.bit_true] using h

/-- The nine allowed adjacent pairs, written with zero-based symbol values. -/
def pairAllowed (x y : Symbol) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 3) ∨
  (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨
  (x = 2 ∧ y = 0) ∨ (x = 2 ∧ y = 1) ∨
  (x = 3 ∧ y = 0) ∨ (x = 3 ∧ y = 1)

instance (x y : Symbol) : Decidable (pairAllowed x y) := by unfold pairAllowed; infer_instance

theorem image_internal : ∀ x : Symbol, pairAllowed (left x) (right x) := by decide

theorem image_boundary : ∀ x y : Symbol, pairAllowed x y → pairAllowed (right x) (left y) := by decide

/-- Every consecutive pair of the concrete infinite word is in the nine-pair table. -/
theorem adjacent_allowed : ∀ n : ℕ, pairAllowed (word n) (word (n + 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · have hn : n = 2 * (n / 2) := by omega
      rw [hn, word_even, word_odd]
      exact image_internal _
    · have hn : n = 2 * (n / 2) + 1 := by omega
      have hnnext : n + 1 = 2 * (n / 2 + 1) := by omega
      have hsmall : n / 2 < n := by omega
      have hprev := ih (n / 2) hsmall
      rw [hnnext, hn, word_odd, word_even]
      have hdiv : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
      rw [hdiv]
      exact image_boundary _ _ hprev

/-- A letter is uniquely determined by the two letters in its image. -/
theorem image_injective : ∀ x y : Symbol, left x = left y → right x = right y → x = y := by decide

/-- Relaxed overlaps remember a relation at each end and require equality in the interior. -/
def Relaxed (R S : Symbol → Symbol → Prop) (i d : ℕ) : Prop :=
  R (word i) (word (i + d)) ∧
  (∀ t, 0 < t → t < d → word (i + t) = word (i + d + t)) ∧
  S (word (i + d)) (word (i + 2 * d))

def pull (f : Symbol → Symbol) (R : Symbol → Symbol → Prop) : Symbol → Symbol → Prop :=
  fun x y => R (f x) (f y)

def meet (R S : Symbol → Symbol → Prop) : Symbol → Symbol → Prop :=
  fun x y => R x y ∧ S x y

/-- Even start and even displacement: a relaxed overlap pulls back through the morphism. -/
theorem halve_even_even {R S : Symbol → Symbol → Prop} {i e : ℕ} (he : 0 < e)
    (h : Relaxed R S (2 * i) (2 * e)) :
    Relaxed (meet (pull left R) (pull right Eq)) (pull left S) i e := by
  rcases h with ⟨hR, hm, hS⟩
  constructor
  · constructor
    · simpa only [pull, show 2 * i + 2 * e = 2 * (i + e) by omega, word_even] using hR
    · have h1 := hm 1 (by omega) (by omega)
      simpa only [pull, show 2 * i + 1 = 2 * i + 1 by rfl,
        show 2 * i + 2 * e + 1 = 2 * (i + e) + 1 by omega, word_odd] using h1
  · constructor
    · intro t ht hte
      have hl := hm (2 * t) (by omega) (by omega)
      have hr := hm (2 * t + 1) (by omega) (by omega)
      have hl' : left (word (i + t)) = left (word (i + e + t)) := by
        simpa only [show 2 * i + 2 * t = 2 * (i + t) by omega,
          show 2 * i + 2 * e + 2 * t = 2 * (i + e + t) by omega, word_even] using hl
      have hr' : right (word (i + t)) = right (word (i + e + t)) := by
        simpa only [show 2 * i + (2 * t + 1) = 2 * (i + t) + 1 by omega,
          show 2 * i + 2 * e + (2 * t + 1) = 2 * (i + e + t) + 1 by omega, word_odd] using hr
      exact image_injective _ _ hl' hr'
    · simpa only [pull, show 2 * i + 2 * e = 2 * (i + e) by omega,
        show 2 * i + 2 * (2 * e) = 2 * (i + 2 * e) by omega, word_even] using hS

/-- Odd start and even displacement: the complementary endpoint pullback. -/
theorem halve_odd_even {R S : Symbol → Symbol → Prop} {i e : ℕ} (he : 0 < e)
    (h : Relaxed R S (2 * i + 1) (2 * e)) :
    Relaxed (pull right R) (meet (pull left Eq) (pull right S)) i e := by
  rcases h with ⟨hR, hm, hS⟩
  constructor
  · simpa only [pull, show (2 * i + 1) + 2 * e = 2 * (i + e) + 1 by omega, word_odd] using hR
  · constructor
    · intro t ht hte
      have hl := hm (2 * t - 1) (by omega) (by omega)
      have hr := hm (2 * t) (by omega) (by omega)
      have hl' : left (word (i + t)) = left (word (i + e + t)) := by
        simpa only [show (2 * i + 1) + (2 * t - 1) = 2 * (i + t) by omega,
          show (2 * i + 1) + 2 * e + (2 * t - 1) = 2 * (i + e + t) by omega, word_even] using hl
      have hr' : right (word (i + t)) = right (word (i + e + t)) := by
        simpa only [show (2 * i + 1) + 2 * t = 2 * (i + t) + 1 by omega,
          show (2 * i + 1) + 2 * e + 2 * t = 2 * (i + e + t) + 1 by omega, word_odd] using hr
      exact image_injective _ _ hl' hr'
    · constructor
      · have hl := hm (2 * e - 1) (by omega) (by omega)
        simpa only [pull, show (2 * i + 1) + (2 * e - 1) = 2 * (i + e) by omega,
          show (2 * i + 1) + 2 * e + (2 * e - 1) = 2 * (i + 2 * e) by omega, word_even] using hl
      · simpa only [pull, show (2 * i + 1) + 2 * e = 2 * (i + e) + 1 by omega,
          show (2 * i + 1) + 2 * (2 * e) = 2 * (i + 2 * e) + 1 by omega, word_odd] using hS

/-- The endpoint-equivalence closure: E, E_{13}, E_{14}, E_{134}. -/
def equiv13 (x y : Symbol) : Prop := x = y ∨ ((x = 0 ∨ x = 2) ∧ (y = 0 ∨ y = 2))
def equiv14 (x y : Symbol) : Prop := x = y ∨ ((x = 0 ∨ x = 3) ∧ (y = 0 ∨ y = 3))
def equiv134 (x y : Symbol) : Prop := x = y ∨ ((x = 0 ∨ x = 2 ∨ x = 3) ∧ (y = 0 ∨ y = 2 ∨ y = 3))

instance (x y : Symbol) : Decidable (equiv13 x y) := by unfold equiv13; infer_instance
instance (x y : Symbol) : Decidable (equiv14 x y) := by unfold equiv14; infer_instance
instance (x y : Symbol) : Decidable (equiv134 x y) := by unfold equiv134; infer_instance

abbrev EndpointState := Fin 4

def stateLeft (s : EndpointState) : Symbol → Symbol → Prop :=
  if s = 2 then equiv14 else Eq

def stateRight (s : EndpointState) : Symbol → Symbol → Prop :=
  if s = 1 then equiv13 else if s = 3 then equiv134 else Eq

def nextEven (s : EndpointState) : EndpointState :=
  if s = 1 ∨ s = 3 then 3 else 1

instance (s : EndpointState) (x y : Symbol) : Decidable (stateLeft s x y) := by
  unfold stateLeft; split_ifs <;> infer_instance
instance (s : EndpointState) (x y : Symbol) : Decidable (stateRight s x y) := by
  unfold stateRight; split_ifs <;> infer_instance

theorem state_even_left : ∀ (s : EndpointState) (x y : Symbol),
    meet (pull left (stateLeft s)) (pull right Eq) x y ↔ stateLeft (nextEven s) x y := by unfold meet pull; decide

theorem state_even_right : ∀ (s : EndpointState) (x y : Symbol),
    pull left (stateRight s) x y ↔ stateRight (nextEven s) x y := by unfold pull; decide

theorem state_odd_left : ∀ (s : EndpointState) (x y : Symbol),
    pull right (stateLeft s) x y ↔ stateLeft 2 x y := by unfold pull; decide

theorem state_odd_right : ∀ (s : EndpointState) (x y : Symbol),
    meet (pull left Eq) (pull right (stateRight s)) x y ↔ stateRight 2 x y := by unfold meet pull; decide


theorem image_not_22 : ∀ x : Symbol, ¬ (left x = 1 ∧ right x = 1) := by decide

theorem no_three_twos (n : ℕ) :
    ¬ (word n = 1 ∧ word (n + 1) = 1 ∧ word (n + 2) = 1) := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · have hn : n = 2 * (n / 2) := by omega
    have hpair : left (word (n / 2)) = 1 ∧ right (word (n / 2)) = 1 := by
      have hfirst := h.1
      have hsecond := h.2.1
      rw [hn, word_even] at hfirst
      have hnext : n + 1 = 2 * (n / 2) + 1 := by omega
      rw [hnext, word_odd] at hsecond
      exact ⟨hfirst, hsecond⟩
    exact image_not_22 _ hpair
  · have hnext : n + 1 = 2 * (n / 2 + 1) := by omega
    have hnext2 : n + 2 = 2 * (n / 2 + 1) + 1 := by omega
    have hfirst := h.2.1
    have hsecond := h.2.2
    rw [hnext, word_even] at hfirst
    rw [hnext2, word_odd] at hsecond
    exact image_not_22 _ ⟨hfirst, hsecond⟩

/-- No four consecutive symbols beginning on opposite parities can agree.
This checks the complete finite pair-transition table, not a bounded prefix. -/
theorem crossing_four_impossible : ∀ a b x y z : Symbol,
    pairAllowed x y → pairAllowed y z → ¬ (x = 1 ∧ y = 1 ∧ z = 1) →
    ¬ (left a = right x ∧ right a = left y ∧
       left b = right y ∧ right b = left z) := by decide

/-- The finite crossing obstruction lifts to every pair of positions in the word. -/
theorem opposite_parity_four (i j : ℕ) :
    ¬ (word (2 * i) = word (2 * j + 1) ∧
       word (2 * i + 1) = word (2 * j + 2) ∧
       word (2 * i + 2) = word (2 * j + 3) ∧
       word (2 * i + 3) = word (2 * j + 4)) := by
  intro h
  have hxy := adjacent_allowed j
  have hyz := adjacent_allowed (j + 1)
  have h' : left (word i) = right (word j) ∧
      right (word i) = left (word (j + 1)) ∧
      left (word (i + 1)) = right (word (j + 1)) ∧
      right (word (i + 1)) = left (word (j + 2)) := by
    simpa only [show 2 * j + 2 = 2 * (j + 1) by omega,
      show 2 * i + 2 = 2 * (i + 1) by omega,
      show 2 * j + 3 = 2 * (j + 1) + 1 by omega,
      show 2 * i + 3 = 2 * (i + 1) + 1 by omega,
      show 2 * j + 4 = 2 * (j + 2) by omega, word_even, word_odd] using h
  have h222 := no_three_twos j
  have h222' : ¬ (word j = 1 ∧ word (j + 1) = 1 ∧ word (j + 1 + 1) = 1) := by
    simpa only [show j + 1 + 1 = j + 2 by omega] using h222
  exact crossing_four_impossible _ _ _ _ _ hxy hyz h222' h'

theorem opposite_parity_four_general {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    ¬ (word a = word b ∧ word (a + 1) = word (b + 1) ∧
       word (a + 2) = word (b + 2) ∧ word (a + 3) = word (b + 3)) := by
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) + 1 := by omega
  intro h
  have h' : word (2 * (a / 2)) = word (2 * (b / 2) + 1) ∧
       word (2 * (a / 2) + 1) = word (2 * (b / 2) + 2) ∧
       word (2 * (a / 2) + 2) = word (2 * (b / 2) + 3) ∧
       word (2 * (a / 2) + 3) = word (2 * (b / 2) + 4) := by
    rw [← ha', ← hb']
    simpa only [show 2 * (b / 2) + 2 = b + 1 by omega,
      show 2 * (b / 2) + 3 = b + 2 by omega,
      show 2 * (b / 2) + 4 = b + 3 by omega] using h
  exact opposite_parity_four _ _ h'

/-- All odd relaxed overlaps of period at least five are impossible,
independently of the endpoint relations. -/
theorem no_odd_relaxed_ge_five {R S : Symbol → Symbol → Prop} {i d : ℕ}
    (hd : 5 ≤ d) (hodd : d % 2 = 1) : ¬ Relaxed R S i d := by
  intro h
  have h1 := h.2.1 1 (by omega) (by omega)
  have h2 := h.2.1 2 (by omega) (by omega)
  have h3 := h.2.1 3 (by omega) (by omega)
  have h4 := h.2.1 4 (by omega) (by omega)
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have ha : (i + d + 1) % 2 = 0 := by omega
    have hb : (i + 1) % 2 = 1 := by omega
    apply opposite_parity_four_general ha hb
    refine ⟨h1.symm, ?_, ?_, ?_⟩
    · simpa only [show i + d + 1 + 1 = i + d + 2 by omega, show i + 1 + 1 = i + 2 by omega] using h2.symm
    · simpa only [show i + d + 1 + 2 = i + d + 3 by omega, show i + 1 + 2 = i + 3 by omega] using h3.symm
    · simpa only [show i + d + 1 + 3 = i + d + 4 by omega, show i + 1 + 3 = i + 4 by omega] using h4.symm
  · have ha : (i + 1) % 2 = 0 := by omega
    have hb : (i + d + 1) % 2 = 1 := by omega
    apply opposite_parity_four_general ha hb
    refine ⟨h1, ?_, ?_, ?_⟩
    · simpa only [show i + d + 1 + 1 = i + d + 2 by omega, show i + 1 + 1 = i + 2 by omega] using h2
    · simpa only [show i + d + 1 + 2 = i + d + 3 by omega, show i + 1 + 2 = i + 3 by omega] using h3
    · simpa only [show i + d + 1 + 3 = i + d + 4 by omega, show i + 1 + 3 = i + 4 by omega] using h4

/-- All endpoint-state possibilities exclude period one in both start parities. -/
theorem no_one_even_table : ∀ (s : EndpointState) (a b : Symbol),
    pairAllowed a b → ¬ (stateLeft s (left a) (right a) ∧ stateRight s (right a) (left b)) := by decide

theorem no_one_odd_table : ∀ (s : EndpointState) (a b : Symbol),
    pairAllowed a b → ¬ (stateLeft s (right a) (left b) ∧ stateRight s (left b) (right b)) := by decide

/-- Period-three rejection from the global pair invariant and the prohibition 222. -/
theorem no_three_even_table : ∀ (s : EndpointState) (a b c d : Symbol),
    pairAllowed a b → pairAllowed b c → pairAllowed c d →
    ¬ (a = 1 ∧ b = 1 ∧ c = 1) → ¬ (b = 1 ∧ c = 1 ∧ d = 1) →
    ¬ (stateLeft s (left a) (right b) ∧ right a = left c ∧
      left b = right c ∧ stateRight s (right b) (left d)) := by decide

set_option maxRecDepth 4096 in
theorem no_three_odd_table : ∀ (s : EndpointState) (a b c d : Symbol),
    pairAllowed a b → pairAllowed b c → pairAllowed c d →
    ¬ (a = 1 ∧ b = 1 ∧ c = 1) → ¬ (b = 1 ∧ c = 1 ∧ d = 1) →
    ¬ (stateLeft s (right a) (left c) ∧ left b = right c ∧
      right b = left d ∧ stateRight s (left c) (right d)) := by
  intro s a b c d
  fin_cases s <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

theorem no_one_state (s : EndpointState) (i : ℕ) :
    ¬ Relaxed (stateLeft s) (stateRight s) i 1 := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · have hi : 2 * (i / 2) = i := by omega
    have h1 : 2 * (i / 2) + 1 = i + 1 := by omega
    have h2 : 2 * (i / 2 + 1) = i + 2 * 1 := by omega
    have hl : stateLeft s (word (2 * (i / 2))) (word (2 * (i / 2) + 1)) := by
      rw [hi]
      exact h.1
    have hr : stateRight s (word (2 * (i / 2) + 1)) (word (2 * (i / 2 + 1))) := by
      rw [h1, h2]
      exact h.2.2
    apply no_one_even_table s (word (i / 2)) (word (i / 2 + 1)) (adjacent_allowed (i / 2))
    exact ⟨by simpa only [word_even, word_odd] using hl, by simpa only [word_even, word_odd] using hr⟩
  · have hi : 2 * (i / 2) + 1 = i := by omega
    have h1 : 2 * (i / 2 + 1) = i + 1 := by omega
    have h2 : 2 * (i / 2 + 1) + 1 = i + 2 * 1 := by omega
    have hl : stateLeft s (word (2 * (i / 2) + 1)) (word (2 * (i / 2 + 1))) := by
      rw [hi, h1]
      exact h.1
    have hr : stateRight s (word (2 * (i / 2 + 1))) (word (2 * (i / 2 + 1) + 1)) := by
      rw [h2, h1]
      exact h.2.2
    apply no_one_odd_table s (word (i / 2)) (word (i / 2 + 1)) (adjacent_allowed (i / 2))
    exact ⟨by simpa only [word_even, word_odd] using hl, by simpa only [word_even, word_odd] using hr⟩

theorem no_three_state (s : EndpointState) (i : ℕ) :
    ¬ Relaxed (stateLeft s) (stateRight s) i 3 := by
  intro h
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
    have h0 := h.1
    have h1 := h.2.1 1 (by omega) (by omega)
    have h2 := h.2.1 2 (by omega) (by omega)
    have h3 := h.2.2
    have hrel : stateLeft s (left (word j)) (right (word (j + 1))) ∧
        right (word j) = left (word (j + 2)) ∧
        left (word (j + 1)) = right (word (j + 2)) ∧
        stateRight s (right (word (j + 1))) (left (word (j + 3))) := by
      constructor
      · simpa only [show 2 * j + 3 = 2 * (j + 1) + 1 by omega, word_even, word_odd] using h0
      constructor
      · simpa only [show 2 * j + 3 + 1 = 2 * (j + 2) by omega, word_odd, word_even] using h1
      constructor
      · simpa only [show 2 * j + 2 = 2 * (j + 1) by omega,
          show 2 * j + 3 + 2 = 2 * (j + 2) + 1 by omega, word_odd, word_even] using h2
      · simpa only [show 2 * j + 3 = 2 * (j + 1) + 1 by omega,
          show 2 * j + 2 * 3 = 2 * (j + 3) by omega, word_even, word_odd] using h3
    apply no_three_even_table s _ _ _ _ (adjacent_allowed j) (adjacent_allowed (j + 1))
      (by simpa only [show j + 1 + 1 = j + 2 by omega] using adjacent_allowed (j + 2))
      (no_three_twos j) (by simpa only [show j + 1 + 1 = j + 2 by omega,
        show j + 1 + 2 = j + 3 by omega] using no_three_twos (j + 1))
    exact hrel
  · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := ⟨i / 2, by omega⟩
    have h0 := h.1
    have h1 := h.2.1 1 (by omega) (by omega)
    have h2 := h.2.1 2 (by omega) (by omega)
    have h3 := h.2.2
    have hrel : stateLeft s (right (word j)) (left (word (j + 2))) ∧
        left (word (j + 1)) = right (word (j + 2)) ∧
        right (word (j + 1)) = left (word (j + 3)) ∧
        stateRight s (left (word (j + 2))) (right (word (j + 3))) := by
      constructor
      · simpa only [show 2 * j + 1 + 3 = 2 * (j + 2) by omega, word_even, word_odd] using h0
      constructor
      · simpa only [show 2 * j + 1 + 1 = 2 * (j + 1) by omega,
          show 2 * j + 1 + 3 + 1 = 2 * (j + 2) + 1 by omega, word_odd, word_even] using h1
      constructor
      · simpa only [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega,
          show 2 * j + 1 + 3 + 2 = 2 * (j + 3) by omega, word_odd, word_even] using h2
      · simpa only [show 2 * j + 1 + 3 = 2 * (j + 2) by omega,
          show 2 * j + 1 + 2 * 3 = 2 * (j + 3) + 1 by omega, word_even, word_odd] using h3
    apply no_three_odd_table s _ _ _ _ (adjacent_allowed j) (adjacent_allowed (j + 1))
      (by simpa only [show j + 1 + 1 = j + 2 by omega] using adjacent_allowed (j + 2))
      (no_three_twos j) (by simpa only [show j + 1 + 1 = j + 2 by omega,
        show j + 1 + 2 = j + 3 by omega] using no_three_twos (j + 1))
    exact hrel

/-- Every state in the pullback closure excludes every positive period. -/
theorem no_relaxed_state : ∀ d : ℕ, 0 < d → ∀ (s : EndpointState) (i : ℕ),
    ¬ Relaxed (stateLeft s) (stateRight s) i d := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro hd s i h
    rcases Nat.mod_two_eq_zero_or_one d with he | ho
    · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
      have hepos : 0 < e := by omega
      have helt : e < 2 * e := by omega
      rcases Nat.mod_two_eq_zero_or_one i with hie | hio
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j := ⟨i / 2, by omega⟩
        have hh := halve_even_even hepos h
        have hh' : Relaxed (stateLeft (nextEven s)) (stateRight (nextEven s)) j e := by
          refine ⟨(state_even_left s _ _).mp hh.1, hh.2.1, ?_⟩
          exact (state_even_right s _ _).mp hh.2.2
        exact ih e helt hepos (nextEven s) j hh'
      · obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j + 1 := ⟨i / 2, by omega⟩
        have hh := halve_odd_even hepos h
        have hh' : Relaxed (stateLeft 2) (stateRight 2) j e := by
          refine ⟨(state_odd_left s _ _).mp hh.1, hh.2.1, ?_⟩
          exact (state_odd_right s _ _).mp hh.2.2
        exact ih e helt hepos 2 j hh'
    · by_cases h1 : d = 1
      · subst d
        exact no_one_state s i h
      · by_cases h3 : d = 3
        · subst d
          exact no_three_state s i h
        · have hlarge : 5 ≤ d := by omega
          exact no_odd_relaxed_ge_five hlarge ho h

/-- Shallit's four-symbol word is overlap-free at every offset and period. -/
theorem overlap_free (i d : ℕ) (hd : 0 < d) :
    ∃ t ≤ d, word (i + t) ≠ word (i + d + t) := by
  by_contra h
  have heq : ∀ t, t ≤ d → word (i + t) = word (i + d + t) := by
    intro t ht
    by_contra hne
    exact h ⟨t, ht, hne⟩
  apply no_relaxed_state d hd 0 i
  constructor
  · simpa only [stateLeft, Fin.reduceEq, ite_false, Nat.add_zero] using heq 0 (by omega)
  · constructor
    · intro t ht htd
      exact heq t (by omega)
    · have hlast := heq d (le_refl d)
      simpa only [stateRight, Fin.reduceEq, ite_false, show i + d + d = i + 2 * d by omega] using hlast

end ShallitWord
