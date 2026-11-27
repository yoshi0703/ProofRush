import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.GCD.Basic

/-! The source language is binary. Letter `true` stands for a, and
`false` for b. Each gap contributes one a followed by its number of b's. -/

namespace KasonyiWord

abbrev Word := List Bool

def ofGaps (gaps : List ℕ) : Word :=
  gaps.flatMap (fun n => true :: List.replicate n false)

def encode {n : ℕ} (e : Fin n → ℕ) : Word := ofGaps (List.ofFn e)

def decode : Word → ℕ × List ℕ
  | [] => (0, [])
  | true :: tail => (0, (decode tail).1 :: (decode tail).2)
  | false :: tail => ((decode tail).1 + 1, (decode tail).2)

private theorem decode_prefix (n : ℕ) (w : Word) :
    decode (List.replicate n false ++ w) = ((decode w).1+n, (decode w).2) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, decode, ih, Nat.add_assoc]

theorem decode_ofGaps (l : List ℕ) : decode (ofGaps l) = (0, l) := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    change (0, (decode (List.replicate n false ++ ofGaps l)).1 ::
      (decode (List.replicate n false ++ ofGaps l)).2) = (0, n :: l)
    simp [decode_prefix, ih]

theorem decode_encode {n : ℕ} (e : Fin n → ℕ) : decode (encode e) = (0, List.ofFn e) :=
  decode_ofGaps _

def power (w : Word) (k : ℕ) : Word := (List.replicate k w).flatten

def Primitive (w : Word) : Prop :=
  w ≠ [] ∧ ∀ (v : Word) (k : ℕ), 2 ≤ k → w ≠ power v k

theorem count_a (gaps : List ℕ) : (ofGaps gaps).count true = gaps.length := by
  induction gaps with
  | nil => rfl
  | cons n tail ih =>
    simp [ofGaps, List.count_replicate] at ih ⊢
    omega

theorem count_b (gaps : List ℕ) : (ofGaps gaps).count false = gaps.sum := by
  induction gaps with
  | nil => rfl
  | cons n tail ih => simpa [ofGaps] using congrArg (n + ·) ih

theorem count_power (c : Bool) (w : Word) (k : ℕ) :
    (power w k).count c = k * w.count c := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    simp only [power, List.replicate_succ, List.flatten_cons, List.count_append, Nat.succ_mul] at ih ⊢
    omega

theorem primitive_of_coprime {n : ℕ} (e : Fin n → ℕ) (hn : 0 < n)
    (h : n.Coprime (∑ i, e i)) : Primitive (encode e) := by
  have ha : (encode e).count true = n := by simp [encode, count_a]
  have hb : (encode e).count false = ∑ i, e i := by simp [encode, count_b, List.sum_ofFn]
  constructor
  · intro he
    rw [he] at ha
    simp at ha
    omega
  · intro v k hk he
    have h1 : k ∣ n := ⟨v.count true, by rw [← ha, he, count_power]⟩
    have h2 : k ∣ ∑ i, e i := ⟨v.count false, by rw [← hb, he, count_power]⟩
    have h3 := Nat.dvd_gcd h1 h2
    rw [h.gcd_eq_one, Nat.dvd_one] at h3
    omega

end KasonyiWord
