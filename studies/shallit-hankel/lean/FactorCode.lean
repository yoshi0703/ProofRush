import Word
import NormalIndex
import Mathlib.Data.List.OfFn

/-! Factor-complexity bounds for the concrete Shallit morphism. -/

namespace ShallitFactorCode

open ShallitWord ShallitNormalIndex

/-- The symbol at position `r` in a (2^h)-letter substitution block. -/
def block : ℕ → Symbol → ℕ → Symbol
  | 0, a, _ => a
  | h+1, a, r =>
      if r % 2 = 0 then left (block h a (r/2)) else right (block h a (r/2))

theorem word_block (h q r : ℕ) (hr : r < 2^h) :
    word (2^h * q + r) = block h (word q) r := by
  induction h generalizing r with
  | zero =>
    have hr0 : r = 0 := by norm_num at hr; omega
    simp [hr0, block]
  | succ h ih =>
    have hr' : r/2 < 2^h := by rw [Nat.pow_succ] at hr; omega
    have ha : 2^(h+1) * q = 2 * (2^h * q) := by
      rw [Nat.pow_succ, Nat.mul_comm (2^h) 2, Nat.mul_assoc]
    have hpos : 2^(h+1)*q+r = 2*(2^h*q+r/2) + r%2 := by rw [ha]; omega
    rcases Nat.mod_two_eq_zero_or_one r with he | ho
    · rw [hpos, he, Nat.add_zero, word_even, ih (r/2) hr']
      simp [block, he]
    · rw [hpos, ho, word_odd, ih (r/2) hr']
      simp [block, ho]

def pairs : Finset (Symbol × Symbol) :=
  Finset.univ.filter (fun p => pairAllowed p.1 p.2)

def inTwoBlocks (a b : Symbol) (r : ℕ) : Symbol :=
  if r < 16 then block 4 a r else block 4 b (r-16)

def candidates (n : ℕ) : Finset (List Symbol) :=
  (pairs.product (Finset.univ : Finset (Fin 16))).image
    (fun p => List.ofFn (fun j : Fin n => inTwoBlocks p.1.1 p.1.2 ((p.2 : ℕ) + j)))

theorem word_inTwoBlocks (q r : ℕ) (hr : r < 32) :
    word (16*q+r) = inTwoBlocks (word q) (word (q+1)) r := by
  by_cases h : r < 16
  · simpa [inTwoBlocks, h] using word_block 4 q r (by norm_num; omega)
  · have hpos : 16*q+r = 16*(q+1)+(r-16) := by omega
    rw [hpos]
    simpa [inTwoBlocks, h] using word_block 4 (q+1) (r-16) (by norm_num; omega)

theorem factor_mem (n : ℕ) (hn : n ≤ 16) (u : ℕ) :
    List.ofFn (fun j : Fin n => word (u+j)) ∈ candidates n := by
  unfold candidates
  apply Finset.mem_image.mpr
  let q := u/16
  let r : Fin 16 := ⟨u % 16, Nat.mod_lt _ (by decide)⟩
  refine ⟨((word q, word (q+1)),r), ?_, ?_⟩
  · simp [pairs, adjacent_allowed]
  · apply congrArg List.ofFn
    funext j
    have hpos : u+(j : ℕ) = 16*q+((r : ℕ)+j) := by dsimp [q,r]; omega
    rw [hpos, word_inTwoBlocks]
    have hj := j.isLt
    have hr := r.isLt
    omega

theorem factorCode_base (n : ℕ) (hn : n ≤ 16) :
    FactorCode word n (candidates n).card := by
  classical
  let e : (candidates n : Type) ≃ Fin (candidates n).card :=
    Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let f (u : ℕ) : (candidates n : Type) :=
    ⟨List.ofFn (fun j : Fin n => word (u+j)), factor_mem n hn u⟩
  refine ⟨e ∘ f, fun u v h j hj => ?_⟩
  have hs : f u = f v := e.injective h
  have hlist : List.ofFn (fun j : Fin n => word (u+j)) =
      List.ofFn (fun j : Fin n => word (v+j)) := congrArg Subtype.val hs
  exact congrFun (List.ofFn_inj.mp hlist) (⟨j,hj⟩ : Fin n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem base_counts :
    (candidates 1).card = 4 ∧ (candidates 2).card = 9 ∧
    (candidates 3).card = 15 ∧ (candidates 4).card = 22 ∧
    (candidates 5).card = 28 ∧ (candidates 6).card = 35 ∧
    (candidates 7).card = 42 ∧ (candidates 8).card = 49 ∧
    (candidates 9).card = 56 := by decide

theorem word_step (u : ℕ) :
    word u = (if u%2=0 then left else right) (word (u/2)) := by
  rcases Nat.mod_two_eq_zero_or_one u with h | h
  · have hu : u = 2*(u/2) := by omega
    simpa [h] using (congrArg word hu).trans (word_even (u/2))
  · have hu : u = 2*(u/2)+1 := by omega
    simpa [h] using (congrArg word hu).trans (word_odd (u/2))

theorem factorCode_linear (n : ℕ) (hn : 5 ≤ n) :
    FactorCode word n (7*(n-1)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hb : n < 10
    · rcases base_counts with ⟨_,_,_,_,h5,h6,h7,h8,h9⟩
      have hcases : n=5 ∨ n=6 ∨ n=7 ∨ n=8 ∨ n=9 := by omega
      rcases hcases with h | h | h | h | h <;> subst n
      · simpa [h5] using factorCode_base 5 (by decide)
      · simpa [h6] using factorCode_base 6 (by decide)
      · simpa [h7] using factorCode_base 7 (by decide)
      · simpa [h8] using factorCode_base 8 (by decide)
      · simpa [h9] using factorCode_base 9 (by decide)
    · let j := n/2
      have hj : 5 ≤ j := by dsimp [j]; omega
      have hjlt : j+1 < n := by dsimp [j]; omega
      have hc₀ := ih j (by omega) hj
      have hc₁ := ih (j+1) hjlt (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hnj : n = 2*j := by dsimp [j]; omega
        have he (i : ℕ) (hi : i < n) : i/2 < j := by omega
        have ho (i : ℕ) (hi : i < n) : (i+1)/2 < j+1 := by omega
        have hres := factorCode_uniform_two word
          (fun u => if u=0 then left else right) word_step he ho hc₀ hc₁
        have hsum : 7*(j-1)+7*(j+1-1) = 7*(n-1) := by omega
        exact hsum ▸ hres
      · have hnj : n = 2*j+1 := by dsimp [j]; omega
        have he (i : ℕ) (hi : i < n) : i/2 < j+1 := by omega
        have ho (i : ℕ) (hi : i < n) : (i+1)/2 < j+1 := by omega
        have hres := factorCode_uniform_two word
          (fun u => if u=0 then left else right) word_step he ho hc₁ hc₁
        have hsum : 7*(j+1-1)+7*(j+1-1) = 7*(n-1) := by omega
        exact hsum ▸ hres

/-- Proven capacity for the length-`n` factor code. -/
def capacity (n : ℕ) : ℕ :=
  if n=1 then 4 else if n=2 then 9 else if n=3 then 15 else if n=4 then 22 else 7*(n-1)

theorem factorCode_capacity (n : ℕ) (hn : 0 < n) :
    FactorCode word n (capacity n) := by
  by_cases h : 5 ≤ n
  · have hcap : capacity n = 7*(n-1) := by
      simp only [capacity]
      split_ifs <;> omega
    rw [hcap]
    exact factorCode_linear n h
  · rcases base_counts with ⟨h1,h2,h3,h4,_⟩
    have hcases : n=1 ∨ n=2 ∨ n=3 ∨ n=4 := by omega
    rcases hcases with h | h | h | h <;> subst n
    · simpa [capacity, h1] using factorCode_base 1 (by decide)
    · simpa [capacity, h2] using factorCode_base 2 (by decide)
    · simpa [capacity, h3] using factorCode_base 3 (by decide)
    · simpa [capacity, h4] using factorCode_base 4 (by decide)

theorem capacity_bound (n : ℕ) (hn : 0 < n) :
    2*capacity n-n+1 ≤ 13*n := by
  unfold capacity
  split_ifs <;> omega

/-- Numeric moments of the shifted word, in an arbitrary coding of its four symbols. -/
def moments {F : Type*} (g : Symbol → F) (t : ℕ) (n : ℕ) : F :=
  g (word (t+n))

theorem next_order_of_noOverlap {F : Type*} [Field F]
    (g : Symbol → F) (hg : Function.Injective g) (hw : NoOverlap word)
    (t k : ℕ) (hpos : 0 < k) (hk : (hankel (moments g t) k).det ≠ 0) :
    ∃ q, k < q ∧ q ≤ 13*k ∧ (hankel (moments g t) q).det ≠ 0 ∧
      ∀ j, k < j → j < q → (hankel (moments g t) j).det = 0 := by
  have hover : NoOverlap (moments g t) := (hw.shift t).map hg
  have hcode : FactorCode (moments g t) k (capacity k) :=
    ((factorCode_capacity k hpos).shift t).map g
  obtain ⟨q, hkq, hq, hn, hz⟩ := next_nonsingular_of_factorCode _ hk hover hcode
  exact ⟨q, hkq, hq.trans (capacity_bound k hpos), hn, hz⟩

theorem nonsingular_interval_of_noOverlap {F : Type*} [Field F]
    (g : Symbol → F) (hg : Function.Injective g) (hw : NoOverlap word)
    (t : ℕ) (hfirst : (hankel (moments g t) 1).det ≠ 0)
    (s : ℕ) :
    ∃ q, s+1 < q ∧ q ≤ 13*(s+1) ∧ (hankel (moments g t) q).det ≠ 0 := by
  induction s with
  | zero =>
    obtain ⟨q,h1q,hq,hn,_⟩ :=
      next_order_of_noOverlap g hg hw t 1 (by decide) hfirst
    exact ⟨q,h1q,hq,hn⟩
  | succ s ih =>
    obtain ⟨q, hlow, hhigh, hq⟩ := ih
    by_cases h : s+1+1 < q
    · exact ⟨q, by omega, by omega, hq⟩
    · have hq' : q = s+1+1 := by omega
      obtain ⟨r, hr, hrhigh, hrn, _⟩ :=
        next_order_of_noOverlap g hg hw t q (by omega) hq
      exact ⟨r, by omega, by omega, hrn⟩

/-- Read the formal symbols as the integers 1, 2, 3 and 4. -/
def numeric {F : Type*} [NatCast F] (a : Symbol) : F :=
  ((a.val+1 : ℕ) : F)

theorem numeric_injective {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : p = 0 ∨ 5 ≤ p) : Function.Injective (numeric (F := F)) := by
  intro a b h
  apply Fin.ext
  change ((a.val+1 : ℕ) : F) = ((b.val+1 : ℕ) : F) at h
  have hm := (CharP.cast_eq_iff_mod_eq F p).mp h
  rcases hp with rfl | hp
  · simpa using hm
  · have ha : a.val+1 < p := by have ha := a.isLt; omega
    have hb : b.val+1 < p := by have hb := b.isLt; omega
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hm

theorem numeric_ne_zero {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : p = 0 ∨ 5 ≤ p) (a : Symbol) : numeric (F := F) a ≠ 0 := by
  intro h
  change ((a.val+1 : ℕ) : F) = 0 at h
  rw [← Nat.cast_zero] at h
  have hm := (CharP.cast_eq_iff_mod_eq F p).mp h
  rcases hp with rfl | hp
  · simp at hm
  · have ha : a.val+1 < p := by have ha := a.isLt; omega
    simp [Nat.mod_eq_of_lt ha] at hm

/-- In every multiplicative interval `(R,13R]`, with `R ≥ 1`,
each shift of the concrete numerical word has a nonsingular Hankel order. -/
theorem numeric_nonsingular_interval {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : p = 0 ∨ 5 ≤ p) (t R : ℕ) (hR : 0 < R) :
    ∃ q, R < q ∧ q ≤ 13*R ∧
      (hankel (moments (numeric (F := F)) t) q).det ≠ 0 := by
  have hover : NoOverlap word := overlap_free
  have hf : (hankel (moments (numeric (F := F)) t) 1).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact numeric_ne_zero hp _
  have hs : R-1+1 = R := by omega
  simpa [hs] using nonsingular_interval_of_noOverlap numeric
    (numeric_injective hp) hover t hf (R-1)

/-- Rational specialization of the canonical numerical Hankel theorem. -/
theorem rational_nonsingular_interval (t R : ℕ) (hR : 0 < R) :
    ∃ q, R < q ∧ q ≤ 13*R ∧
      (hankel (moments (numeric (F := ℚ)) t) q).det ≠ 0 :=
  numeric_nonsingular_interval (p := 0) (Or.inl rfl) t R hR

#print axioms base_counts
#print axioms factorCode_linear
#print axioms nonsingular_interval_of_noOverlap
#print axioms numeric_nonsingular_interval
#print axioms rational_nonsingular_interval

end ShallitFactorCode
