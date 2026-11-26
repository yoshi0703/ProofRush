import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! The positive-odd accelerated moves in Althöfer Prize 3.
The state 1 is terminal. The statement only classifies losses in exactly two
moves, before any questions of infinite optimal play arise. -/
namespace Althofer

set_option maxHeartbeats 4000000

inductive Sign
  | plus | minus
  deriving DecidableEq

def Sign.val : Sign → ℤ
  | .plus => 1
  | .minus => -1

def Sign.flip : Sign → Sign
  | .plus => .minus
  | .minus => .plus

/-- In each equation the odd child is the result after all halving. -/
def Move (s : Sign) (n child : ℤ) : Prop :=
  0 < child ∧ child % 2 = 1 ∧
    ∃ e : ℕ, 0 < e ∧ (2 : ℤ)^e * child = 3*n + s.val

def WinsInOne (n : ℤ) : Prop := 1 < n ∧ ∃ s, Move s n 1

/-- Starting player must move to a nonterminal state with an immediate win
available to the other player, whichever of the two signs is chosen. -/
def LosesInTwo (n : ℤ) : Prop :=
  1 < n ∧ n % 2 = 1 ∧
    ∀ s, ∃ child, Move s n child ∧ 1 < child ∧ WinsInOne child

def Families (n : ℤ) : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ 9*n + 1 = (2 : ℤ)^(6*k)) ∨
  (∃ k : ℕ, 1 ≤ k ∧ 9*n - 1 = (2 : ℤ)^(6*k+3)) ∨
  (∃ k : ℕ, 1 ≤ k ∧ 9*n + 5 = (2 : ℤ)^(6*k+5)) ∨
  (∃ k : ℕ, 1 ≤ k ∧ 9*n - 5 = (2 : ℤ)^(6*k+2))

private theorem pow_split {a m : ℕ} (h : m ≤ a) :
    (2 : ℤ)^a = 2^m * 2^(a-m) := by
  rw [← pow_add]
  congr 1
  omega

private theorem two_pow_pos (a : ℕ) : (0 : ℤ) < 2^a := pow_pos (by norm_num) _

private theorem two_pow_even {a : ℕ} (h : 0 < a) : (2 : ℤ)^a % 2 = 0 := by
  rw [pow_split (m := 1) h]
  norm_num

theorem move_unique {s : Sign} {n x y : ℤ}
    (hx : Move s n x) (hy : Move s n y) : x = y := by
  obtain ⟨_, hxodd, a, _, ha⟩ := hx
  obtain ⟨_, hyodd, b, _, hb⟩ := hy
  have heq : (2 : ℤ)^a * x = 2^b * y := ha.trans hb.symm
  have H (c d : ℕ) (v w : ℤ) (hw : v % 2 = 1) (hcd : c < d)
      (h : (2 : ℤ)^c * v = 2^d * w) : False := by
    rw [pow_split (m := c) (by omega : c ≤ d), mul_assoc] at h
    have hv : v = 2^(d-c) * w := mul_left_cancel₀ (two_pow_pos c).ne' h
    rw [pow_split (m := 1) (by omega : 1 ≤ d-c), pow_one, mul_assoc] at hv
    omega
  have hab : a = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hg
    · exact H a b x y hxodd hl heq
    · exact H b a y x hyodd hg heq.symm
  subst b
  exact mul_left_cancel₀ (two_pow_pos a).ne' heq

private theorem factor_positive (a : ℕ) (ha : 0 < a) :
    ∃ child : ℤ, 0 < child ∧ child % 2 = 1 ∧
      ∃ e : ℕ, (2 : ℤ)^e * child = (a : ℤ) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    by_cases odd : a % 2 = 1
    · refine ⟨a, by omega, by omega, 0, by simp⟩
    · have small : a/2 < a := by omega
      have pos : 0 < a/2 := by omega
      obtain ⟨child, hc, ho, e, eq⟩ := ih (a/2) small pos
      refine ⟨child, hc, ho, e+1, ?_⟩
      calc
        _ = 2*((2 : ℤ)^e*child) := by rw [pow_succ]; ring
        _ = _ := by rw [eq]; omega

theorem move_exists (s : Sign) {n : ℤ} (hn : 0 < n) (ho : n % 2 = 1) :
    ∃ child, Move s n child := by
  let raw := 3*n+s.val
  have raw_pos : 0 < raw := by cases s <;> simp [raw, Sign.val] <;> omega
  have raw_even : raw % 2 = 0 := by cases s <;> simp [raw, Sign.val] <;> omega
  have cast_raw : ((raw.toNat : ℕ) : ℤ) = raw := Int.toNat_of_nonneg (by omega)
  obtain ⟨child, hc, hodd, a, eq⟩ := factor_positive raw.toNat (by omega)
  rw [cast_raw] at eq
  refine ⟨child, hc, hodd, a, ?_, eq⟩
  by_contra ha
  have hzero : a = 0 := by omega
  subst a
  simp at eq
  omega

private theorem mk_two {n y z : ℤ} {s sy sz : Sign} {e b c : ℕ}
    (hn : 1 < n) (ho : n % 2 = 1)
    (hy : 1 < y) (hyodd : y % 2 = 1) (hz : 1 < z) (hzodd : z % 2 = 1)
    (he : 0 < e) (hb : 0 < b) (hc : 0 < c)
    (hs : 2*y = 3*n + s.val)
    (hl : (2 : ℤ)^e*z = 3*n + s.flip.val)
    (hys : (2 : ℤ)^b = 3*y + sy.val) (hzs : (2 : ℤ)^c = 3*z + sz.val) :
    LosesInTwo n := by
  have short : Move s n y := ⟨by omega, hyodd, 1, by decide, by simpa using hs⟩
  have long : Move s.flip n z := ⟨by omega, hzodd, e, he, hl⟩
  have shortWin : WinsInOne y := ⟨hy, sy, by decide, by decide, b, hb, by simpa using hys⟩
  have longWin : WinsInOne z := ⟨hz, sz, by decide, by decide, c, hc, by simpa using hzs⟩
  refine ⟨hn, ho, ?_⟩
  cases s <;> intro move <;> cases move
  · exact ⟨y, short, hy, shortWin⟩
  · exact ⟨z, long, hz, longWin⟩
  · exact ⟨z, long, hz, longWin⟩
  · exact ⟨y, short, hy, shortWin⟩

private theorem first_family {n : ℤ} {a : ℕ} (ha : 6 ≤ a)
    (hn : 9*n + 1 = (2 : ℤ)^a) : LosesInTwo n := by
  have h₁ := pow_split (a := a) (m := 1) (by omega)
  have h₂ := pow_split (a := a) (m := 2) (by omega)
  have h₅ := pow_split (a := a) (m := 5) (by omega)
  have h₆ := pow_split (a := a) (m := 6) ha
  have positive := two_pow_pos (a-6)
  norm_num at h₁ h₂ h₅ h₆
  apply mk_two (y := (3*n+1)/2) (z := (3*n-1)/4)
    (s := .plus) (sy := .minus) (sz := .plus) (e := 2) (b := a-1) (c := a-2)
    <;> (try simp [Sign.val, Sign.flip]) <;> omega

private theorem second_family {n : ℤ} {a : ℕ} (ha : 6 ≤ a)
    (hn : 9*n - 1 = (2 : ℤ)^a) : LosesInTwo n := by
  have h₁ := pow_split (a := a) (m := 1) (by omega)
  have h₂ := pow_split (a := a) (m := 2) (by omega)
  have h₅ := pow_split (a := a) (m := 5) (by omega)
  have h₆ := pow_split (a := a) (m := 6) ha
  have positive := two_pow_pos (a-6)
  norm_num at h₁ h₂ h₅ h₆
  apply mk_two (y := (3*n-1)/2) (z := (3*n+1)/4)
    (s := .minus) (sy := .plus) (sz := .minus) (e := 2) (b := a-1) (c := a-2)
    <;> (try simp [Sign.val, Sign.flip]) <;> omega

private theorem third_family {n : ℤ} {a : ℕ} (ha : 6 ≤ a)
    (hn : 9*n + 5 = (2 : ℤ)^a) : LosesInTwo n := by
  have h₁ := pow_split (a := a) (m := 1) (by omega)
  have h₃ := pow_split (a := a) (m := 3) (by omega)
  have h₅ := pow_split (a := a) (m := 5) (by omega)
  have h₆ := pow_split (a := a) (m := 6) ha
  have positive := two_pow_pos (a-6)
  norm_num at h₁ h₃ h₅ h₆
  apply mk_two (y := (3*n+1)/2) (z := (3*n-1)/8)
    (s := .plus) (sy := .plus) (sz := .plus) (e := 3) (b := a-1) (c := a-3)
    <;> (try simp [Sign.val, Sign.flip]) <;> omega

private theorem fourth_family {n : ℤ} {a : ℕ} (ha : 6 ≤ a)
    (hn : 9*n - 5 = (2 : ℤ)^a) : LosesInTwo n := by
  have h₁ := pow_split (a := a) (m := 1) (by omega)
  have h₃ := pow_split (a := a) (m := 3) (by omega)
  have h₅ := pow_split (a := a) (m := 5) (by omega)
  have h₆ := pow_split (a := a) (m := 6) ha
  have positive := two_pow_pos (a-6)
  norm_num at h₁ h₃ h₅ h₆
  apply mk_two (y := (3*n-1)/2) (z := (3*n+1)/8)
    (s := .minus) (sy := .minus) (sz := .minus) (e := 3) (b := a-1) (c := a-3)
    <;> (try simp [Sign.val, Sign.flip]) <;> omega

theorem loses_of_families {n : ℤ} (h : Families n) : LosesInTwo n := by
  rcases h with ⟨k,hk,h⟩ | ⟨k,hk,h⟩ | ⟨k,hk,h⟩ | ⟨k,hk,h⟩
  · exact first_family (by omega) h
  · exact second_family (by omega) h
  · exact third_family (by omega) h
  · exact fourth_family (by omega) h

private theorem small_impossible {x : ℤ} {s : Sign} {a : ℕ}
    (hx : 3 ≤ x) (h : (2 : ℤ)^a = 3*x + s.val) : 3 ≤ a := by
  by_contra ha
  have casesA : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases casesA with rfl | rfl | rfl <;> cases s <;> norm_num [Sign.val] at h <;> omega

private theorem short_implies_four {x : ℤ} {s : Sign} {a : ℕ}
    (hx : 5 ≤ x) (h : (2 : ℤ)^a = 3*x + s.val) : 4 ≤ a := by
  have h₃ := small_impossible (by omega : 3 ≤ x) h
  by_contra ha
  have hEq : a = 3 := by omega
  subst a
  cases s <;> norm_num [Sign.val] at h <;> omega

private theorem basic_forms {n y z : ℤ} {s sy sz : Sign} {e b c : ℕ}
    (hn : 1 < n) (hnodd : n % 2 = 1) (hyodd : y % 2 = 1)
    (hz : 1 < z) (hzodd : z % 2 = 1) (he : 2 ≤ e)
    (short : 2*y = 3*n + s.val)
    (long : (2 : ℤ)^e*z = 3*n + s.flip.val)
    (hitY : (2 : ℤ)^b = 3*y + sy.val)
    (hitZ : (2 : ℤ)^c = 3*z + sz.val) :
    5 ≤ b+1 ∧
      (9*n+1 = (2 : ℤ)^(b+1) ∨ 9*n-1 = (2 : ℤ)^(b+1) ∨
       9*n+5 = (2 : ℤ)^(b+1) ∨ 9*n-5 = (2 : ℤ)^(b+1)) := by
  have hy : 5 ≤ y := by cases s <;> simp [Sign.val] at short <;> omega
  have hb : 4 ≤ b := short_implies_four hy hitY
  have hc : 3 ≤ c := small_impossible (by omega) hitZ
  refine ⟨by omega, ?_⟩
  have pB := pow_split (a := b+1) (m := 5) (by omega)
  have pC := pow_split (a := e+c) (m := 5) (by omega)
  norm_num at pB pC
  have combine : (2 : ℤ)^(b+1) - 2^(e+c) = 6*s.val + 2*sy.val - 2^e*sz.val := by
    calc
      _ = 2*(3*y+sy.val) - ((2 : ℤ)^e*(3*z+sz.val)) := by
        rw [pow_succ, pow_add, hitY, hitZ]
        ring
      _ = (3*(2*y)+2*sy.val) - (3*((2 : ℤ)^e*z)+(2 : ℤ)^e*sz.val) := by ring
      _ = _ := by
        rw [short, long]
        cases s <;> simp [Sign.val, Sign.flip] <;> ring
  have he₄ : e < 4 := by
    by_contra hof
    have pE := pow_split (a := e) (m := 4) (by omega)
    norm_num at pE
    rw [pB, pC, pE] at combine
    cases s <;> cases sy <;> cases sz <;> norm_num [Sign.val] at combine <;> omega
  have powY : (2 : ℤ)^(b+1) = 2 * (3*y+sy.val) := by rw [pow_succ, hitY, mul_comm]
  rw [pB, pC] at combine
  have heCases : e = 2 ∨ e = 3 := by omega
  rcases heCases with rfl | rfl <;> cases s <;> cases sy <;> cases sz <;>
    norm_num [Sign.val] at short powY combine <;>
    first
    | exact Or.inl (by omega)
    | exact Or.inr (Or.inl (by omega))
    | exact Or.inr (Or.inr (Or.inl (by omega)))
    | exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem two_power_mod_nine (a : ℕ) : (2 : ℤ)^a % 9 = (2 : ℤ)^(a%6) % 9 := by
  have base (k : ℕ) : (64 : ℤ)^k % 9 = 1 := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [pow_succ, Int.mul_emod, ih]
      decide
  have splitA : a = 6*(a/6)+a%6 := by omega
  calc
    (2 : ℤ)^a % 9 = (2 : ℤ)^(6*(a/6)+a%6) % 9 := congrArg (fun t : ℕ => (2 : ℤ)^t % 9) splitA
    _ = _ := by
      rw [pow_add, pow_mul, Int.mul_emod]
      norm_num [base]

private theorem exponent_remainders (n : ℤ) (a : ℕ) :
    (9*n+1 = (2 : ℤ)^a → a%6 = 0) ∧
    (9*n-1 = (2 : ℤ)^a → a%6 = 3) ∧
    (9*n+5 = (2 : ℤ)^a → a%6 = 5) ∧
    (9*n-5 = (2 : ℤ)^a → a%6 = 2) := by
  have h := two_power_mod_nine a
  have casesA : a%6 = 0 ∨ a%6 = 1 ∨ a%6 = 2 ∨
      a%6 = 3 ∨ a%6 = 4 ∨ a%6 = 5 := by omega
  rcases casesA with ha|ha|ha|ha|ha|ha <;> rw [ha] at h ⊢ <;> norm_num at h ⊢ <;>
    (repeat' constructor) <;> intro hc <;> omega

private theorem families_of_basic {n : ℤ} {a : ℕ}
    (hn : n ≠ 3) (ha : 5 ≤ a)
    (h : 9*n+1 = (2 : ℤ)^a ∨ 9*n-1 = (2 : ℤ)^a ∨
         9*n+5 = (2 : ℤ)^a ∨ 9*n-5 = (2 : ℤ)^a) : Families n := by
  obtain ⟨rem₁, rem₂, rem₃, rem₄⟩ := exponent_remainders n a
  rcases h with h | h | h | h
  · have rem := rem₁ h
    have eq : 6*(a/6) = a := by omega
    exact Or.inl ⟨a/6, by omega, by rwa [eq]⟩
  · have rem := rem₂ h
    have eq : 6*(a/6)+3 = a := by omega
    exact Or.inr (Or.inl ⟨a/6, by omega, by rwa [eq]⟩)
  · have rem := rem₃ h
    have large : a ≠ 5 := by
      intro bad
      rw [bad] at h
      norm_num at h
      -- This exponent would give n = 3, whose minus move hits 1.
      omega
    have eq : 6*(a/6)+5 = a := by omega
    exact Or.inr (Or.inr (Or.inl ⟨a/6, by omega, by rwa [eq]⟩))
  · have rem := rem₄ h
    have eq : 6*(a/6)+2 = a := by omega
    exact Or.inr (Or.inr (Or.inr ⟨a/6, by omega, by rwa [eq]⟩))

theorem families_of_loses {n : ℤ} (h : LosesInTwo n) : Families n := by
  obtain ⟨hn, hnodd, moves⟩ := h
  obtain ⟨u, ⟨_, uodd, a, ha, hplus⟩, hu, _, su, _, _, b, _, winu⟩ := moves .plus
  obtain ⟨v, ⟨_, vodd, d, hd, hminus⟩, hv, _, sv, _, _, c, _, winv⟩ := moves .minus
  simp only [Sign.val, mul_one] at hplus hminus winu winv
  have n_ne_three : n ≠ 3 := by
    intro bad
    have h₁ : Move .minus n 1 := by
      subst n
      exact ⟨by decide, by decide, 3, by decide, by decide⟩
    have h₂ : Move .minus n v := ⟨by omega, vodd, d, hd, hminus⟩
    have := move_unique h₁ h₂
    omega
  have short : a = 1 ∨ d = 1 := by
    by_contra hnone
    have pa := pow_split (a := a) (m := 2) (by omega)
    have pd := pow_split (a := d) (m := 2) (by omega)
    norm_num at pa pd
    rw [pa, mul_assoc] at hplus
    rw [pd, mul_assoc] at hminus
    omega
  rcases short with rfl | rfl
  · norm_num at hplus
    have long : 2 ≤ d := by
      by_contra hnolong
      have heq : d = 1 := by omega
      rw [heq] at hminus
      norm_num at hminus
      omega
    obtain ⟨hb, result⟩ := basic_forms (s := .plus) hn hnodd uodd hv vodd long hplus hminus winu winv
    exact families_of_basic n_ne_three hb result
  · norm_num at hminus
    have long : 2 ≤ a := by
      by_contra hnolong
      have heq : a = 1 := by omega
      rw [heq] at hplus
      norm_num at hplus
      omega
    obtain ⟨hc, result⟩ := basic_forms (s := .minus) hn hnodd vodd hu uodd long hminus hplus winv winu
    exact families_of_basic n_ne_three hc result

theorem loses_in_two_iff_families (n : ℤ) : LosesInTwo n ↔ Families n :=
  ⟨families_of_loses, loses_of_families⟩

theorem explicit_starts (k : ℕ) (hk : 1 ≤ k) :
    LosesInTwo (((2 : ℤ)^(6*k)-1)/9) ∧
    LosesInTwo (((2 : ℤ)^(6*k+3)+1)/9) ∧
    LosesInTwo (((2 : ℤ)^(6*k+5)-5)/9) ∧
    LosesInTwo (((2 : ℤ)^(6*k+2)+5)/9) := by
  have mod₀ := two_power_mod_nine (6*k)
  have mod₃ := two_power_mod_nine (6*k+3)
  have mod₅ := two_power_mod_nine (6*k+5)
  have mod₂ := two_power_mod_nine (6*k+2)
  rw [show (6*k)%6 = 0 by omega] at mod₀
  rw [show (6*k+3)%6 = 3 by omega] at mod₃
  rw [show (6*k+5)%6 = 5 by omega] at mod₅
  rw [show (6*k+2)%6 = 2 by omega] at mod₂
  norm_num at mod₀ mod₃ mod₅ mod₂
  exact ⟨
    loses_of_families (Or.inl ⟨k, hk, by omega⟩),
    loses_of_families (Or.inr (Or.inl ⟨k, hk, by omega⟩)),
    loses_of_families (Or.inr (Or.inr (Or.inl ⟨k, hk, by omega⟩))),
    loses_of_families (Or.inr (Or.inr (Or.inr ⟨k, hk, by omega⟩)))⟩

/-- Every displayed closed-form family is unbounded and has no repeated starts. -/
theorem strictMono_starts (r : ℕ) (offset : ℤ) :
    StrictMono (fun k : ℕ => ((2 : ℤ)^(6*k+r)+offset)/9) := by
  intro a b hab
  change ((2 : ℤ)^(6*a+r)+offset)/9 < ((2 : ℤ)^(6*b+r)+offset)/9
  have large : (2 : ℤ)^((6*a+r)+6) ≤ (2 : ℤ)^(6*b+r) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  rw [pow_add] at large
  norm_num at large
  have positive := two_pow_pos (6*a+r)
  omega

end Althofer
