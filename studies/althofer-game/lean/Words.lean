import Seeds
import Diamonds
import Mathlib.Data.List.Induction

/-! Every finite list of inverse diamonds can be realized from a two-ply
losing seed and can end arbitrarily high in a prescribed residue class. -/
namespace Althofer

inductive InverseFamily
  | eight | sixteen
  deriving DecidableEq

/-- The two inverse families, each with either choice of sign. -/
structure InverseLetter where
  family : InverseFamily
  sign : Sign
  deriving DecidableEq

def InverseLetter.exponent (letter : InverseLetter) : ℕ :=
  match letter.family with
  | .eight => 3
  | .sixteen => 4

def InverseLetter.shift (letter : InverseLetter) : ℤ :=
  match letter.family with
  | .eight => letter.sign.val
  | .sixteen => 5*letter.sign.val

def InverseLetter.Step (letter : InverseLetter) (old new : ℤ) : Prop :=
  9*new = (2 : ℤ)^letter.exponent*old-letter.shift

theorem InverseLetter.lifts_loss {k : ℕ} {old new : ℤ} (letter : InverseLetter)
    (step : letter.Step old new) (loss : LosesBy k old) : LosesBy (k+2) new := by
  rcases letter with ⟨family,sign⟩
  cases family
  · apply diamond_eight sign _ loss
    simpa [InverseLetter.Step, InverseLetter.exponent, InverseLetter.shift] using step
  · apply diamond_sixteen sign _ loss
    simpa [InverseLetter.Step, InverseLetter.exponent, InverseLetter.shift] using step

/-- A left-to-right list of inverse transitions on actual integer positions. -/
inductive InversePath (seed : ℤ) : List InverseLetter → ℤ → Prop
  | empty : InversePath seed [] seed
  | snoc {word : List InverseLetter} {letter : InverseLetter} {old new : ℤ} :
      InversePath seed word old → letter.Step old new → Playable new →
        InversePath seed (word ++ [letter]) new

theorem InversePath.lifts_loss {seed finish : ℤ} {word : List InverseLetter} {k : ℕ}
    (path : InversePath seed word finish) (loss : LosesBy k seed) :
    LosesBy (k+2*word.length) finish := by
  induction path with
  | empty => simpa using loss
  | @snoc word letter old new _ step _ ih =>
    have result := letter.lifts_loss step ih
    have budget : (k+2*word.length)+2 = k+2*(word ++ [letter]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    exact budget ▸ result

private theorem three_power_odd (h : ℕ) : (3 : ℤ)^h % 2 = 1 := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [pow_succ, Int.mul_emod, ih]
    decide

/-- Inverting multiplication by \(2^r\) modulo \(3^{h+d}\) pulls an arbitrary
affine target residue back through a division by \(3^d\). -/
private theorem affine_preimage (h d r : ℕ) (b shift : ℤ) :
    ∃ c : ℤ, ∀ g : ℤ, Int.ModEq ((3 : ℤ)^(h+d)) g c →
      ∃ n : ℤ, Int.ModEq ((3 : ℤ)^h) n b ∧
        (3 : ℤ)^d*n = (2 : ℤ)^r*g-shift := by
  let M := (3 : ℤ)^(h+d)
  let P := (3 : ℤ)^h
  let D := (3 : ℤ)^d
  let A := (2 : ℤ)^r
  let target := D*b+shift
  let z := (M+1)/2
  have odd : M%2 = 1 := three_power_odd (h+d)
  have hz : 2*z = M+1 := by dsimp only [z]; omega
  have unit : Int.ModEq M (2*z) 1 := by
    change (2*z)%M = (1 : ℤ)%M
    rw [hz, Int.add_emod]
    simp
  have inverse : Int.ModEq M (A*z^r) 1 := by
    simpa only [A, mul_pow, one_pow] using unit.pow r
  refine ⟨z^r*target, ?_⟩
  intro g congruent
  have scaled : Int.ModEq M (A*g) target := by
    apply (congruent.mul_left A).trans
    simpa only [mul_assoc, one_mul] using inverse.mul_right target
  obtain ⟨v,v_eq⟩ := scaled.dvd
  have product_modulus : M = P*D := by
    dsimp only [M,P,D]
    rw [pow_add]
  refine ⟨b+P*(-v), ?_, ?_⟩
  · change (b+P*(-v))%P = b%P
    rw [Int.add_mul_emod_self_left]
  · change D*(b+P*(-v)) = A*g-shift
    change D*b+shift-A*g = M*v at v_eq
    calc
      _ = D*b-M*v := by rw [product_modulus]; ring
      _ = _ := by rw [←v_eq]; ring

private theorem affine_above {d r : ℕ} {g n N shift : ℤ}
    (large : max 0 ((3 : ℤ)^d*N+shift) < g)
    (eq : (3 : ℤ)^d*n = (2 : ℤ)^r*g-shift) : N < n := by
  have g_pos := lt_of_le_of_lt (le_max_left 0 ((3 : ℤ)^d*N+shift)) large
  have g_bound := lt_of_le_of_lt (le_max_right 0 ((3 : ℤ)^d*N+shift)) large
  have A_pos : (0 : ℤ) < 2^r := pow_pos (by decide) _
  have D_pos : (0 : ℤ) < 3^d := pow_pos (by decide) _
  have scaled : (1 : ℤ)*g ≤ (2 : ℤ)^r*g :=
    mul_le_mul_of_nonneg_right (by omega) g_pos.le
  apply Int.lt_of_mul_lt_mul_left (a := (3 : ℤ)^d) _ D_pos.le
  omega

/-- Every finite prescribed word can end beyond any bound in any \(3\)-power
residue, along an actual path from the first two-ply losing family. -/
theorem inverse_word_density (word : List InverseLetter) (h : ℕ) (b N : ℤ) :
    ∃ (seed n : ℤ) (m : ℕ), 1 ≤ m ∧ 9*seed+1 = (64 : ℤ)^m ∧
      LosesInTwo seed ∧ InversePath seed word n ∧ N<n ∧
      Int.ModEq ((3 : ℤ)^h) n b ∧ LosesBy (2+2*word.length) n := by
  induction word using List.reverseRecOn generalizing h b N with
  | nil =>
    obtain ⟨seed,m,v,large,m_pos,seed_eq,seed_pow,seed_loss⟩ := seed_density_witness h b N
    have congruent : Int.ModEq ((3 : ℤ)^h) seed b := by
      change seed%(3 : ℤ)^h = b%(3 : ℤ)^h
      rw [seed_eq, Int.add_mul_emod_self_left]
    exact ⟨seed,seed,m,m_pos,seed_pow,seed_loss,.empty,large,congruent,
      (losesBy_two_iff seed).mpr seed_loss⟩
  | append_singleton word letter ih =>
    obtain ⟨c,preimage⟩ := affine_preimage h 2 letter.exponent b letter.shift
    obtain ⟨seed,g,m,m_pos,seed_pow,seed_loss,path,large,congruent,_⟩ :=
      ih (h+2) c (max 0 ((3 : ℤ)^2*N+letter.shift))
    obtain ⟨n,n_congruent,eq⟩ := preimage g congruent
    have step : letter.Step g n := by
      simpa only [InverseLetter.Step, show (3 : ℤ)^2 = 9 by decide] using eq
    have tail := letter.lifts_loss step (path.lifts_loss ((losesBy_two_iff seed).mpr seed_loss))
    have actual : InversePath seed (word ++ [letter]) n :=
      .snoc path step (losesBy_playable tail)
    exact ⟨seed,n,m,m_pos,seed_pow,seed_loss,actual,affine_above large eq,n_congruent,
      actual.lifts_loss ((losesBy_two_iff seed).mpr seed_loss)⟩

/-- The inverse word can be followed by a winning predecessor via the plus
move, while prescribing the final residue and an arbitrary lower bound. -/
theorem inverse_word_win_density (word : List InverseLetter) (h : ℕ) (b N : ℤ) :
    ∃ (seed g n : ℤ) (m : ℕ), 1 ≤ m ∧ 9*seed+1 = (64 : ℤ)^m ∧
      LosesInTwo seed ∧ InversePath seed word g ∧ 3*n = 2*g-1 ∧ N<n ∧
      Int.ModEq ((3 : ℤ)^h) n b ∧ WinsBy ((2+2*word.length)+1) n := by
  obtain ⟨c,preimage⟩ := affine_preimage h 1 1 b 1
  obtain ⟨seed,g,m,m_pos,seed_pow,seed_loss,path,large,congruent,loss⟩ :=
    inverse_word_density word (h+1) c (max 0 ((3 : ℤ)^1*N+1))
  obtain ⟨n,n_congruent,eq⟩ := preimage g congruent
  have step : 3*n = 2*g-1 := by simpa only [pow_one] using eq
  exact ⟨seed,g,n,m,m_pos,seed_pow,seed_loss,path,step,affine_above large eq,n_congruent,
    win_from_loss .plus step loss⟩

end Althofer
