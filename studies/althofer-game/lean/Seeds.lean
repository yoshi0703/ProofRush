import GameTwo
import Mathlib.Data.Int.ModEq

/-! Every residue modulo a power of three contains arbitrarily large starts
from the first two-ply losing family. -/
namespace Althofer

/-- The normalized increment of the seed power is 1 modulo 3. -/
theorem seed_period_coefficient (h : ℕ) :
    ∃ d : ℤ, (64 : ℤ)^((3 : ℕ)^h) = 1 + 9*(3 : ℤ)^h + 27*(3 : ℤ)^h*d := by
  induction h with
  | zero => exact ⟨2, by norm_num⟩
  | succ h ih =>
    obtain ⟨d, previous⟩ := ih
    let P := (3 : ℤ)^h
    refine ⟨d + 3*P*(1+3*d)^2 + 9*P^2*(1+3*d)^3, ?_⟩
    rw [show (3 : ℕ)^(h+1) = (3 : ℕ)^h*3 by rw [pow_succ], pow_mul, previous]
    rw [show (3 : ℤ)^(h+1) = (3 : ℤ)^h*3 by rw [pow_succ]]
    dsimp only [P]
    ring

private theorem mul_seed_expression (p b u k v : ℤ) :
    (1 + 9*(b+p*u))*(1 + 9*p*k + 27*p*v) =
      1 + 9*(b+p*(u+k+3*v+9*(b+p*u)*(k+3*v))) := by
  ring

/-- Adding \(k\) periods changes only the next base-three digit, by \(k\). -/
theorem seed_period_multiple (h k : ℕ) :
    ∃ v : ℤ, (64 : ℤ)^((3 : ℕ)^h*k) =
      1 + 9*(3 : ℤ)^h*(k : ℤ) + 27*(3 : ℤ)^h*v := by
  obtain ⟨d,d_eq⟩ := seed_period_coefficient h
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨v,v_eq⟩ := ih
    let p := (3 : ℤ)^h
    refine ⟨v+d+3*p*((k : ℤ)+3*v)*(1+3*d), ?_⟩
    rw [Nat.mul_succ, pow_add, v_eq, d_eq]
    simp only [Nat.cast_succ, p]
    ring

/-- A seed exponent with any prescribed residue, allowing exponent zero
for this intermediate arithmetic lemma. -/
theorem seed_congruence (h : ℕ) (b : ℤ) :
    ∃ m : ℕ, ∃ u : ℤ, (64 : ℤ)^m = 1 + 9*(b+(3 : ℤ)^h*u) := by
  induction h with
  | zero => exact ⟨0, -b, by simp⟩
  | succ h ih =>
    obtain ⟨m,u,previous⟩ := ih
    let k : ℕ := ((-u)%3).toNat
    have digit : (k : ℤ) = (-u)%3 := Int.toNat_of_nonneg (by omega)
    have divided : u+(k : ℤ) = 3*((u+(k : ℤ))/3) := by omega
    obtain ⟨v,v_eq⟩ := seed_period_multiple h k
    let p := (3 : ℤ)^h
    refine ⟨m+(3 : ℕ)^h*k,
      (u+(k : ℤ))/3 + v + 3*(b+p*u)*((k : ℤ)+3*v), ?_⟩
    rw [pow_add, previous, v_eq, mul_seed_expression, pow_succ]
    dsimp only [p]
    have factor :
        u+(k : ℤ)+3*v+9*(b+(3 : ℤ)^h*u)*((k : ℤ)+3*v) =
          3*((u+(k : ℤ))/3+v+3*(b+(3 : ℤ)^h*u)*((k : ℤ)+3*v)) := by
      calc
        _ = (u+(k : ℤ)) + (3*v+9*(b+(3 : ℤ)^h*u)*((k : ℤ)+3*v)) := by ring
        _ = _ := by
          -- Use the division identity once without rewriting its own argument.
          have rearranged := congrArg
            (fun z : ℤ => z + (3*v+9*(b+(3 : ℤ)^h*u)*((k : ℤ)+3*v))) divided
          exact rearranged.trans (by ring)
    rw [factor]
    ring

private theorem seed_power_lower (m : ℕ) :
    1 + 63*(m : ℤ) ≤ (64 : ℤ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have positive : (0 : ℤ) ≤ (m : ℤ) := by omega
    calc
      _ ≤ 64*(1+63*(m : ℤ)) := by simp only [Nat.cast_succ]; omega
      _ ≤ 64*(64 : ℤ)^m := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ, mul_comm]

private theorem seed_power_base (m : ℕ) : (64 : ℤ)^m = (2 : ℤ)^(6*m) := by
  rw [pow_mul]
  norm_num

/-- Explicit arithmetic witness in every residue class with any prescribed
lower bound.  The losing assertion is the literal predicate from GameTwo. -/
theorem seed_density_witness (h : ℕ) (b N : ℤ) :
    ∃ (g : ℤ) (m : ℕ) (v : ℤ), N < g ∧ 1 ≤ m ∧
      g = b+(3 : ℤ)^h*v ∧ 9*g+1 = (64 : ℤ)^m ∧ LosesInTwo g := by
  obtain ⟨a,u,a_eq⟩ := seed_congruence h b
  let k := N.toNat+1
  let m := a+(3 : ℕ)^h*k
  have lower_k : N < (k : ℤ) := by dsimp [k]; omega
  have k_pos : 1 ≤ k := by dsimp [k]; omega
  have lower_m : k ≤ m := by
    have positive : (0 : ℕ) < (3 : ℕ)^h := Nat.pow_pos (by decide)
    have := Nat.le_mul_of_pos_left k positive
    dsimp only [m]
    omega
  obtain ⟨w,w_eq⟩ := seed_period_multiple h k
  let p := (3 : ℤ)^h
  let v := u+(k : ℤ)+3*w+9*(b+p*u)*((k : ℤ)+3*w)
  let g := b+p*v
  have g_pow : 9*g+1 = (64 : ℤ)^m := by
    unfold m
    rw [pow_add, a_eq, w_eq, mul_seed_expression]
    dsimp only [g, v, p]
    ring
  have g_lower : N < g := by
    have bound := seed_power_lower m
    rw [←g_pow] at bound
    omega
  refine ⟨g,m,v,g_lower,by omega,rfl,g_pow,?_⟩
  apply loses_of_families
  exact Or.inl ⟨m,by omega,g_pow.trans (seed_power_base m)⟩

theorem seed_density (h : ℕ) (b N : ℤ) :
    ∃ g : ℤ, N < g ∧ Int.ModEq ((3 : ℤ)^h) g b ∧ LosesInTwo g := by
  obtain ⟨g,_,v,hN,_,g_eq,_,loses⟩ := seed_density_witness h b N
  refine ⟨g,hN,?_,loses⟩
  change g % (3 : ℤ)^h = b % (3 : ℤ)^h
  rw [g_eq, Int.add_mul_emod_self_left]

end Althofer
