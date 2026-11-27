import Problems.Erdos030.PeriodicDFT
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Universal Power-Saving 3-AP-Free Support Bound (Theorem T2-B)

Completely elementary proof (no Galois field algebra, no Kelley–Meka, no measure theory)
of uniform Fourier flatness and the universal `O(N^(11/12))` 3-AP-free support bound for
EVERY dense fractional Sidon measure on `Finset.range N` (and in particular every dense
Sidon set and every dense witness of the nonlinear 3-AP-free relaxation `M_3AP(N)`):

1. `dirichlet_kernel_lower_bound` and `dirichlet_kernel_upper_bound`:
   elementary chord-length bounds on `‖∑ s < H, ω^(ξ * s)‖` on `ℤ / Mℤ`.
2. `box_energy_le` and `fractional_sidon_sum_le_two_sqrt`:
   exact box-kernel variance identity and the universal Lindström upper bound `S₁ ≤ 2√N + 1`.
3. `small_freq_eta_bound`:
   uniform `O(N^(5/12))` bound on `‖dft (2*N+1) η ξ‖` for small frequencies
   `2 * H₁ * min ξ (M - ξ) ≤ M`.
4. `large_freq_eta_bound`:
   Two-Frequency Lindström inequality giving an `O(N^(5/12))` bound for large frequencies
   `M < 2 * H₁ * min ξ (M - ξ)`.
5. `universal_3ap_free_superset_from_U`:
   exact finite-DFT 3-AP counting bound `|T| ≤ (2 * N / S₁) * U + √(2 * N)` on `ℤ / (2N+1)ℤ`.
6. `universal_3ap_free_superset_asymptotic`:
   for every `C₀ : ℝ`, eventually for all `N`, any dense fractional Sidon measure with
   `∑ μ ≥ √N - C₀ N^(1/4)` forces every `T ⊆ range N` forming zero nontrivial linear 3-APs
   `t₁ + t₂ = 2x` (`t₁ ≠ t₂`, `μ x > 0`) to satisfy `|T| ≤ 66 * N^(11/12)`.
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-! ### Part 1: Dirichlet Kernel Lower & Upper Bounds -/

private lemma norm_exp_I_sub_one_eq_two_sin {α : ℝ} (h0 : 0 ≤ α) (h2pi : α ≤ 2 * Real.pi) :
    ‖Complex.exp ((α : ℂ) * Complex.I) - 1‖ = 2 * Real.sin (α / 2) := by
  rw [Complex.exp_mul_I]
  have hre : (Complex.cos (α : ℂ) + Complex.sin (α : ℂ) * Complex.I - 1).re =
      Real.cos α - 1 := by
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him : (Complex.cos (α : ℂ) + Complex.sin (α : ℂ) * Complex.I - 1).im =
      Real.sin α := by
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsq : ‖Complex.cos (α : ℂ) + Complex.sin (α : ℂ) * Complex.I - 1‖ ^ 2 =
      (2 * Real.sin (α / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have hcos2 : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
      have h := Real.cos_two_mul' (α / 2)
      have hsc := Real.sin_sq_add_cos_sq (α / 2)
      rw [show 2 * (α / 2) = α by ring] at h
      linarith
    have hsc2 := Real.sin_sq_add_cos_sq α
    nlinarith
  have hsin_nn : 0 ≤ 2 * Real.sin (α / 2) :=
    mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  nlinarith [norm_nonneg (Complex.cos (α : ℂ) + Complex.sin (α : ℂ) * Complex.I - 1)]

/-- Lower bound on the Dirichlet kernel on `ℤ / Mℤ` for small frequencies:
for `M ≥ 1, H ≥ 1, ξ < M` with `2 * H * min ξ (M - ξ) ≤ M`,
`(2 / π) * H ≤ ‖∑ s ∈ range H, ω^(ξ * s)‖`. -/
lemma dirichlet_kernel_lower_bound {M H ξ : ℕ} (hM : 0 < M) (hH : 1 ≤ H) (hξ : ξ < M)
    (hsmall : 2 * H * min ξ (M - ξ) ≤ M) :
    (2 / Real.pi) * (H : ℝ) ≤ ‖∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)‖ := by
  by_cases hξ0 : ξ = 0
  · subst hξ0
    have hsum : ∑ s ∈ Finset.range H, (rootOfUnity M) ^ (0 * s) = (H : ℂ) := by
      simp
    rw [hsum, Complex.norm_natCast]
    have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hHnn : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
    have hdiv : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr hpi
    nlinarith
  · have hξ1 : 1 ≤ ξ := Nat.pos_of_ne_zero hξ0
    set k : ℕ := min ξ (M - ξ)
    have hk1 : 1 ≤ k := by dsimp only [k]; omega
    have hkM : k < M := by dsimp only [k]; omega
    have h2Hk : 2 * H * k ≤ M := hsmall
    have hnorm_k :
        ‖∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)‖ =
        ‖∑ s ∈ Finset.range H, ((rootOfUnity M) ^ k) ^ s‖ := by
      have hpow_k : ∀ s : ℕ, (rootOfUnity M) ^ (k * s) = ((rootOfUnity M) ^ k) ^ s :=
        fun s => pow_mul (rootOfUnity M) k s
      rw [← Finset.sum_congr rfl fun s _ => hpow_k s]
      by_cases hle : ξ ≤ M - ξ
      · have hk : k = ξ := min_eq_left hle
        rw [hk]
      · have hk : k = M - ξ := min_eq_right (by omega)
        rw [hk]
        have hconj :
            ∑ s ∈ Finset.range H, (rootOfUnity M) ^ ((M - ξ) * s) =
            starRingEnd ℂ (∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun s _ => rootOfUnity_pow_sub_eq_star hM hξ.le s
        rw [hconj, Complex.norm_conj]
    rw [hnorm_k]
    have hne : (rootOfUnity M) ^ k ≠ 1 := by
      intro h1
      have hdvd := (rootOfUnity_pow_eq_one_iff_dvd hM k).mp h1
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, norm_div]
    have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
    have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
    -- Numerator: `‖(ω^k)^H - 1‖ = 2 sin(π k H / M) ≥ 4 k H / M`
    set α₁ : ℝ := 2 * Real.pi * ((k * H : ℕ) : ℝ) / (M : ℝ)
    have hnum_exp : ((rootOfUnity M) ^ k) ^ H = Complex.exp ((α₁ : ℂ) * Complex.I) := by
      rw [← pow_mul]
      unfold rootOfUnity
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp only [α₁]
      push_cast; ring
    have hα₁_nn : 0 ≤ α₁ := by dsimp only [α₁]; positivity
    have hα₁_le_pi : α₁ ≤ Real.pi := by
      dsimp only [α₁]
      rw [div_le_iff₀ hMpos]
      have h2kHR : (2 : ℝ) * ((k * H : ℕ) : ℝ) ≤ (M : ℝ) := by
        have : 2 * (k * H) ≤ M := by nlinarith
        exact_mod_cast this
      nlinarith [Real.pi_pos]
    have hnum_eq : ‖((rootOfUnity M) ^ k) ^ H - 1‖ = 2 * Real.sin (α₁ / 2) := by
      rw [hnum_exp]
      exact norm_exp_I_sub_one_eq_two_sin hα₁_nn (by linarith [Real.pi_pos])
    have hnum_ge : 4 * (k : ℝ) * (H : ℝ) / (M : ℝ) ≤ ‖((rootOfUnity M) ^ k) ^ H - 1‖ := by
      rw [hnum_eq]
      have hj := Real.mul_le_sin (x := α₁ / 2) (by linarith) (by linarith)
      have hsimp : 2 * (2 / Real.pi * (α₁ / 2)) = 4 * (k : ℝ) * (H : ℝ) / (M : ℝ) := by
        dsimp only [α₁]
        push_cast
        have hpi := Real.pi_ne_zero
        field_simp
        ring
      linarith
    -- Denominator: `‖ω^k - 1‖ = 2 sin(π k / M) ≤ 2 π k / M`
    set α₂ : ℝ := 2 * Real.pi * (k : ℝ) / (M : ℝ)
    have hden_exp : (rootOfUnity M) ^ k = Complex.exp ((α₂ : ℂ) * Complex.I) := by
      unfold rootOfUnity
      rw [← Complex.exp_nat_mul]
      congr 1
      dsimp only [α₂]
      push_cast; ring
    have hα₂_nn : 0 ≤ α₂ := by dsimp only [α₂]; positivity
    have hα₂_le_pi : α₂ ≤ Real.pi := by
      dsimp only [α₂]
      rw [div_le_iff₀ hMpos]
      have h2kR : (2 : ℝ) * (k : ℝ) ≤ (M : ℝ) := by
        have : 2 * k ≤ M := by nlinarith
        exact_mod_cast this
      nlinarith [Real.pi_pos]
    have hden_eq : ‖(rootOfUnity M) ^ k - 1‖ = 2 * Real.sin (α₂ / 2) := by
      rw [hden_exp]
      exact norm_exp_I_sub_one_eq_two_sin hα₂_nn (by linarith [Real.pi_pos])
    have hden_le : ‖(rootOfUnity M) ^ k - 1‖ ≤ 2 * Real.pi * (k : ℝ) / (M : ℝ) := by
      rw [hden_eq]
      have hsin := Real.sin_le (show 0 ≤ α₂ / 2 by linarith)
      dsimp only [α₂] at hsin ⊢
      linarith
    have hden_pos : 0 < ‖(rootOfUnity M) ^ k - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hfrac :
        (4 * (k : ℝ) * (H : ℝ) / (M : ℝ)) / (2 * Real.pi * (k : ℝ) / (M : ℝ)) =
        (2 / Real.pi) * (H : ℝ) := by
      have hpi := Real.pi_ne_zero
      field_simp [hpi, hMpos.ne', hkpos.ne']
      ring
    rw [← hfrac]
    calc (4 * (k : ℝ) * (H : ℝ) / (M : ℝ)) / (2 * Real.pi * (k : ℝ) / (M : ℝ))
        ≤ (4 * (k : ℝ) * (H : ℝ) / (M : ℝ)) / ‖(rootOfUnity M) ^ k - 1‖ :=
          div_le_div_of_nonneg_left (by positivity) hden_pos hden_le
      _ ≤ ‖((rootOfUnity M) ^ k) ^ H - 1‖ / ‖(rootOfUnity M) ^ k - 1‖ :=
          div_le_div_of_nonneg_right hnum_ge hden_pos.le

/-- Upper bound on the Dirichlet kernel on `ℤ / Mℤ` for any `H : ℕ` and `1 ≤ ξ < M`:
`‖∑ s ∈ range H, ω^(ξ * s)‖ ≤ M / (2 * min ξ (M - ξ))`. -/
lemma dirichlet_kernel_upper_bound {M ξ : ℕ} (hM : 0 < M) (hξ1 : 1 ≤ ξ) (hξM : ξ < M) (H : ℕ) :
    ‖∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)‖ ≤
      (M : ℝ) / (2 * ((min ξ (M - ξ) : ℕ) : ℝ)) := by
  have hpow : ∀ s : ℕ, (rootOfUnity M) ^ (ξ * s) = ((rootOfUnity M) ^ ξ) ^ s :=
    fun s => pow_mul (rootOfUnity M) ξ s
  rw [Finset.sum_congr rfl fun s _ => hpow s]
  have hne : (rootOfUnity M) ^ ξ ≠ 1 := by
    intro h1
    have hdvd := (rootOfUnity_pow_eq_one_iff_dvd hM ξ).mp h1
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖((rootOfUnity M) ^ ξ) ^ H - 1‖ ≤ 2 := by
    calc ‖((rootOfUnity M) ^ ξ) ^ H - 1‖
        ≤ ‖((rootOfUnity M) ^ ξ) ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_rootOfUnity_pow, one_pow, norm_one]; norm_num
  have hden_ge := norm_rootOfUnity_sub_one_ge hM hξ1 hξM
  have hk_pos : (0 : ℝ) < ((min ξ (M - ξ) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < min ξ (M - ξ) by omega)
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hlb_pos : (0 : ℝ) < 4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ) := by positivity
  have hdiv : ‖((rootOfUnity M) ^ ξ) ^ H - 1‖ / ‖(rootOfUnity M) ^ ξ - 1‖ ≤
      2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) := by
    calc ‖((rootOfUnity M) ^ ξ) ^ H - 1‖ / ‖(rootOfUnity M) ^ ξ - 1‖
        ≤ 2 / ‖(rootOfUnity M) ^ ξ - 1‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ 2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) hlb_pos hden_ge
  have hsimp : 2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) =
      (M : ℝ) / (2 * ((min ξ (M - ξ) : ℕ) : ℝ)) := by
    field_simp; ring
  linarith

/-! ### Part 2: Window Overlap Identity, Box Energy Bound, and Lindström `S₁ ≤ 2√N + 1` -/

/-- Exact count of windows `x < N + H - 1` containing both `y` and `z` (for `y, z < N, H ≥ 1`). -/
private lemma card_window_overlap {N H y z : ℕ} (hH : 1 ≤ H) (hy : y < N) (hz : z < N) :
    ((Finset.range (N + H - 1)).filter (fun x => (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H))).card =
      if y ≤ z then (if z - y < H then H - (z - y) else 0)
      else (if y - z < H then H - (y - z) else 0) := by
  have heq : (Finset.range (N + H - 1)).filter
      (fun x => (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H)) =
      Finset.Ico (max y z) (min (y + H) (z + H)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, max_le_iff, lt_min_iff]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨by omega, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [heq, Nat.card_Ico]
  by_cases hyz : y ≤ z
  · rw [if_pos hyz, max_eq_right hyz, min_eq_left (by omega)]
    by_cases hd : z - y < H
    · rw [if_pos hd]; omega
    · rw [if_neg hd]; omega
  · rw [if_neg hyz, max_eq_left (by omega), min_eq_right (by omega)]
    by_cases hd : y - z < H
    · rw [if_pos hd]; omega
    · rw [if_neg hd]; omega

/-- Splitting a symmetric double sum weighted by window overlap into diagonal and lags `1 ≤ d < H`. -/
private lemma sum_window_overlap_split {N H : ℕ} (hH : 1 ≤ H)
    (f : ℕ → ℝ) (w : ℕ → ℝ) :
    ∑ x ∈ Finset.range (N + H - 1),
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (if (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H)
         then f y * f z * w (if y ≤ z then z - y else y - z) else 0) =
    (H : ℝ) * w 0 * (∑ y ∈ Finset.range N, (f y) ^ 2) +
    2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * w d *
      (∑ y ∈ Finset.range (N - d), f y * f (y + d)) := by
  -- Swap `x` inside `(y, z)`
  have hswap :
      ∑ x ∈ Finset.range (N + H - 1),
        ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          (if (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H)
           then f y * f z * w (if y ≤ z then z - y else y - z) else 0) =
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (f y * f z * w (if y ≤ z then z - y else y - z)) *
          (((Finset.range (N + H - 1)).filter
            (fun x => (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H))).card : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap]
  -- Split each `(y, z)` into `y = z`, `y < z`, `z < y`
  have h3way : ∀ y ∈ Finset.range N, ∀ z ∈ Finset.range N,
      (f y * f z * w (if y ≤ z then z - y else y - z)) *
        (((Finset.range (N + H - 1)).filter
          (fun x => (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H))).card : ℝ) =
      (if y = z then (H : ℝ) * w 0 * (f y) ^ 2 else 0) +
      (if y < z ∧ z - y < H then ((H - (z - y) : ℕ) : ℝ) * w (z - y) * (f y * f z) else 0) +
      (if z < y ∧ y - z < H then ((H - (y - z) : ℕ) : ℝ) * w (y - z) * (f z * f y) else 0) := by
    intro y hy z hz
    rw [Finset.mem_range] at hy hz
    rw [card_window_overlap hH hy hz]
    rcases lt_trichotomy y z with hlt | heq | hgt
    · have hle : y ≤ z := hlt.le
      have hne : y ≠ z := hlt.ne
      have hngt : ¬ z < y := by omega
      simp only [hle, ↓reduceIte, hne, hlt, true_and, hngt, false_and, zero_add, add_zero]
      split_ifs <;> ring
    · subst heq
      simp only [le_refl, ↓reduceIte, Nat.sub_self, Nat.sub_zero, show (0 : ℕ) < H by omega,
        lt_irrefl, false_and, add_zero]
      ring
    · have hnle : ¬ y ≤ z := by omega
      have hne : y ≠ z := by omega
      have hnlt : ¬ y < z := by omega
      simp only [hnle, ↓reduceIte, hne, hnlt, false_and, hgt, true_and, zero_add]
      split_ifs <;> ring
  have hrewrite :
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (f y * f z * w (if y ≤ z then z - y else y - z)) *
          (((Finset.range (N + H - 1)).filter
            (fun x => (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H))).card : ℝ) =
      (∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        if y = z then (H : ℝ) * w 0 * (f y) ^ 2 else 0) +
      (∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        if y < z ∧ z - y < H then ((H - (z - y) : ℕ) : ℝ) * w (z - y) * (f y * f z) else 0) +
      (∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        if z < y ∧ y - z < H then ((H - (y - z) : ℕ) : ℝ) * w (y - z) * (f z * f y) else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun z hz => h3way y hy z hz
  rw [hrewrite]
  have hdiag :
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (if y = z then (H : ℝ) * w 0 * (f y) ^ 2 else 0) =
      (H : ℝ) * w 0 * ∑ y ∈ Finset.range N, (f y) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.sum_ite_eq, if_pos hy]
  have hsymm :
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (if z < y ∧ y - z < H then ((H - (y - z) : ℕ) : ℝ) * w (y - z) * (f z * f y) else 0) =
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (if y < z ∧ z - y < H then ((H - (z - y) : ℕ) : ℝ) * w (z - y) * (f y * f z) else 0) := by
    rw [Finset.sum_comm]
  have hoff :
      ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
        (if y < z ∧ z - y < H then ((H - (z - y) : ℕ) : ℝ) * w (z - y) * (f y * f z) else 0) =
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * w d *
        (∑ y ∈ Finset.range (N - d), f y * f (y + d)) := by
    -- Rewrite both sides as sums over `Finset.product` / `Finset.sigma`
    have hL :
        ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          (if y < z ∧ z - y < H then ((H - (z - y) : ℕ) : ℝ) * w (z - y) * (f y * f z) else 0) =
        ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 < p.2 ∧ p.2 - p.1 < H),
          ((H - (p.2 - p.1) : ℕ) : ℝ) * w (p.2 - p.1) * (f p.1 * f p.2) := by
      rw [Finset.sum_filter, Finset.sum_product]
    have hR :
        ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * w d *
          (∑ y ∈ Finset.range (N - d), f y * f (y + d)) =
        ∑ q ∈ (Finset.Ico 1 H).sigma (fun d => Finset.range (N - d)),
          ((H - q.1 : ℕ) : ℝ) * w q.1 * (f q.2 * f (q.2 + q.1)) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => Finset.mul_sum _ _ _
    rw [hL, hR]
    refine Finset.sum_nbij (fun p => ⟨p.2 - p.1, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_sigma, Finset.mem_Ico] at hp ⊢
      omega
    · intro p₁ hp₁ p₂ hp₂ hEq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
      have h1 : p₁.2 - p₁.1 = p₂.2 - p₂.1 := congrArg Sigma.fst hEq
      have h2 : p₁.1 = p₂.1 := by simpa using (Sigma.mk.inj_iff.mp hEq).2
      exact Prod.ext h2 (by omega)
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hq
      refine ⟨(q.2, q.2 + q.1), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      dsimp only
      rw [show p.1 + (p.2 - p.1) = p.2 by omega]
  rw [hdiag, hsymm, hoff]
  ring

/-- Sum of box window averages over `range (N + H - 1)` equals `H * ∑_{y < N} f y`. -/
lemma sum_box_window {N H : ℕ} (hH : 1 ≤ H) (f : ℕ → ℝ) :
    ∑ x ∈ Finset.range (N + H - 1),
      (∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H then f y else 0) =
    (H : ℝ) * ∑ y ∈ Finset.range N, f y := by
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_range] at hy
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hfil : (Finset.range (N + H - 1)).filter (fun x => y ≤ x ∧ x < y + H) =
      Finset.Ico y (y + H) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, Nat.card_Ico]
  simp

/-- Clean proof of `2 * ∑_{1 ≤ d < H} (H - d) = H * (H - 1)` in `ℝ`. -/
private lemma two_mul_sum_sub_Ico (H : ℕ) (hH : 1 ≤ H) :
    2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) = (H : ℝ) * ((H : ℝ) - 1) := by
  have hnat : 2 * ∑ d ∈ Finset.Ico 1 H, (H - d) = H * (H - 1) := by
    have hrev : ∑ d ∈ Finset.Ico 1 H, (H - d) = ∑ k ∈ Finset.range H, k := by
      rw [← Finset.sum_range_add_sum_Ico _ hH, Finset.range_one, Finset.sum_singleton, zero_add]
      refine Finset.sum_nbij (fun d => H - d) ?_ ?_ ?_ ?_
      · intro d hd; simp only [Finset.mem_Ico] at hd ⊢; omega
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
        dsimp only at hab; omega
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_Ico] at hk
        exact ⟨H - k, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp; omega⟩
      · intro _ _; rfl
    rw [hrev, mul_comm, Finset.sum_range_id_mul_two]
  have hcast : (2 : ℝ) * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) = ((H * (H - 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hcast, Nat.cast_mul, Nat.cast_sub hH, Nat.cast_one]

/-- Exact box-kernel energy bound for any measure with linear autocorrelation `≤ 1`. -/
lemma box_energy_le {N H : ℕ} (hH : 1 ≤ H) {μ : ℕ → ℝ}
    (hac : ∀ d, 1 ≤ d → d < N → ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1) :
    ∑ x ∈ Finset.range (N + H - 1),
      (∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H then μ y else 0) ^ 2 ≤
    (H : ℝ) * (∑ y ∈ Finset.range N, (μ y) ^ 2) + (H : ℝ) * ((H : ℝ) - 1) := by
  have hsq :
      ∑ x ∈ Finset.range (N + H - 1),
        (∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H then μ y else 0) ^ 2 =
      ∑ x ∈ Finset.range (N + H - 1),
        ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          if (y ≤ x ∧ x < y + H) ∧ (z ≤ x ∧ x < z + H) then μ y * μ z * 1 else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hy : y ≤ x ∧ x < y + H <;> by_cases hz : z ≤ x ∧ x < z + H <;> simp [hy, hz]
  rw [hsq, sum_window_overlap_split hH μ (fun _ => 1)]
  have htail :
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * 1 *
        (∑ y ∈ Finset.range (N - d), μ y * μ (y + d)) ≤
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Ico] at hd
    rw [mul_one]
    have hcoeff : (0 : ℝ) ≤ ((H - d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle1 : ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1 := by
      by_cases hdN : d < N
      · exact hac d hd.1 hdN
      · have h0 : N - d = 0 := by omega
        rw [h0, Finset.range_zero, Finset.sum_empty]
        norm_num
    nlinarith
  have hsum_Hd := two_mul_sum_sub_Ico H hH
  linarith only [htail, hsum_Hd]

/-- Universal elementary Lindström bound: for every `N ≥ 1`, any fractional Sidon measure
satisfies `∑_{x < N} μ x ≤ 2 * √N + 1`. -/
lemma fractional_sidon_sum_le_two_sqrt {N : ℕ} (hN : 1 ≤ N) {μ : ℕ → ℝ}
    (hbound : ∀ x < N, 0 ≤ μ x ∧ μ x ≤ 1)
    (hac : ∀ d, 1 ≤ d → d < N → ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1) :
    ∑ x ∈ Finset.range N, μ x ≤ 2 * Real.sqrt (N : ℝ) + 1 := by
  set S₁ : ℝ := ∑ x ∈ Finset.range N, μ x
  set S₂ : ℝ := ∑ x ∈ Finset.range N, (μ x) ^ 2
  have hS₂_le : S₂ ≤ S₁ := by
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mem_range] at hx
    rcases hbound x hx with ⟨h0, h1⟩
    nlinarith
  set H : ℕ := Nat.sqrt N + 1
  have hH1 : 1 ≤ H := by omega
  have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH1
  set C : ℕ → ℝ := fun x => ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H then μ y else 0
  have hsumC : ∑ x ∈ Finset.range (N + H - 1), C x = (H : ℝ) * S₁ := sum_box_window hH1 μ
  have hCS : ((H : ℝ) * S₁) ^ 2 ≤ ((N + H - 1 : ℕ) : ℝ) * ∑ x ∈ Finset.range (N + H - 1), (C x) ^ 2 := by
    rw [← hsumC]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1)) (fun _ => (1 : ℝ)) C
    simpa [Finset.card_range] using h
  have hE : ∑ x ∈ Finset.range (N + H - 1), (C x) ^ 2 ≤
      (H : ℝ) * S₂ + (H : ℝ) * ((H : ℝ) - 1) := box_energy_le hH1 hac
  have hNH_nn : (0 : ℝ) ≤ ((N + H - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hquad : (H : ℝ) ^ 2 * S₁ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * (S₁ + ((H : ℝ) - 1))) := by
    calc (H : ℝ) ^ 2 * S₁ ^ 2 = ((H : ℝ) * S₁) ^ 2 := by ring
      _ ≤ ((N + H - 1 : ℕ) : ℝ) * ∑ x ∈ Finset.range (N + H - 1), (C x) ^ 2 := hCS
      _ ≤ ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * S₂ + (H : ℝ) * ((H : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hE hNH_nn
      _ ≤ ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * (S₁ + ((H : ℝ) - 1))) := by
          have : (H : ℝ) * S₂ + (H : ℝ) * ((H : ℝ) - 1) ≤ (H : ℝ) * (S₁ + ((H : ℝ) - 1)) := by
            nlinarith
          exact mul_le_mul_of_nonneg_left this hNH_nn
  set s : ℝ := Real.sqrt (N : ℝ)
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hsqrt_le : (Nat.sqrt N : ℝ) ≤ s := by
    have hle : (Nat.sqrt N) ^ 2 ≤ N := by
      have := Nat.sqrt_le N; nlinarith
    have hleR : ((Nat.sqrt N : ℝ)) ^ 2 ≤ s ^ 2 := by rw [hs_sq]; exact_mod_cast hle
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt N)]
  have hs_lt_H : s < (H : ℝ) := by
    have hlt : N < H ^ 2 := by
      have := Nat.lt_succ_sqrt N; dsimp only [H]; nlinarith
    have hltR : s ^ 2 < (H : ℝ) ^ 2 := by rw [hs_sq]; exact_mod_cast hlt
    nlinarith
  have hHm1 : (H : ℝ) - 1 = (Nat.sqrt N : ℝ) := by
    dsimp only [H]; push_cast; ring
  have hNH_le : ((N + H - 1 : ℕ) : ℝ) ≤ (H : ℝ) * (s + 1) := by
    have hcast : ((N + H - 1 : ℕ) : ℝ) = (N : ℝ) + ((H : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]; ring
    rw [hcast, hHm1, ← hs_sq]
    nlinarith
  have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun x hx => (hbound x (Finset.mem_range.mp hx)).1
  have hS₁_quad : S₁ ^ 2 ≤ (s + 1) * (S₁ + s) := by
    have h1 : (H : ℝ) ^ 2 * S₁ ^ 2 ≤ (H : ℝ) ^ 2 * ((s + 1) * (S₁ + s)) := by
      have hfac_nn : 0 ≤ (H : ℝ) * (S₁ + ((H : ℝ) - 1)) := by
        rw [hHm1]; positivity
      calc (H : ℝ) ^ 2 * S₁ ^ 2
          ≤ ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * (S₁ + ((H : ℝ) - 1))) := hquad
        _ ≤ ((H : ℝ) * (s + 1)) * ((H : ℝ) * (S₁ + ((H : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_right hNH_le hfac_nn
        _ ≤ ((H : ℝ) * (s + 1)) * ((H : ℝ) * (S₁ + s)) := by
            have : (H : ℝ) * (S₁ + ((H : ℝ) - 1)) ≤ (H : ℝ) * (S₁ + s) := by
              rw [hHm1]; nlinarith
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ = (H : ℝ) ^ 2 * ((s + 1) * (S₁ + s)) := by ring
    nlinarith [sq_pos_of_pos hHpos]
  -- If `S₁ > 2s + 1`, then `S₁^2 - (s+1)(S₁ + s) > s^2 ≥ 0`, contradiction.
  by_contra hgt
  push Not at hgt
  nlinarith

/-! ### Part 3: Small-Frequency Uniform Fourier Bound -/

/-- Exact `L¹` boundary error for the box convolution of the uniform measure `1_[0, N)`:
for `1 ≤ H₁ ≤ N` and `N₁ = N + H₁ - 1`,
`∑_{x < N₁} |H₁ / N₁ - L(x) / N| ≤ 3 * H₁^2 / N`. -/
private lemma box_uniform_boundary_l1 {N H₁ : ℕ} (hH₁ : 1 ≤ H₁) (hH₁N : H₁ ≤ N) :
    ∑ x ∈ Finset.range (N + H₁ - 1),
      |(H₁ : ℝ) / ((N + H₁ - 1 : ℕ) : ℝ) -
        ((∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then (1 : ℝ) else 0) / (N : ℝ))| ≤
    3 * (H₁ : ℝ) ^ 2 / (N : ℝ) := by
  set N₁ : ℕ := N + H₁ - 1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast (show 0 < N₁ by omega)
  have hH₁pos : (0 : ℝ) < (H₁ : ℝ) := Nat.cast_pos.mpr hH₁
  set L : ℕ → ℝ := fun x => ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then (1 : ℝ) else 0
  have hL_bounds : ∀ x, 0 ≤ L x ∧ L x ≤ (H₁ : ℝ) := by
    intro x
    constructor
    · exact Finset.sum_nonneg fun y _ => by split_ifs <;> norm_num
    · have hfil : L x = (((Finset.range N).filter (fun y => y ≤ x ∧ x < y + H₁)).card : ℝ) := by
        dsimp only [L]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hfil]
      have hsub : (Finset.range N).filter (fun y => y ≤ x ∧ x < y + H₁) ⊆
          Finset.Ico (x + 1 - H₁) (x + 1) := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hy ⊢
        omega
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hcard
      have hle : x + 1 - (x + 1 - H₁) ≤ H₁ := by omega
      exact_mod_cast le_trans hcard hle
  have hL_interior : ∀ x, H₁ - 1 ≤ x → x < N → L x = (H₁ : ℝ) := by
    intro x hx1 hx2
    have hfil : L x = (((Finset.range N).filter (fun y => y ≤ x ∧ x < y + H₁)).card : ℝ) := by
      dsimp only [L]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hfil]
    have heq : (Finset.range N).filter (fun y => y ≤ x ∧ x < y + H₁) =
        Finset.Ico (x + 1 - H₁) (x + 1) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [heq, Nat.card_Ico]
    exact_mod_cast (show x + 1 - (x + 1 - H₁) = H₁ by omega)
  have hbd_term : ∀ x, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| ≤ (H₁ : ℝ) / (N : ℝ) := by
    intro x
    rcases hL_bounds x with ⟨h0, h1⟩
    have hN_le_N₁ : (N : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast (show N ≤ N₁ by omega)
    have hA0 : 0 ≤ (H₁ : ℝ) / (N₁ : ℝ) := by positivity
    have hA1 : (H₁ : ℝ) / (N₁ : ℝ) ≤ (H₁ : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_left hH₁pos.le hNpos hN_le_N₁
    have hB0 : 0 ≤ L x / (N : ℝ) := div_nonneg h0 hNpos.le
    have hB1 : L x / (N : ℝ) ≤ (H₁ : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right h1 hNpos.le
    rw [abs_le]
    constructor <;> linarith
  -- Split `range N₁` into `range (H₁ - 1)`, `Ico (H₁ - 1) N`, `Ico N N₁`
  have hsplit :
      ∑ x ∈ Finset.range N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| =
      (∑ x ∈ Finset.range (H₁ - 1), |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|) +
      (∑ x ∈ Finset.Ico (H₁ - 1) N, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|) +
      (∑ x ∈ Finset.Ico N N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show N ≤ N₁ by omega),
      ← Finset.sum_range_add_sum_Ico _ (show H₁ - 1 ≤ N by omega)]
  rw [hsplit]
  have hleft :
      ∑ x ∈ Finset.range (H₁ - 1), |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| ≤
      (H₁ : ℝ) ^ 2 / (N : ℝ) := by
    calc ∑ x ∈ Finset.range (H₁ - 1), |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|
        ≤ ∑ _x ∈ Finset.range (H₁ - 1), (H₁ : ℝ) / (N : ℝ) :=
          Finset.sum_le_sum fun x _ => hbd_term x
      _ = ((H₁ - 1 : ℕ) : ℝ) * ((H₁ : ℝ) / (N : ℝ)) := by simp
      _ ≤ (H₁ : ℝ) * ((H₁ : ℝ) / (N : ℝ)) := by
          have hle : ((H₁ - 1 : ℕ) : ℝ) ≤ (H₁ : ℝ) := by exact_mod_cast Nat.sub_le H₁ 1
          exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (H₁ : ℝ) ^ 2 / (N : ℝ) := by ring
  have hright :
      ∑ x ∈ Finset.Ico N N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| ≤
      (H₁ : ℝ) ^ 2 / (N : ℝ) := by
    calc ∑ x ∈ Finset.Ico N N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|
        ≤ ∑ _x ∈ Finset.Ico N N₁, (H₁ : ℝ) / (N : ℝ) :=
          Finset.sum_le_sum fun x _ => hbd_term x
      _ = ((N₁ - N : ℕ) : ℝ) * ((H₁ : ℝ) / (N : ℝ)) := by simp [Nat.card_Ico]
      _ ≤ (H₁ : ℝ) * ((H₁ : ℝ) / (N : ℝ)) := by
          have hle : ((N₁ - N : ℕ) : ℝ) ≤ (H₁ : ℝ) := by
            exact_mod_cast (show N₁ - N ≤ H₁ by omega)
          exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (H₁ : ℝ) ^ 2 / (N : ℝ) := by ring
  have hmid :
      ∑ x ∈ Finset.Ico (H₁ - 1) N, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| ≤
      (H₁ : ℝ) ^ 2 / (N : ℝ) := by
    have heq :
        ∑ x ∈ Finset.Ico (H₁ - 1) N, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| =
        ((N - (H₁ - 1) : ℕ) : ℝ) * ((H₁ : ℝ) * ((H₁ - 1 : ℕ) : ℝ) / ((N : ℝ) * (N₁ : ℝ))) := by
      have hterm : ∀ x ∈ Finset.Ico (H₁ - 1) N,
          |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| =
          (H₁ : ℝ) * ((H₁ - 1 : ℕ) : ℝ) / ((N : ℝ) * (N₁ : ℝ)) := by
        intro x hx
        rw [Finset.mem_Ico] at hx
        rw [hL_interior x hx.1 hx.2]
        have hN₁R : (N₁ : ℝ) = (N : ℝ) + ((H₁ - 1 : ℕ) : ℝ) := by
          have : N₁ = N + (H₁ - 1) := by omega
          exact_mod_cast this
        have hdiff : (H₁ : ℝ) / (N₁ : ℝ) - (H₁ : ℝ) / (N : ℝ) =
            -((H₁ : ℝ) * ((H₁ - 1 : ℕ) : ℝ) / ((N : ℝ) * (N₁ : ℝ))) := by
          rw [div_sub_div _ _ hN₁pos.ne' hNpos.ne', hN₁R]
          ring
        rw [hdiff, abs_neg, abs_of_nonneg (by positivity)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [heq]
    have hcard_le : ((N - (H₁ - 1) : ℕ) : ℝ) ≤ (N₁ : ℝ) := by
      exact_mod_cast (show N - (H₁ - 1) ≤ N₁ by omega)
    have hH₁m1_le : ((H₁ - 1 : ℕ) : ℝ) ≤ (H₁ : ℝ) := by exact_mod_cast Nat.sub_le H₁ 1
    calc ((N - (H₁ - 1) : ℕ) : ℝ) * ((H₁ : ℝ) * ((H₁ - 1 : ℕ) : ℝ) / ((N : ℝ) * (N₁ : ℝ)))
        ≤ (N₁ : ℝ) * ((H₁ : ℝ) * (H₁ : ℝ) / ((N : ℝ) * (N₁ : ℝ))) := by
          have h1 : (H₁ : ℝ) * ((H₁ - 1 : ℕ) : ℝ) / ((N : ℝ) * (N₁ : ℝ)) ≤
              (H₁ : ℝ) * (H₁ : ℝ) / ((N : ℝ) * (N₁ : ℝ)) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hH₁m1_le hH₁pos.le
          exact mul_le_mul hcard_le h1 (by positivity) hN₁pos.le
      _ = (H₁ : ℝ) ^ 2 / (N : ℝ) := by field_simp [hN₁pos.ne', hNpos.ne']
  have h3 : (H₁ : ℝ) ^ 2 / (N : ℝ) + (H₁ : ℝ) ^ 2 / (N : ℝ) + (H₁ : ℝ) ^ 2 / (N : ℝ) =
      3 * (H₁ : ℝ) ^ 2 / (N : ℝ) := by ring
  linarith only [hleft, hmid, hright, h3]

/-- Small-frequency uniform Fourier bound for the centered measure
`η(x) = if x < N then μ(x) - S₁ / N else 0` on `ℤ / (2N + 1)ℤ`. -/
lemma small_freq_eta_bound {N H₁ ξ : ℕ} (hN : 1 ≤ N) (hH₁ : 1 ≤ H₁) (hH₁N : H₁ ≤ N)
    {μ : ℕ → ℝ} (hμ0 : ∀ x < N, 0 ≤ μ x)
    (hac : ∀ d, 1 ≤ d → d < N → ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1)
    (hξ : ξ < 2 * N + 1)
    (hsmall : 2 * H₁ * min ξ (2 * N + 1 - ξ) ≤ 2 * N + 1) :
    let M := 2 * N + 1
    let N₁ := N + H₁ - 1
    let S₁ := ∑ x ∈ Finset.range N, μ x
    let S₂ := ∑ x ∈ Finset.range N, (μ x) ^ 2
    let η : ℕ → ℝ := fun x => if x < N then μ x - S₁ / (N : ℝ) else 0
    ‖dft M η ξ‖ ≤
      (Real.pi / (2 * (H₁ : ℝ))) *
        (Real.sqrt (((N₁ : ℝ)) *
          ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) -
            ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ))) +
          3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ)) := by
  intro M N₁ S₁ S₂ η
  have hMpos : 0 < M := by dsimp only [M]; omega
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hH₁pos : (0 : ℝ) < (H₁ : ℝ) := Nat.cast_pos.mpr hH₁
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast (show 0 < N₁ by dsimp only [N₁]; omega)
  have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun x hx => hμ0 x (Finset.mem_range.mp hx)
  set K₁ : ℕ → ℝ := fun s => if s < H₁ then 1 else 0
  -- Exact evaluation of `cyclicConv M K₁ η` (zero wrap-around since `H₁ ≤ N`)
  have hconv : ∀ x < M, cyclicConv M K₁ η x =
      if x < N₁ then
        (∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then μ y else 0) -
        (S₁ / (N : ℝ)) * (∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then (1 : ℝ) else 0)
      else 0 := by
    intro x hxM
    unfold cyclicConv
    have hrestrict :
        ∑ s ∈ Finset.range M, K₁ s * η ((x + M - s) % M) =
        ∑ s ∈ Finset.range H₁, η ((x + M - s) % M) := by
      rw [← Finset.sum_subset (Finset.range_mono (show H₁ ≤ M by dsimp only [M]; omega))]
      · refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mem_range] at hs
        simp [K₁, hs]
      · intro s _ hs
        rw [Finset.mem_range] at hs
        simp [K₁, hs]
    rw [hrestrict]
    by_cases hxN₁ : x < N₁
    · rw [if_pos hxN₁]
      -- Each `s < H₁` with `x < s` gives `(x + M - s) % M = x + M - s ≥ N`, so `η = 0`.
      -- Each `s < H₁` with `s ≤ x` gives `(x + M - s) % M = x - s`.
      have hbi :
          ∑ s ∈ Finset.range H₁, η ((x + M - s) % M) =
          ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then μ y - S₁ / (N : ℝ) else 0 := by
        have hL :
            ∑ s ∈ Finset.range H₁, η ((x + M - s) % M) =
            ∑ s ∈ (Finset.range H₁).filter (fun s => s ≤ x ∧ x - s < N),
              (μ (x - s) - S₁ / (N : ℝ)) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [Finset.mem_range] at hs
          by_cases hsx : s ≤ x
          · have hmod : (x + M - s) % M = x - s := by
              rw [show x + M - s = (x - s) + M by omega, Nat.add_mod_right,
                Nat.mod_eq_of_lt (by omega)]
            rw [hmod]
            dsimp only [η]
            by_cases hlt : x - s < N
            · simp [hsx, hlt]
            · simp [hsx, hlt]
          · have hmod : (x + M - s) % M = x + M - s := Nat.mod_eq_of_lt (by omega)
            rw [hmod]
            have hgeN : ¬ (x + M - s < N) := by dsimp only [M]; omega
            simp [η, hsx, hgeN]
        have hR :
            ∑ y ∈ Finset.range N, (if y ≤ x ∧ x < y + H₁ then μ y - S₁ / (N : ℝ) else 0) =
            ∑ y ∈ (Finset.range N).filter (fun y => y ≤ x ∧ x < y + H₁),
              (μ y - S₁ / (N : ℝ)) := (Finset.sum_filter ..).symm
        rw [hL, hR]
        refine Finset.sum_nbij (fun s => x - s) ?_ ?_ ?_ ?_
        · intro s hs
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs ⊢; omega
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
          dsimp only at hab; omega
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hy
          refine ⟨x - y, Finset.mem_coe.mpr (by
            simp only [Finset.mem_filter, Finset.mem_range]; omega), by dsimp; omega⟩
        · intro _ _; rfl
      rw [hbi, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    · rw [if_neg hxN₁]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_range] at hs
      have hsx : s ≤ x := by dsimp only [N₁] at hxN₁; omega
      have hmod : (x + M - s) % M = x - s := by
        rw [show x + M - s = (x - s) + M by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      have hgeN : ¬ (x - s < N) := by dsimp only [N₁] at hxN₁; omega
      simp [η, hgeN]
  -- Bound `‖dft M (cyclicConv M K₁ η) ξ‖ ≤ ∑_{x < N₁} |cyclicConv M K₁ η x|`
  set C : ℕ → ℝ := fun x => ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then μ y else 0
  set L : ℕ → ℝ := fun x => ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₁ then (1 : ℝ) else 0
  set Cbar : ℝ := (H₁ : ℝ) * S₁ / (N₁ : ℝ)
  have hdft_le :
      ‖dft M K₁ ξ‖ * ‖dft M η ξ‖ ≤ ∑ x ∈ Finset.range N₁, |C x - (S₁ / (N : ℝ)) * L x| := by
    rw [← norm_mul, ← dft_cyclicConv hMpos K₁ η ξ]
    unfold dft
    calc ‖∑ x ∈ Finset.range M, ((cyclicConv M K₁ η x : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * x)‖
        ≤ ∑ x ∈ Finset.range M, ‖((cyclicConv M K₁ η x : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * x)‖ :=
          norm_sum_le _ _
      _ = ∑ x ∈ Finset.range M, |cyclicConv M K₁ η x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_rootOfUnity_pow, mul_one]
      _ = ∑ x ∈ Finset.range N₁, |C x - (S₁ / (N : ℝ)) * L x| := by
          rw [← Finset.sum_subset (Finset.range_mono (show N₁ ≤ M by dsimp only [N₁, M]; omega))]
          · refine Finset.sum_congr rfl fun x hx => ?_
            rw [Finset.mem_range] at hx
            rw [hconv x (by dsimp only [N₁, M] at hx ⊢; omega), if_pos hx]
          · intro x hxM hxN₁
            rw [Finset.mem_range] at hxM hxN₁
            rw [hconv x hxM, if_neg hxN₁, abs_zero]
  -- Split `|C x - (S₁/N) L x| ≤ |C x - Cbar| + S₁ * |H₁/N₁ - L x / N|`
  have htri :
      ∑ x ∈ Finset.range N₁, |C x - (S₁ / (N : ℝ)) * L x| ≤
      (∑ x ∈ Finset.range N₁, |C x - Cbar|) +
      S₁ * ∑ x ∈ Finset.range N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have hsplit : C x - (S₁ / (N : ℝ)) * L x =
        (C x - Cbar) + S₁ * ((H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)) := by
      dsimp only [Cbar]; ring
    calc |C x - (S₁ / (N : ℝ)) * L x|
        = |(C x - Cbar) + S₁ * ((H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ))| := by rw [hsplit]
      _ ≤ |C x - Cbar| + |S₁ * ((H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ))| := abs_add_le _ _
      _ = |C x - Cbar| + S₁ * |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hS₁_nn]
  -- First sum via Cauchy-Schwarz + `box_energy_le`
  have hvar :
      ∑ x ∈ Finset.range N₁, (C x - Cbar) ^ 2 ≤
      (H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ) := by
    have hsumC : ∑ x ∈ Finset.range N₁, C x = (H₁ : ℝ) * S₁ := sum_box_window hH₁ μ
    have hexp :
        ∑ x ∈ Finset.range N₁, (C x - Cbar) ^ 2 =
        (∑ x ∈ Finset.range N₁, (C x) ^ 2) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ) := by
      have h1 : ∑ x ∈ Finset.range N₁, (C x - Cbar) ^ 2 =
          (∑ x ∈ Finset.range N₁, (C x) ^ 2) - 2 * Cbar * (∑ x ∈ Finset.range N₁, C x) +
          (N₁ : ℝ) * Cbar ^ 2 := by
        have hstep : ∀ x ∈ Finset.range N₁, (C x - Cbar) ^ 2 = (C x) ^ 2 - 2 * Cbar * C x + Cbar ^ 2 :=
          fun x _ => by ring
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [h1, hsumC]
      dsimp only [Cbar]
      field_simp [hN₁pos.ne']
      ring
    rw [hexp]
    have hE := box_energy_le hH₁ hac
    linarith only [hE]
  have hpart1 :
      ∑ x ∈ Finset.range N₁, |C x - Cbar| ≤
      Real.sqrt ((N₁ : ℝ) *
        ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ))) := by
    have hCS : (∑ x ∈ Finset.range N₁, |C x - Cbar|) ^ 2 ≤
        (N₁ : ℝ) * ∑ x ∈ Finset.range N₁, (C x - Cbar) ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N₁) (fun _ => (1 : ℝ)) (fun x => |C x - Cbar|)
      simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, sq_abs] at h
      exact h
    have hsq_le : (∑ x ∈ Finset.range N₁, |C x - Cbar|) ^ 2 ≤
        (N₁ : ℝ) *
          ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ)) :=
      le_trans hCS (mul_le_mul_of_nonneg_left hvar hN₁pos.le)
    have hsum_nn : 0 ≤ ∑ x ∈ Finset.range N₁, |C x - Cbar| :=
      Finset.sum_nonneg fun x _ => abs_nonneg _
    exact Real.le_sqrt_of_sq_le hsq_le
  -- Second sum via `box_uniform_boundary_l1`
  have hpart2 :
      S₁ * ∑ x ∈ Finset.range N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)| ≤
      3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) := by
    have hb := box_uniform_boundary_l1 hH₁ hH₁N
    calc S₁ * ∑ x ∈ Finset.range N₁, |(H₁ : ℝ) / (N₁ : ℝ) - L x / (N : ℝ)|
        ≤ S₁ * (3 * (H₁ : ℝ) ^ 2 / (N : ℝ)) := mul_le_mul_of_nonneg_left hb hS₁_nn
      _ = 3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) := by ring
  -- Lower bound `‖dft M K₁ ξ‖ ≥ (2 / π) * H₁`
  have hdftK₁ : dft M K₁ ξ = ∑ s ∈ Finset.range H₁, (rootOfUnity M) ^ (ξ * s) := by
    unfold dft
    rw [← Finset.sum_subset (Finset.range_mono (show H₁ ≤ M by dsimp only [M]; omega))]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      simp [K₁, hs]
    · intro s _ hs
      rw [Finset.mem_range] at hs
      simp [K₁, hs]
  have hK₁_lb : (2 / Real.pi) * (H₁ : ℝ) ≤ ‖dft M K₁ ξ‖ := by
    rw [hdftK₁]
    exact dirichlet_kernel_lower_bound hMpos hH₁ hξ hsmall
  have hK₁_lb_pos : 0 < (2 / Real.pi) * (H₁ : ℝ) := by positivity
  have hprod : ((2 / Real.pi) * (H₁ : ℝ)) * ‖dft M η ξ‖ ≤
      Real.sqrt ((N₁ : ℝ) *
        ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ))) +
      3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hK₁_lb (norm_nonneg (dft M η ξ))
    linarith only [h1, hdft_le, htri, hpart1, hpart2]
  have hdiv := (le_div_iff₀' hK₁_lb_pos).mpr hprod
  have hrew :
      (Real.sqrt ((N₁ : ℝ) *
          ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ))) +
        3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ)) / ((2 / Real.pi) * (H₁ : ℝ)) =
      (Real.pi / (2 * (H₁ : ℝ))) *
        (Real.sqrt ((N₁ : ℝ) *
          ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - ((H₁ : ℝ) ^ 2 * S₁ ^ 2) / (N₁ : ℝ))) +
        3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ)) := by
    have hpi := Real.pi_ne_zero
    field_simp [hpi, hH₁pos.ne']
  rw [← hrew]
  exact hdiv

/-! ### Part 4: Two-Frequency Lindström Inequality & Large-Frequency Bound -/

private lemma re_rootOfUnity_mul_conj (M ξ y z : ℕ) :
    ((rootOfUnity M) ^ (ξ * y) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * z))).re =
      ((rootOfUnity M) ^ (ξ * (if y ≤ z then z - y else y - z))).re := by
  by_cases hyz : y ≤ z
  · rw [if_pos hyz]
    have hsplit : (rootOfUnity M) ^ (ξ * z) =
        (rootOfUnity M) ^ (ξ * y) * (rootOfUnity M) ^ (ξ * (z - y)) := by
      rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hyz]
    rw [hsplit, map_mul, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_rootOfUnity_pow, one_pow, Complex.ofReal_one, one_mul, Complex.conj_re]
  · rw [if_neg hyz]
    have hsplit : (rootOfUnity M) ^ (ξ * y) =
        (rootOfUnity M) ^ (ξ * z) * (rootOfUnity M) ^ (ξ * (y - z)) := by
      rw [← pow_add, ← mul_add, Nat.add_sub_cancel' (show z ≤ y by omega)]
    rw [hsplit, mul_right_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_rootOfUnity_pow, one_pow, Complex.ofReal_one, one_mul]

/-- Exact Fejér identity for the squared norm of the Dirichlet kernel:
`‖∑ s < H, ω^(ξ * s)‖^2 = H + 2 * ∑_{1 ≤ d < H} (H - d) * (ω^(ξ * d)).re`. -/
private lemma norm_dirichlet_sq_eq (M ξ H : ℕ) :
    ‖∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 =
      (H : ℝ) + 2 * ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * ((rootOfUnity M) ^ (ξ * d)).re := by
  have hmul :
      ‖∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 =
      ((∑ s ∈ Finset.range H, (rootOfUnity M) ^ (ξ * s)) *
        starRingEnd ℂ (∑ t ∈ Finset.range H, (rootOfUnity M) ^ (ξ * t))).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hmul, map_sum, Finset.sum_mul, Complex.re_sum]
  have hexp :
      ∑ s ∈ Finset.range H,
        ((rootOfUnity M) ^ (ξ * s) *
          ∑ t ∈ Finset.range H, starRingEnd ℂ ((rootOfUnity M) ^ (ξ * t))).re =
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        ((rootOfUnity M) ^ (ξ * (if s ≤ t then t - s else s - t))).re := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun t _ => re_rootOfUnity_mul_conj M ξ s t
  rw [hexp]
  -- Split double sum into `s = t`, `s < t`, `t < s`
  have hsplit :
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        ((rootOfUnity M) ^ (ξ * (if s ≤ t then t - s else s - t))).re =
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, if s = t then (1 : ℝ) else 0) +
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        if s < t then ((rootOfUnity M) ^ (ξ * (t - s))).re else 0) +
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        if t < s then ((rootOfUnity M) ^ (ξ * (s - t))).re else 0) := by
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rcases lt_trichotomy s t with hlt | heq | hgt
    · simp [hlt, hlt.le, hlt.ne, show ¬ t < s by omega]
    · subst heq; simp
    · simp [hgt, show ¬ s ≤ t by omega, show s ≠ t by omega, show ¬ s < t by omega]
  rw [hsplit]
  have hdiag :
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (if s = t then (1 : ℝ) else 0) = (H : ℝ) := by
    have : ∀ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (if s = t then (1 : ℝ) else 0) = 1 :=
      fun s hs => by rw [Finset.sum_ite_eq, if_pos hs]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hsymm :
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (if t < s then ((rootOfUnity M) ^ (ξ * (s - t))).re else 0) =
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (if s < t then ((rootOfUnity M) ^ (ξ * (t - s))).re else 0) := by
    rw [Finset.sum_comm]
  have hoff :
      ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
        (if s < t then ((rootOfUnity M) ^ (ξ * (t - s))).re else 0) =
      ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * ((rootOfUnity M) ^ (ξ * d)).re := by
    have hL :
        ∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H,
          (if s < t then ((rootOfUnity M) ^ (ξ * (t - s))).re else 0) =
        ∑ p ∈ ((Finset.range H) ×ˢ (Finset.range H)).filter (fun p => p.1 < p.2),
          ((rootOfUnity M) ^ (ξ * (p.2 - p.1))).re := by
      rw [Finset.sum_filter, Finset.sum_product]
    have hR :
        ∑ d ∈ Finset.Ico 1 H, ((H - d : ℕ) : ℝ) * ((rootOfUnity M) ^ (ξ * d)).re =
        ∑ q ∈ (Finset.Ico 1 H).sigma (fun d => Finset.range (H - d)),
          ((rootOfUnity M) ^ (ξ * q.1)).re := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => ?_
      dsimp only
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hL, hR]
    refine Finset.sum_nbij (fun p => ⟨p.2 - p.1, p.1⟩) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_sigma, Finset.mem_Ico] at hp ⊢; omega
    · intro p₁ hp₁ p₂ hp₂ hEq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp₁ hp₂
      have h1 : p₁.2 - p₁.1 = p₂.2 - p₂.1 := congrArg Sigma.fst hEq
      have h2 : p₁.1 = p₂.1 := by simpa using (Sigma.mk.inj_iff.mp hEq).2
      exact Prod.ext h2 (by omega)
    · intro q hq
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hq
      refine ⟨(q.2, q.2 + q.1), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
      · exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
    · intro _ _; rfl
  rw [hdiag, hsymm, hoff]; ring

/-- Two-Frequency Lindström Inequality:
for any `N, M, H₂ ≥ 1` (`N ≤ M`), any `ξ : ℕ`, and any measure with linear AC `≤ 1`,
`S₁^2 + ‖dft M μ₀ ξ‖^2 ≤ (N + H₂ - 1) * (1 + (‖∑ s < H₂, ω^(ξ * s)‖ / H₂)^2 + 2 * (S₂ - 1) / H₂)`. -/
lemma two_freq_lindstrom {N M H₂ : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) (hH₂ : 1 ≤ H₂) (ξ : ℕ)
    {μ : ℕ → ℝ}
    (hac : ∀ d, 1 ≤ d → d < N → ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1) :
    let S₁ := ∑ x ∈ Finset.range N, μ x
    let S₂ := ∑ x ∈ Finset.range N, (μ x) ^ 2
    let μ₀ : ℕ → ℝ := fun x => if x < N then μ x else 0
    S₁ ^ 2 + ‖dft M μ₀ ξ‖ ^ 2 ≤
      ((N + H₂ - 1 : ℕ) : ℝ) *
        (1 + (‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ / (H₂ : ℝ)) ^ 2 +
          2 * (S₂ - 1) / (H₂ : ℝ)) := by
  intro S₁ S₂ μ₀
  set N₂ : ℕ := N + H₂ - 1
  have hH₂pos : (0 : ℝ) < (H₂ : ℝ) := Nat.cast_pos.mpr hH₂
  have hN₂pos : (0 : ℝ) < (N₂ : ℝ) := by exact_mod_cast (show 0 < N₂ by dsimp only [N₂]; omega)
  set A₀ : ℕ → ℝ := fun x => ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₂ then μ y else 0
  set B₀ : ℕ → ℂ := fun x =>
    ∑ y ∈ Finset.range N, if y ≤ x ∧ x < y + H₂ then (μ y : ℂ) * (rootOfUnity M) ^ (ξ * y) else 0
  have hsumA : ∑ x ∈ Finset.range N₂, A₀ x = (H₂ : ℝ) * S₁ := sum_box_window hH₂ μ
  have hsumB : ∑ x ∈ Finset.range N₂, B₀ x = (H₂ : ℂ) * dft M μ₀ ξ := by
    have hdftμ₀ : dft M μ₀ ξ = ∑ y ∈ Finset.range N, (μ y : ℂ) * (rootOfUnity M) ^ (ξ * y) := by
      unfold dft
      rw [← Finset.sum_subset (Finset.range_mono hNM)]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_range] at hy; simp [μ₀, hy]
      · intro y _ hy
        rw [Finset.mem_range] at hy; simp [μ₀, hy]
    rw [hdftμ₀]
    dsimp only [B₀]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_range] at hy
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hfil : (Finset.range N₂).filter (fun x => y ≤ x ∧ x < y + H₂) = Finset.Ico y (y + H₂) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; dsimp only [N₂]; omega
    rw [hfil, Nat.card_Ico]; simp
  have hCS_A : ((H₂ : ℝ) * S₁) ^ 2 ≤ (N₂ : ℝ) * ∑ x ∈ Finset.range N₂, (A₀ x) ^ 2 := by
    rw [← hsumA]
    simpa [Finset.card_range] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N₂) (fun _ => (1 : ℝ)) A₀)
  have hCS_B : ((H₂ : ℝ) * ‖dft M μ₀ ξ‖) ^ 2 ≤ (N₂ : ℝ) * ∑ x ∈ Finset.range N₂, ‖B₀ x‖ ^ 2 := by
    have hnorm : (H₂ : ℝ) * ‖dft M μ₀ ξ‖ ≤ ∑ x ∈ Finset.range N₂, ‖B₀ x‖ := by
      have h1 : ‖∑ x ∈ Finset.range N₂, B₀ x‖ = (H₂ : ℝ) * ‖dft M μ₀ ξ‖ := by
        rw [hsumB, norm_mul, Complex.norm_natCast]
      rw [← h1]
      exact norm_sum_le _ _
    have hsq1 : ((H₂ : ℝ) * ‖dft M μ₀ ξ‖) ^ 2 ≤ (∑ x ∈ Finset.range N₂, ‖B₀ x‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnorm 2
    have hsq2 : (∑ x ∈ Finset.range N₂, ‖B₀ x‖) ^ 2 ≤
        (N₂ : ℝ) * ∑ x ∈ Finset.range N₂, ‖B₀ x‖ ^ 2 := by
      simpa [Finset.card_range] using
        (Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N₂) (fun _ => (1 : ℝ)) (fun x => ‖B₀ x‖))
    exact le_trans hsq1 hsq2
  -- Expand `∑_{x < N₂} (A₀(x)^2 + ‖B₀(x)‖^2)` via `sum_window_overlap_split`
  set w : ℕ → ℝ := fun d => 1 + ((rootOfUnity M) ^ (ξ * d)).re
  have hE_eq :
      ∑ x ∈ Finset.range N₂, ((A₀ x) ^ 2 + ‖B₀ x‖ ^ 2) =
      (H₂ : ℝ) * w 0 * S₂ +
      2 * ∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * w d *
        (∑ y ∈ Finset.range (N - d), μ y * μ (y + d)) := by
    have hpoint : ∀ x ∈ Finset.range N₂,
        (A₀ x) ^ 2 + ‖B₀ x‖ ^ 2 =
        ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          if (y ≤ x ∧ x < y + H₂) ∧ (z ≤ x ∧ x < z + H₂)
          then μ y * μ z * w (if y ≤ z then z - y else y - z) else 0 := by
      intro x _
      have hA : (A₀ x) ^ 2 = ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          if (y ≤ x ∧ x < y + H₂) ∧ (z ≤ x ∧ x < z + H₂) then μ y * μ z else 0 := by
        dsimp only [A₀]
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hy : y ≤ x ∧ x < y + H₂ <;> by_cases hz : z ≤ x ∧ x < z + H₂ <;> simp [hy, hz]
      have hB : ‖B₀ x‖ ^ 2 = ∑ y ∈ Finset.range N, ∑ z ∈ Finset.range N,
          if (y ≤ x ∧ x < y + H₂) ∧ (z ≤ x ∧ x < z + H₂)
          then μ y * μ z * ((rootOfUnity M) ^ (ξ * (if y ≤ z then z - y else y - z))).re else 0 := by
        have hmul : ‖B₀ x‖ ^ 2 = (B₀ x * starRingEnd ℂ (B₀ x)).re := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        rw [hmul]
        dsimp only [B₀]
        rw [map_sum, Finset.sum_mul, Complex.re_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hy : y ≤ x ∧ x < y + H₂ <;> by_cases hz : z ≤ x ∧ x < z + H₂
        · simp only [hy, hz, and_self, ↓reduceIte, map_mul, Complex.conj_ofReal]
          have hre : ((μ y : ℂ) * (rootOfUnity M) ^ (ξ * y) *
              ((μ z : ℂ) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * z)))).re =
              μ y * μ z *
                ((rootOfUnity M) ^ (ξ * y) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * z))).re := by
            have hassoc : (μ y : ℂ) * (rootOfUnity M) ^ (ξ * y) *
                ((μ z : ℂ) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * z))) =
                (((μ y * μ z : ℝ) : ℂ)) *
                  ((rootOfUnity M) ^ (ξ * y) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * z))) := by
              push_cast; ring
            rw [hassoc, Complex.re_ofReal_mul]
          rw [hre, re_rootOfUnity_mul_conj]
        · simp [hy, hz]
        · simp [hy, hz]
        · simp [hy, hz]
      rw [hA, hB, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      dsimp only [w]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpoint]
    exact sum_window_overlap_split hH₂ μ w
  -- Upper-bound every lag autocorrelation by `1`, using `w d = 1 + Re(ω^(ξd)) ≥ 0`
  have hw_nn : ∀ d, 0 ≤ w d := by
    intro d
    dsimp only [w]
    have hle : |((rootOfUnity M) ^ (ξ * d)).re| ≤ 1 := by
      calc |((rootOfUnity M) ^ (ξ * d)).re|
          ≤ ‖(rootOfUnity M) ^ (ξ * d)‖ := Complex.abs_re_le_norm _
        _ = 1 := norm_rootOfUnity_pow M (ξ * d)
    linarith [(abs_le.mp hle).1]
  have hE_le :
      ∑ x ∈ Finset.range N₂, ((A₀ x) ^ 2 + ‖B₀ x‖ ^ 2) ≤
      (H₂ : ℝ) ^ 2 + ‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 +
        2 * (H₂ : ℝ) * (S₂ - 1) := by
    rw [hE_eq]
    have hw0 : w 0 = 2 := by dsimp only [w]; simp; norm_num
    have htail :
        ∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * w d *
          (∑ y ∈ Finset.range (N - d), μ y * μ (y + d)) ≤
        ∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * w d := by
      refine Finset.sum_le_sum fun d hd => ?_
      rw [Finset.mem_Ico] at hd
      have hcoeff : 0 ≤ ((H₂ - d : ℕ) : ℝ) * w d :=
        mul_nonneg (Nat.cast_nonneg _) (hw_nn d)
      have hle1 : ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1 := by
        by_cases hdN : d < N
        · exact hac d hd.1 hdN
        · have h0 : N - d = 0 := by omega
          rw [h0, Finset.range_zero, Finset.sum_empty]; norm_num
      nlinarith
    have hsplit_w :
        2 * ∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * w d =
        (H₂ : ℝ) * ((H₂ : ℝ) - 1) +
        (‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 - (H₂ : ℝ)) := by
      have h1 :
          ∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * w d =
          (∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ)) +
          (∑ d ∈ Finset.Ico 1 H₂, ((H₂ - d : ℕ) : ℝ) * ((rootOfUnity M) ^ (ξ * d)).re) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        dsimp only [w]; ring
      rw [h1, mul_add, two_mul_sum_sub_Ico H₂ hH₂, norm_dirichlet_sq_eq M ξ H₂]
      ring
    rw [hw0]
    linarith only [htail, hsplit_w]
  have hcombined :
      (H₂ : ℝ) ^ 2 * (S₁ ^ 2 + ‖dft M μ₀ ξ‖ ^ 2) ≤
      (N₂ : ℝ) *
        ((H₂ : ℝ) ^ 2 + ‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 +
          2 * (H₂ : ℝ) * (S₂ - 1)) := by
    have hsum_add :
        (H₂ : ℝ) ^ 2 * (S₁ ^ 2 + ‖dft M μ₀ ξ‖ ^ 2) ≤
        (N₂ : ℝ) * ∑ x ∈ Finset.range N₂, ((A₀ x) ^ 2 + ‖B₀ x‖ ^ 2) := by
      rw [Finset.sum_add_distrib]
      nlinarith only [hCS_A, hCS_B]
    exact le_trans hsum_add (mul_le_mul_of_nonneg_left hE_le hN₂pos.le)
  have hrew :
      (N₂ : ℝ) *
        (1 + (‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ / (H₂ : ℝ)) ^ 2 +
          2 * (S₂ - 1) / (H₂ : ℝ)) =
      ((N₂ : ℝ) *
        ((H₂ : ℝ) ^ 2 + ‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ ^ 2 +
          2 * (H₂ : ℝ) * (S₂ - 1))) / (H₂ : ℝ) ^ 2 := by
    field_simp [hH₂pos.ne']
  rw [hrew, le_div_iff₀ (sq_pos_of_pos hH₂pos)]
  linarith only [hcombined]

/-- Large-frequency uniform Fourier bound for the centered measure `η` on `ℤ / (2N + 1)ℤ`:
whenever `1 ≤ ξ < 2N + 1` and `2N + 1 < 2 * H₁ * min ξ (2N + 1 - ξ)`. -/
lemma large_freq_eta_bound {N H₁ H₂ ξ : ℕ} (hN : 1 ≤ N) (hH₁ : 1 ≤ H₁) (hH₂ : 1 ≤ H₂)
    {μ : ℕ → ℝ} (hμ0 : ∀ x < N, 0 ≤ μ x)
    (hac : ∀ d, 1 ≤ d → d < N → ∑ y ∈ Finset.range (N - d), μ y * μ (y + d) ≤ 1)
    (hξ1 : 1 ≤ ξ) (hξM : ξ < 2 * N + 1)
    (hlarge : 2 * N + 1 < 2 * H₁ * min ξ (2 * N + 1 - ξ)) :
    let M := 2 * N + 1
    let S₁ := ∑ x ∈ Finset.range N, μ x
    let S₂ := ∑ x ∈ Finset.range N, (μ x) ^ 2
    let η : ℕ → ℝ := fun x => if x < N then μ x - S₁ / (N : ℝ) else 0
    ‖dft M η ξ‖ ≤
      Real.sqrt (((N + H₂ - 1 : ℕ) : ℝ) *
        (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2) +
      S₁ * (H₁ : ℝ) / (N : ℝ) := by
  intro M S₁ S₂ η
  have hMpos : 0 < M := by dsimp only [M]; omega
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hH₁pos : (0 : ℝ) < (H₁ : ℝ) := Nat.cast_pos.mpr hH₁
  have hH₂pos : (0 : ℝ) < (H₂ : ℝ) := Nat.cast_pos.mpr hH₂
  have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun x hx => hμ0 x (Finset.mem_range.mp hx)
  set μ₀ : ℕ → ℝ := fun x => if x < N then μ x else 0
  set u₀ : ℕ → ℝ := fun x => if x < N then (1 : ℝ) else 0
  have hη_eq : η = fun x => μ₀ x - (S₁ / (N : ℝ)) * u₀ x := by
    ext x
    dsimp only [η, μ₀, u₀]
    split_ifs <;> ring
  have hdft_η : dft M η ξ = dft M μ₀ ξ - ((S₁ / (N : ℝ) : ℝ) : ℂ) * dft M u₀ ξ := by
    rw [hη_eq, dft_sub, dft_smul]
  have htri : ‖dft M η ξ‖ ≤ ‖dft M μ₀ ξ‖ + (S₁ / (N : ℝ)) * ‖dft M u₀ ξ‖ := by
    rw [hdft_η]
    calc ‖dft M μ₀ ξ - ((S₁ / (N : ℝ) : ℝ) : ℂ) * dft M u₀ ξ‖
        ≤ ‖dft M μ₀ ξ‖ + ‖((S₁ / (N : ℝ) : ℝ) : ℂ) * dft M u₀ ξ‖ := norm_sub_le _ _
      _ = ‖dft M μ₀ ξ‖ + (S₁ / (N : ℝ)) * ‖dft M u₀ ξ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- Bound `M / (2 * min ξ (M - ξ)) ≤ H₁`
  have hkpos : (0 : ℝ) < ((min ξ (M - ξ) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < min ξ (M - ξ) by dsimp only [M]; omega)
  have hMdiv_le : (M : ℝ) / (2 * ((min ξ (M - ξ) : ℕ) : ℝ)) ≤ (H₁ : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hltR : (M : ℝ) ≤ (2 : ℝ) * (H₁ : ℝ) * ((min ξ (M - ξ) : ℕ) : ℝ) := by
      have : M ≤ 2 * H₁ * min ξ (M - ξ) := le_of_lt hlarge
      exact_mod_cast this
    linarith only [hltR]
  -- Bound `‖dft M u₀ ξ‖ ≤ H₁`
  have hdft_u₀ : dft M u₀ ξ = ∑ s ∈ Finset.range N, (rootOfUnity M) ^ (ξ * s) := by
    unfold dft
    rw [← Finset.sum_subset (Finset.range_mono (show N ≤ M by dsimp only [M]; omega))]
    · refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs; simp [u₀, hs]
    · intro s _ hs
      rw [Finset.mem_range] at hs; simp [u₀, hs]
  have hu₀_le : ‖dft M u₀ ξ‖ ≤ (H₁ : ℝ) := by
    rw [hdft_u₀]
    exact le_trans (dirichlet_kernel_upper_bound hMpos hξ1 hξM N) hMdiv_le
  -- Bound `‖dft M μ₀ ξ‖` via Two-Frequency Lindström
  have hD₂_le : ‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ / (H₂ : ℝ) ≤
      (H₁ : ℝ) / (H₂ : ℝ) :=
    div_le_div_of_nonneg_right
      (le_trans (dirichlet_kernel_upper_bound hMpos hξ1 hξM H₂) hMdiv_le) hH₂pos.le
  have hD₂_sq : (‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ / (H₂ : ℝ)) ^ 2 ≤
      ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD₂_le 2
  have h2f := two_freq_lindstrom hN (show N ≤ M by dsimp only [M]; omega) hH₂ ξ hac
  have hμ₀_sq : ‖dft M μ₀ ξ‖ ^ 2 ≤
      ((N + H₂ - 1 : ℕ) : ℝ) *
        (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2 := by
    have hN₂_nn : (0 : ℝ) ≤ ((N + H₂ - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hmono :
        ((N + H₂ - 1 : ℕ) : ℝ) *
          (1 + (‖∑ s ∈ Finset.range H₂, (rootOfUnity M) ^ (ξ * s)‖ / (H₂ : ℝ)) ^ 2 +
            2 * (S₂ - 1) / (H₂ : ℝ)) ≤
        ((N + H₂ - 1 : ℕ) : ℝ) *
          (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hD₂_sq]) hN₂_nn
    linarith only [h2f, hmono]
  have hμ₀_le : ‖dft M μ₀ ξ‖ ≤
      Real.sqrt (((N + H₂ - 1 : ℕ) : ℝ) *
        (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2) :=
    Real.le_sqrt_of_sq_le hμ₀_sq
  have hlin : (S₁ / (N : ℝ)) * ‖dft M u₀ ξ‖ ≤ S₁ * (H₁ : ℝ) / (N : ℝ) := by
    calc (S₁ / (N : ℝ)) * ‖dft M u₀ ξ‖
        ≤ (S₁ / (N : ℝ)) * (H₁ : ℝ) := mul_le_mul_of_nonneg_left hu₀_le (by positivity)
      _ = S₁ * (H₁ : ℝ) / (N : ℝ) := by ring
  linarith only [htri, hμ₀_le, hlin]

/-! ### Part 5: Finite-DFT 3-AP Counting on `ℤ / (2N + 1)ℤ` -/

/-- Exact 3-AP counting identity on `ℤ / (2N + 1)ℤ` for any `T ⊆ range N` and `f` supported on `range N`:
no modular wrap-around occurs because `0 ≤ t₁ + t₂ < 2N + 1` and `0 ≤ 2x < 2N + 1`. -/
private lemma dft_3ap_identity {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.range N)
    (f : ℕ → ℝ) (hf_zero : ∀ x, N ≤ x → f x = 0) :
    let M := 2 * N + 1
    let indT : ℕ → ℝ := fun x => if x ∈ T then 1 else 0
    (1 / (M : ℝ)) *
      (∑ ξ ∈ Finset.range M,
        (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M f (2 * ξ))).re =
    ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N, if t₁ + t₂ = 2 * x then f x else 0 := by
  intro M indT
  have hMpos : 0 < M := by dsimp only [M]; omega
  have hTM : T ⊆ Finset.range M := Subset.trans hT (Finset.range_mono (by dsimp only [M]; omega))
  have hdftT : ∀ ξ, dft M indT ξ = ∑ t ∈ T, (rootOfUnity M) ^ (ξ * t) :=
    fun ξ => dft_indicator hTM ξ
  have hdftf : ∀ ξ, dft M f (2 * ξ) = ∑ x ∈ Finset.range N, (f x : ℂ) * (rootOfUnity M) ^ (ξ * (2 * x)) := by
    intro ξ
    unfold dft
    rw [← Finset.sum_subset (Finset.range_mono (show N ≤ M by dsimp only [M]; omega))]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [show 2 * ξ * x = ξ * (2 * x) by ring]
    · intro x _ hx
      rw [Finset.mem_range] at hx
      simp [hf_zero x (by omega)]
  have hsumC :
      ∑ ξ ∈ Finset.range M, (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M f (2 * ξ)) =
      (M : ℂ) * ((∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
        if t₁ + t₂ = 2 * x then f x else 0 : ℝ) : ℂ) := by
    have hexp : ∀ ξ ∈ Finset.range M,
        (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M f (2 * ξ)) =
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (f x : ℂ) * (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) := by
      intro ξ _
      rw [hdftT, hdftf, sq, map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t₁ _ => ?_
      rw [Finset.mul_sum T (fun t₂ => (rootOfUnity M) ^ (ξ * t₂)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun t₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      rw [map_mul, Complex.conj_ofReal]
      have hpow :
          (rootOfUnity M) ^ (ξ * t₁) * (rootOfUnity M) ^ (ξ * t₂) *
            starRingEnd ℂ ((rootOfUnity M) ^ (ξ * (2 * x))) =
          (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) := by
        rw [← pow_add, ← mul_add]
        exact rootOfUnity_conj_mul_eq hMpos ξ (t₁ + t₂) (2 * x) (by dsimp only [M]; omega)
      calc (rootOfUnity M) ^ (ξ * t₁) * (rootOfUnity M) ^ (ξ * t₂) *
            ((f x : ℂ) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * (2 * x))))
          = (f x : ℂ) * ((rootOfUnity M) ^ (ξ * t₁) * (rootOfUnity M) ^ (ξ * t₂) *
              starRingEnd ℂ ((rootOfUnity M) ^ (ξ * (2 * x)))) := by ring
        _ = (f x : ℂ) * (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) := by rw [hpow]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    have hcomm1 : ∀ t₁ ∈ T,
        ∑ ξ ∈ Finset.range M, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (f x : ℂ) * (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) =
        ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (f x : ℂ) * ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) := by
      intro t₁ _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t₂ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => (Finset.mul_sum ..).symm
    rw [Finset.sum_congr rfl hcomm1]
    have hinner : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ x ∈ Finset.range N,
        (f x : ℂ) * ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) =
        (M : ℂ) * ((if t₁ + t₂ = 2 * x then f x else 0 : ℝ) : ℂ) := by
      intro t₁ ht₁ t₂ ht₂ x hx
      have ht₁N : t₁ < N := Finset.mem_range.mp (hT ht₁)
      have ht₂N : t₂ < N := Finset.mem_range.mp (hT ht₂)
      rw [Finset.mem_range] at hx
      rw [sum_rootOfUnity_ortho hMpos]
      by_cases heq : t₁ + t₂ = 2 * x
      · have hmod0 : (t₁ + t₂ + M - 2 * x) % M = 0 := by
          rw [show t₁ + t₂ + M - 2 * x = M by omega, Nat.mod_self]
        rw [hmod0, if_pos (dvd_zero M), if_pos heq]; ring
      · have hndvd : ¬ M ∣ ((t₁ + t₂ + M - 2 * x) % M) := by
          intro hdvd
          have hmod0 : (t₁ + t₂ + M - 2 * x) % M = 0 :=
            Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hMpos)
          rcases Nat.dvd_of_mod_eq_zero hmod0 with ⟨q, hq⟩
          have hq1 : q = 1 := by
            by_contra hqne
            rcases lt_or_gt_of_ne hqne with hlt | hgt
            · have : q = 0 := by omega
              subst this; dsimp only [M] at hq; omega
            · have : 2 ≤ q := by omega
              have : 2 * M ≤ M * q := by nlinarith
              dsimp only [M] at hq this; omega
          subst hq1; dsimp only [M] at hq; omega
        rw [if_neg hndvd, if_neg heq]; simp
    have hstep :
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (f x : ℂ) * ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((t₁ + t₂ + M - 2 * x) % M)) =
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (M : ℂ) * ((if t₁ + t₂ = 2 * x then f x else 0 : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun t₁ ht₁ =>
        Finset.sum_congr rfl fun t₂ ht₂ =>
          Finset.sum_congr rfl fun x hx => hinner t₁ ht₁ t₂ ht₂ x hx
    rw [hstep]
    push_cast
    simp_rw [← Finset.mul_sum]
  rw [hsumC]
  have hre : ((M : ℂ) * ((∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
      if t₁ + t₂ = 2 * x then f x else 0 : ℝ) : ℂ)).re =
      (M : ℝ) * (∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
      if t₁ + t₂ = 2 * x then f x else 0) := by simp
  rw [hre]
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  field_simp [hMne]

/-- Universal 3-AP-free support bound from uniform Fourier flatness on `ℤ / (2N + 1)ℤ`:
if `‖dft (2N+1) η ξ‖ ≤ U` for all `ξ < 2N + 1`, and `T ⊆ range N` forms zero nontrivial
linear 3-APs `t₁ + t₂ = 2x` (`t₁ ≠ t₂`) centered at points with `μ x > 0`, then
`|T| ≤ (2 * N / S₁) * U + √(2 * N)`. -/
theorem universal_3ap_free_superset_from_U {N : ℕ} (hN : 1 ≤ N)
    {μ : ℕ → ℝ} (hμ0 : ∀ x < N, 0 ≤ μ x)
    (hS₁_pos : 0 < ∑ x ∈ Finset.range N, μ x)
    {T : Finset ℕ} (hT : T ⊆ Finset.range N)
    (h3ap : ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ x < N, t₁ ≠ t₂ → t₁ + t₂ = 2 * x → μ x = 0)
    {U : ℝ} (hU_nn : 0 ≤ U)
    (hU : ∀ ξ < 2 * N + 1,
      ‖dft (2 * N + 1)
        (fun x => if x < N then μ x - (∑ y ∈ Finset.range N, μ y) / (N : ℝ) else 0) ξ‖ ≤ U) :
    (T.card : ℝ) ≤ (2 * (N : ℝ) / (∑ x ∈ Finset.range N, μ x)) * U + Real.sqrt (2 * (N : ℝ)) := by
  set M : ℕ := 2 * N + 1
  set S₁ : ℝ := ∑ x ∈ Finset.range N, μ x
  set μ₀ : ℕ → ℝ := fun x => if x < N then μ x else 0
  set u₀ : ℕ → ℝ := fun x => if x < N then (1 : ℝ) else 0
  set η : ℕ → ℝ := fun x => if x < N then μ x - S₁ / (N : ℝ) else 0
  set indT : ℕ → ℝ := fun x => if x ∈ T then 1 else 0
  have hMpos : 0 < M := by dsimp only [M]; omega
  have hMposR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  -- Step 1: Upper bound `I(μ₀) ≤ S₁`
  have hIμ : ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
      (if t₁ + t₂ = 2 * x then μ₀ x else 0) ≤ S₁ := by
    have hdiag :
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N, (if t₁ + t₂ = 2 * x then μ₀ x else 0) =
        ∑ t ∈ T, μ t := by
      refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
      have ht₁N : t₁ < N := Finset.mem_range.mp (hT ht₁)
      rw [Finset.sum_eq_single t₁]
      · rw [Finset.sum_eq_single t₁]
        · rw [if_pos (by omega)]
          simp [μ₀, ht₁N]
        · intro x _ hxt; rw [if_neg (by omega)]
        · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr ht₁N))
      · intro t₂ ht₂ ht₂ne
        refine Finset.sum_eq_zero fun x hx => ?_
        rw [Finset.mem_range] at hx
        by_cases heq : t₁ + t₂ = 2 * x
        · rw [if_pos heq]
          simp [μ₀, hx, h3ap t₁ ht₁ t₂ ht₂ x hx (Ne.symm ht₂ne) heq]
        · rw [if_neg heq]
      · intro hnot; exact False.elim (hnot ht₁)
    rw [hdiag]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT fun x hx _ => hμ0 x (Finset.mem_range.mp hx)
  -- Step 2: Lower bound `I((S₁ / N) * u₀) ≥ (S₁ / (2 N)) * |T|^2`
  have hIu : (S₁ / (2 * (N : ℝ))) * (T.card : ℝ) ^ 2 ≤
      ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
        (if t₁ + t₂ = 2 * x then (S₁ / (N : ℝ)) * u₀ x else 0) := by
    have heq_cnt :
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
          (if t₁ + t₂ = 2 * x then (S₁ / (N : ℝ)) * u₀ x else 0) =
        (S₁ / (N : ℝ)) *
          ∑ t₁ ∈ T, ∑ t₂ ∈ T, (if (t₁ + t₂) % 2 = 0 then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t₂ ht₂ => ?_
      have ht₁N : t₁ < N := Finset.mem_range.mp (hT ht₁)
      have ht₂N : t₂ < N := Finset.mem_range.mp (hT ht₂)
      by_cases heven : (t₁ + t₂) % 2 = 0
      · rw [if_pos heven, mul_one, Finset.sum_eq_single ((t₁ + t₂) / 2)]
        · rw [if_pos (by omega)]
          simp [u₀, show (t₁ + t₂) / 2 < N by omega]
        · intro x _ hne; rw [if_neg (by omega)]
        · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
      · rw [if_neg heven, mul_zero]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [if_neg (by omega)]
    rw [heq_cnt]
    -- Count even-sum pairs via `T_even` and `T_odd`
    set Teven := T.filter (fun t => t % 2 = 0)
    set Todd := T.filter (fun t => t % 2 ≠ 0)
    have hcard_sum : (Teven.card : ℝ) + (Todd.card : ℝ) = (T.card : ℝ) := by
      have hnat : Teven.card + Todd.card = T.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
        congr 1; ext t; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      exact_mod_cast hnat
    have hpair_eq :
        ∑ t₁ ∈ T, ∑ t₂ ∈ T, (if (t₁ + t₂) % 2 = 0 then (1 : ℝ) else 0) =
        (Teven.card : ℝ) ^ 2 + (Todd.card : ℝ) ^ 2 := by
      have h1 : ∀ t₁ ∈ T,
          ∑ t₂ ∈ T, (if (t₁ + t₂) % 2 = 0 then (1 : ℝ) else 0) =
          if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ) := by
        intro t₁ _
        by_cases h0 : t₁ % 2 = 0
        · rw [if_pos h0]
          have hfil : T.filter (fun t₂ => (t₁ + t₂) % 2 = 0) = Teven := by
            ext t₂; dsimp only [Teven]; simp only [Finset.mem_filter]
            exact ⟨fun ⟨h, hm⟩ => ⟨h, by omega⟩, fun ⟨h, hm⟩ => ⟨h, by omega⟩⟩
          rw [← Finset.sum_filter, hfil, Finset.sum_const, nsmul_eq_mul, mul_one]
        · rw [if_neg h0]
          have hfil : T.filter (fun t₂ => (t₁ + t₂) % 2 = 0) = Todd := by
            ext t₂; dsimp only [Todd]; simp only [Finset.mem_filter]
            exact ⟨fun ⟨h, hm⟩ => ⟨h, by omega⟩, fun ⟨h, hm⟩ => ⟨h, by omega⟩⟩
          rw [← Finset.sum_filter, hfil, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl h1]
      have hsplit := Finset.sum_filter_add_sum_filter_not T (fun t => t % 2 = 0)
        (fun t₁ => if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ))
      rw [← hsplit]
      have hA : ∑ t₁ ∈ Teven, (if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ)) =
          (Teven.card : ℝ) ^ 2 := by
        have : ∀ t₁ ∈ Teven,
            (if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ)) = (Teven.card : ℝ) := by
          intro t₁ ht₁; simp [(Finset.mem_filter.mp ht₁).2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, sq]
      have hB : ∑ t₁ ∈ Todd, (if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ)) =
          (Todd.card : ℝ) ^ 2 := by
        have : ∀ t₁ ∈ Todd,
            (if t₁ % 2 = 0 then (Teven.card : ℝ) else (Todd.card : ℝ)) = (Todd.card : ℝ) := by
          intro t₁ ht₁; simp [(Finset.mem_filter.mp ht₁).2]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, sq]
      rw [hA, hB]
    rw [hpair_eq]
    have hsq2 : (T.card : ℝ) ^ 2 / 2 ≤ (Teven.card : ℝ) ^ 2 + (Todd.card : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((Teven.card : ℝ) - (Todd.card : ℝ)), hcard_sum]
    calc (S₁ / (2 * (N : ℝ))) * (T.card : ℝ) ^ 2
        = (S₁ / (N : ℝ)) * ((T.card : ℝ) ^ 2 / 2) := by ring
      _ ≤ (S₁ / (N : ℝ)) * ((Teven.card : ℝ) ^ 2 + (Todd.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq2 (by positivity)
  -- Step 3: Bound `|I(η)| ≤ U * |T|` via `dft_3ap_identity` + `dft_parseval`
  have hIη_eq :
      ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N, (if t₁ + t₂ = 2 * x then η x else 0) =
      (∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N, (if t₁ + t₂ = 2 * x then μ₀ x else 0)) -
      (∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
        (if t₁ + t₂ = 2 * x then (S₁ / (N : ℝ)) * u₀ x else 0)) := by
    simp_rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t₁ _ =>
      Finset.sum_congr rfl fun t₂ _ =>
        Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    dsimp only [η, μ₀, u₀]
    split_ifs <;> simp [hx]
  have hIη_le :
      |∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N, (if t₁ + t₂ = 2 * x then η x else 0)| ≤
      U * (T.card : ℝ) := by
    rw [← dft_3ap_identity hT η (fun x hx => by dsimp only [η]; rw [if_neg (by omega)])]
    rw [abs_mul, abs_of_pos (div_pos one_pos hMposR)]
    have hparseval : ∑ ξ ∈ Finset.range M, ‖dft M indT ξ‖ ^ 2 = (M : ℝ) * (T.card : ℝ) := by
      rw [dft_parseval hMpos indT]
      congr 1
      have hTM : T ⊆ Finset.range M := Subset.trans hT (Finset.range_mono (by dsimp only [M]; omega))
      rw [← Finset.sum_subset hTM]
      · have : ∀ x ∈ T, (indT x) ^ 2 = 1 := fun x hx => by simp [indT, hx]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
      · intro x _ hx; simp [indT, hx]
    have hnorm_sum :
        |(∑ ξ ∈ Finset.range M, (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M η (2 * ξ))).re| ≤
        (M : ℝ) * (T.card : ℝ) * U := by
      calc |(∑ ξ ∈ Finset.range M, (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M η (2 * ξ))).re|
          ≤ ‖∑ ξ ∈ Finset.range M, (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M η (2 * ξ))‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ∑ ξ ∈ Finset.range M, ‖(dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M η (2 * ξ))‖ :=
            norm_sum_le _ _
        _ = ∑ ξ ∈ Finset.range M, ‖dft M indT ξ‖ ^ 2 * ‖dft M η ((2 * ξ) % M)‖ := by
            refine Finset.sum_congr rfl fun ξ _ => ?_
            rw [norm_mul, norm_pow, Complex.norm_conj, dft_mod hMpos η (2 * ξ)]
        _ ≤ ∑ ξ ∈ Finset.range M, ‖dft M indT ξ‖ ^ 2 * U := by
            refine Finset.sum_le_sum fun ξ _ =>
              mul_le_mul_of_nonneg_left (hU ((2 * ξ) % M) (Nat.mod_lt _ hMpos)) (sq_nonneg _)
        _ = (∑ ξ ∈ Finset.range M, ‖dft M indT ξ‖ ^ 2) * U := (Finset.sum_mul ..).symm
        _ = (M : ℝ) * (T.card : ℝ) * U := by rw [hparseval]
    calc (1 / (M : ℝ)) *
          |(∑ ξ ∈ Finset.range M, (dft M indT ξ) ^ 2 * starRingEnd ℂ (dft M η (2 * ξ))).re|
        ≤ (1 / (M : ℝ)) * ((M : ℝ) * (T.card : ℝ) * U) :=
          mul_le_mul_of_nonneg_left hnorm_sum (by positivity)
      _ = U * (T.card : ℝ) := by field_simp [hMposR.ne']
  -- Step 4: Solve quadratic `(S₁ / (2 N)) |T|^2 - S₁ ≤ U |T|`
  have hquad : (S₁ / (2 * (N : ℝ))) * (T.card : ℝ) ^ 2 - S₁ ≤ U * (T.card : ℝ) := by
    have hneg : -(∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ x ∈ Finset.range N,
        if t₁ + t₂ = 2 * x then η x else 0) ≤ U * (T.card : ℝ) := (abs_le.mp hIη_le).1 |> fun h => by linarith
    linarith only [hIμ, hIu, hIη_eq, hneg]
  have hquad2 : (T.card : ℝ) ^ 2 ≤ (2 * (N : ℝ) / S₁) * U * (T.card : ℝ) + 2 * (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 2 * (N : ℝ) / S₁ by positivity)
    have hL : (2 * (N : ℝ) / S₁) * ((S₁ / (2 * (N : ℝ))) * (T.card : ℝ) ^ 2 - S₁) =
        (T.card : ℝ) ^ 2 - 2 * (N : ℝ) := by
      field_simp [hS₁_pos.ne', hNpos.ne']
    have hR : (2 * (N : ℝ) / S₁) * (U * (T.card : ℝ)) =
        (2 * (N : ℝ) / S₁) * U * (T.card : ℝ) := by ring
    linarith only [hmul, hL, hR]
  set A : ℝ := (2 * (N : ℝ) / S₁) * U
  set B : ℝ := Real.sqrt (2 * (N : ℝ))
  have hA_nn : 0 ≤ A := by dsimp only [A]; positivity
  have hB_nn : 0 ≤ B := Real.sqrt_nonneg _
  have hB_sq : B ^ 2 = 2 * (N : ℝ) := Real.sq_sqrt (by positivity)
  by_contra hgt
  push Not at hgt
  nlinarith only [hquad2, hgt, hA_nn, hB_nn, hB_sq]

/-! ### Part 6: Asymptotic Universal `O(N^(11/12))` 3-AP-Free Support Theorem -/

/-- Universal power-saving 3-AP-free support theorem (Theorem T2-B):
for every `C₀ : ℝ`, eventually for all `N`, ANY fractional Sidon measure `μ` on `range N`
with `∑ μ ≥ √N - C₀ N^(1/4)` satisfies:
every subset `T ⊆ range N` forming zero nontrivial linear 3-APs `t₁ + t₂ = 2x` (`t₁ ≠ t₂`,
`μ x > 0`) has `|T| ≤ 66 * N^(11/12)`. -/
theorem universal_3ap_free_superset_asymptotic (C₀ : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ (μ : ℕ → ℝ) (T : Finset ℕ),
        (∀ x < N, 0 ≤ μ x ∧ μ x ≤ 1) →
        (∀ d, 1 ≤ d → d < N → ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) ≤ 1) →
        (Real.sqrt (N : ℝ) - C₀ * (N : ℝ) ^ (1 / 4 : ℝ) ≤ ∑ x ∈ Finset.range N, μ x) →
        T ⊆ Finset.range N →
        (∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ x < N, t₁ ≠ t₂ → t₁ + t₂ = 2 * x → μ x = 0) →
        (T.card : ℝ) ≤ 66 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  set K : ℝ := max 1 |C₀|
  have hK1 : 1 ≤ K := le_max_left 1 |C₀|
  have hC₀_le : C₀ ≤ K := le_trans (le_abs_self C₀) (le_max_right 1 |C₀|)
  set R₀ : ℕ := Nat.ceil (4 * K + 4) + 1
  have hR₀_ge : 4 * K + 4 ≤ (R₀ : ℝ) := by
    have h1 : 4 * K + 4 ≤ (Nat.ceil (4 * K + 4) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (4 * K + 4) : ℝ) ≤ (R₀ : ℝ) := by exact_mod_cast Nat.le_succ _
    linarith only [h1, h2]
  rw [Filter.eventually_atTop]
  refine ⟨R₀ ^ 12, ?_⟩
  intro N hNge μ T hbound hac hdense hT h3ap
  have hR₀_ge8 : (8 : ℝ) ≤ (R₀ : ℝ) := by linarith only [hR₀_ge, hK1]
  have hN1 : 1 ≤ N := by
    have hR₀_nat : 1 ≤ R₀ := by dsimp only [R₀]; omega
    exact le_trans (one_le_pow₀ hR₀_nat) hNge
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
  -- Introduce `r = N^(1/12)` so every fractional power is a monomial in `r`
  set r : ℝ := (N : ℝ) ^ (1 / 12 : ℝ)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hNpos _
  have hr_pow : ∀ k : ℕ, r ^ k = (N : ℝ) ^ ((k : ℝ) / 12) := by
    intro k
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1; ring
  have hr12 : r ^ 12 = (N : ℝ) := by
    rw [hr_pow 12]; norm_num
  have hr6 : r ^ 6 = Real.sqrt (N : ℝ) := by
    rw [hr_pow 6, Real.sqrt_eq_rpow]; norm_num
  have hr3 : r ^ 3 = (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hr_pow 3]; norm_num
  have hr11 : r ^ 11 = (N : ℝ) ^ (11 / 12 : ℝ) := by
    rw [hr_pow 11]; norm_num
  have hr_ge_R₀ : (R₀ : ℝ) ≤ r := by
    have hpow : ((R₀ : ℝ)) ^ 12 ≤ r ^ 12 := by rw [hr12]; exact_mod_cast hNge
    by_contra hlt
    push Not at hlt
    have : r ^ 12 < (R₀ : ℝ) ^ 12 := pow_lt_pow_left₀ hlt hr_pos.le (by norm_num)
    linarith only [hpow, this]
  have hr_ge : 4 * K + 4 ≤ r := le_trans hR₀_ge hr_ge_R₀
  have hr8 : (8 : ℝ) ≤ r := by linarith only [hr_ge, hK1]
  -- Bounds on `S₁` and `S₂`
  set S₁ : ℝ := ∑ x ∈ Finset.range N, μ x
  set S₂ : ℝ := ∑ x ∈ Finset.range N, (μ x) ^ 2
  have hμ0 : ∀ x < N, 0 ≤ μ x := fun x hx => (hbound x hx).1
  have hS₂_le_S₁ : S₂ ≤ S₁ := by
    refine Finset.sum_le_sum fun x hx => ?_
    rcases hbound x (Finset.mem_range.mp hx) with ⟨h0, h1⟩
    nlinarith only [h0, h1]
  have hS₁_ub : S₁ ≤ 3 * r ^ 6 := by
    have hL := fractional_sidon_sum_le_two_sqrt hN1 hbound hac
    rw [← hr6] at hL
    have hr6_ge1 : (1 : ℝ) ≤ r ^ 6 := one_le_pow₀ (by linarith only [hr8])
    linarith only [hL, hr6_ge1]
  have hS₂_ub : S₂ ≤ 3 * r ^ 6 := le_trans hS₂_le_S₁ hS₁_ub
  have hS₁_lb_exact : r ^ 6 - K * r ^ 3 ≤ S₁ := by
    rw [← hr6, ← hr3] at hdense
    have hr3_nn : 0 ≤ r ^ 3 := pow_nonneg hr_pos.le 3
    have : C₀ * r ^ 3 ≤ K * r ^ 3 := mul_le_mul_of_nonneg_right hC₀_le hr3_nn
    linarith only [hdense, this]
  have hS₁_lb : (1 / 2 : ℝ) * r ^ 6 ≤ S₁ := by
    have hKr : K * r ^ 3 ≤ (1 / 2 : ℝ) * r ^ 6 := by
      have hr2_ge : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith only [hr8])
      have hK_le : K ≤ (1 / 4 : ℝ) * r := by linarith only [hr_ge]
      have h1 : K * r ^ 3 ≤ (1 / 4 : ℝ) * r ^ 4 := by
        nlinarith only [hK_le, pow_nonneg hr_pos.le 3]
      have h2 : (1 / 4 : ℝ) * r ^ 4 ≤ (1 / 2 : ℝ) * r ^ 6 := by
        have : r ^ 4 ≤ r ^ 6 := by
          calc r ^ 4 = r ^ 4 * 1 := (mul_one _).symm
            _ ≤ r ^ 4 * r ^ 2 := mul_le_mul_of_nonneg_left hr2_ge (pow_nonneg hr_pos.le 4)
            _ = r ^ 6 := by ring
        linarith only [this, pow_nonneg hr_pos.le 6]
      linarith only [h1, h2]
    linarith only [hS₁_lb_exact, hKr]
  have hS₁_pos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁_lb
  have hS₁_sq_lb : r ^ 12 - 2 * K * r ^ 9 ≤ S₁ ^ 2 := by
    have h1 : 0 ≤ r ^ 6 - K * r ^ 3 := by
      have : K * r ^ 3 ≤ (1 / 2 : ℝ) * r ^ 6 := by
        have hr2_ge : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (by linarith only [hr8])
        have hK_le : K ≤ (1 / 4 : ℝ) * r := by linarith only [hr_ge]
        have ha : K * r ^ 3 ≤ (1 / 4 : ℝ) * r ^ 4 := by
          nlinarith only [hK_le, pow_nonneg hr_pos.le 3]
        have hb : r ^ 4 ≤ r ^ 6 := by
          calc r ^ 4 = r ^ 4 * 1 := (mul_one _).symm
            _ ≤ r ^ 4 * r ^ 2 := mul_le_mul_of_nonneg_left hr2_ge (pow_nonneg hr_pos.le 4)
            _ = r ^ 6 := by ring
        linarith only [ha, hb, pow_nonneg hr_pos.le 6]
      linarith only [this, pow_pos hr_pos 6]
    have hsq : (r ^ 6 - K * r ^ 3) ^ 2 ≤ S₁ ^ 2 := pow_le_pow_left₀ h1 hS₁_lb_exact 2
    have hK2 : 0 ≤ K ^ 2 * r ^ 6 := by positivity
    nlinarith only [hsq, hK2]
  -- Choose `H₁ = ⌊r^8⌋`, `H₂ = ⌊r^9⌋`
  set H₁ : ℕ := Nat.floor (r ^ 8)
  set H₂ : ℕ := Nat.floor (r ^ 9)
  have hr8_ge2 : (2 : ℝ) ≤ r ^ 8 := by
    have : (8 : ℝ) ^ 8 ≤ r ^ 8 := pow_le_pow_left₀ (by norm_num) hr8 8
    linarith only [this]
  have hr9_ge2 : (2 : ℝ) ≤ r ^ 9 := by
    have : (8 : ℝ) ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ (by norm_num) hr8 9
    linarith only [this]
  have hH₁_ub : (H₁ : ℝ) ≤ r ^ 8 := Nat.floor_le (pow_nonneg hr_pos.le 8)
  have hH₁_lb : (1 / 2 : ℝ) * r ^ 8 ≤ (H₁ : ℝ) := by
    have hlt := Nat.lt_floor_add_one (r ^ 8)
    linarith only [hlt, hr8_ge2]
  have hH₂_ub : (H₂ : ℝ) ≤ r ^ 9 := Nat.floor_le (pow_nonneg hr_pos.le 9)
  have hH₂_lb : (1 / 2 : ℝ) * r ^ 9 ≤ (H₂ : ℝ) := by
    have hlt := Nat.lt_floor_add_one (r ^ 9)
    linarith only [hlt, hr9_ge2]
  have hH₁_pos : 1 ≤ H₁ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [h0, Nat.cast_zero] at hH₁_lb; linarith only [hH₁_lb, hr8_ge2])
  have hH₂_pos : 1 ≤ H₂ := Nat.one_le_iff_ne_zero.mpr (by
    intro h0; rw [h0, Nat.cast_zero] at hH₂_lb; linarith only [hH₂_lb, hr9_ge2])
  have hH₁_le_N : H₁ ≤ N := by
    have hleR : (H₁ : ℝ) ≤ (N : ℝ) := by
      rw [← hr12]
      have : r ^ 8 ≤ r ^ 12 := by
        calc r ^ 8 = r ^ 8 * 1 := (mul_one _).symm
          _ ≤ r ^ 8 * r ^ 4 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith only [hr8])) (pow_nonneg hr_pos.le 8)
          _ = r ^ 12 := by ring
      linarith only [hH₁_ub, this]
    exact_mod_cast hleR
  -- Uniform Fourier bound `‖dft (2N+1) η ξ‖ ≤ 16 * r^5` for all `ξ < 2N + 1`
  have hU_all : ∀ ξ < 2 * N + 1,
      ‖dft (2 * N + 1) (fun x => if x < N then μ x - S₁ / (N : ℝ) else 0) ξ‖ ≤ 16 * r ^ 5 := by
    intro ξ hξM
    by_cases hsmall : 2 * H₁ * min ξ (2 * N + 1 - ξ) ≤ 2 * N + 1
    · -- Small-frequency regime
      have hsm := small_freq_eta_bound hN1 hH₁_pos hH₁_le_N hμ0 hac hξM hsmall
      set N₁ : ℕ := N + H₁ - 1
      have hN₁_ge : r ^ 12 ≤ (N₁ : ℝ) := by
        rw [hr12]; exact_mod_cast (show N ≤ N₁ by dsimp only [N₁]; omega)
      have hN₁_le : (N₁ : ℝ) ≤ 2 * r ^ 12 := by
        have h1 : (N₁ : ℝ) = (N : ℝ) + ((H₁ - 1 : ℕ) : ℝ) := by
          have : N₁ = N + (H₁ - 1) := by dsimp only [N₁]; omega
          exact_mod_cast this
        have h2 : ((H₁ - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show H₁ - 1 ≤ N by omega)
        rw [h1, ← hr12]; linarith only [h2, hr12]
      have hN₁_pos : (0 : ℝ) < (N₁ : ℝ) := lt_of_lt_of_le (pow_pos hr_pos 12) hN₁_ge
      have hN₁_sub_S₁sq : (N₁ : ℝ) - S₁ ^ 2 ≤ 3 * K * r ^ 9 := by
        have h1 : (N₁ : ℝ) ≤ r ^ 12 + r ^ 8 := by
          have : (N₁ : ℝ) ≤ (N : ℝ) + (H₁ : ℝ) := by
            exact_mod_cast (show N₁ ≤ N + H₁ by dsimp only [N₁]; omega)
          rw [← hr12] at this; linarith only [this, hH₁_ub]
        have hr8_le_r9 : r ^ 8 ≤ r ^ 9 := by
          calc r ^ 8 = r ^ 8 * 1 := (mul_one _).symm
            _ ≤ r ^ 8 * r := mul_le_mul_of_nonneg_left (by linarith only [hr8]) (pow_nonneg hr_pos.le 8)
            _ = r ^ 9 := by ring
        have : r ^ 8 ≤ K * r ^ 9 := by
          calc r ^ 8 ≤ r ^ 9 := hr8_le_r9
            _ = 1 * r ^ 9 := (one_mul _).symm
            _ ≤ K * r ^ 9 := mul_le_mul_of_nonneg_right hK1 (pow_nonneg hr_pos.le 9)
        linarith only [h1, hS₁_sq_lb, this]
      have hV_le :
          (H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ) ≤
          4 * r ^ 14 := by
        have hterm1 : (H₁ : ℝ) * S₂ ≤ 3 * r ^ 14 := by
          calc (H₁ : ℝ) * S₂ ≤ r ^ 8 * (3 * r ^ 6) :=
                mul_le_mul hH₁_ub hS₂_ub (Finset.sum_nonneg fun x _ => sq_nonneg _) (pow_nonneg hr_pos.le 8)
            _ = 3 * r ^ 14 := by ring
        have hterm2 :
            (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ) ≤ r ^ 14 := by
          have hrew : (H₁ : ℝ) ^ 2 - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ) =
              (H₁ : ℝ) ^ 2 * ((N₁ : ℝ) - S₁ ^ 2) / (N₁ : ℝ) := by
            field_simp [hN₁_pos.ne']
          have hfrac : (H₁ : ℝ) ^ 2 * ((N₁ : ℝ) - S₁ ^ 2) / (N₁ : ℝ) ≤ r ^ 14 := by
            rw [div_le_iff₀ hN₁_pos]
            have hnum : (H₁ : ℝ) ^ 2 * ((N₁ : ℝ) - S₁ ^ 2) ≤ (r ^ 8) ^ 2 * (3 * K * r ^ 9) := by
              have hH1sq : (H₁ : ℝ) ^ 2 ≤ (r ^ 8) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hH₁_ub 2
              by_cases hsign : 0 ≤ (N₁ : ℝ) - S₁ ^ 2
              · exact mul_le_mul hH1sq hN₁_sub_S₁sq hsign (sq_nonneg _)
              · have hL : (H₁ : ℝ) ^ 2 * ((N₁ : ℝ) - S₁ ^ 2) ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (le_of_not_ge hsign)
                have hR : 0 ≤ (r ^ 8) ^ 2 * (3 * K * r ^ 9) := by positivity
                linarith only [hL, hR]
            have h3K : 3 * K ≤ r := by linarith only [hr_ge, hK1]
            have hcmp : (r ^ 8) ^ 2 * (3 * K * r ^ 9) ≤ r ^ 14 * r ^ 12 := by
              have : 3 * K * r ^ 25 ≤ r * r ^ 25 :=
                mul_le_mul_of_nonneg_right h3K (pow_nonneg hr_pos.le 25)
              linarith only [this]
            have hRHS : r ^ 14 * r ^ 12 ≤ r ^ 14 * (N₁ : ℝ) :=
              mul_le_mul_of_nonneg_left hN₁_ge (pow_nonneg hr_pos.le 14)
            linarith only [hnum, hcmp, hRHS]
          have hH1_nn : (0 : ℝ) ≤ (H₁ : ℝ) := Nat.cast_nonneg _
          nlinarith only [hrew, hfrac, hH1_nn]
        linarith only [hterm1, hterm2]
      have hsqrt_le :
          Real.sqrt ((N₁ : ℝ) *
            ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ))) ≤
          3 * r ^ 13 := by
        refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
        have h1 : (N₁ : ℝ) *
            ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ)) ≤
            (2 * r ^ 12) * (4 * r ^ 14) := by
          have hstep1 := mul_le_mul_of_nonneg_left hV_le hN₁_pos.le
          have hstep2 := mul_le_mul_of_nonneg_right hN₁_le (show 0 ≤ 4 * r ^ 14 by positivity)
          linarith only [hstep1, hstep2]
        have h2 : (2 * r ^ 12) * (4 * r ^ 14) ≤ (3 * r ^ 13) ^ 2 := by
          have : (0 : ℝ) ≤ r ^ 26 := pow_nonneg hr_pos.le 26
          linarith only [this]
        linarith only [h1, h2]
      have hbd_le : 3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) ≤ r ^ 13 := by
        rw [div_le_iff₀ hNpos, ← hr12]
        have hH1sq : (H₁ : ℝ) ^ 2 ≤ (r ^ 8) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hH₁_ub 2
        have h1 : 3 * (H₁ : ℝ) ^ 2 * S₁ ≤ 3 * (r ^ 8) ^ 2 * (3 * r ^ 6) := by
          have ha : (H₁ : ℝ) ^ 2 * S₁ ≤ (r ^ 8) ^ 2 * (3 * r ^ 6) :=
            mul_le_mul hH1sq hS₁_ub hS₁_pos.le (sq_nonneg _)
          linarith only [ha]
        have hr3_ge9 : (9 : ℝ) ≤ r ^ 3 := by
          have : (8 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr8 3
          linarith only [this]
        have h2 : 9 * r ^ 22 ≤ r ^ 13 * r ^ 12 := by
          have := mul_le_mul_of_nonneg_right hr3_ge9 (pow_nonneg hr_pos.le 22)
          linarith only [this]
        linarith only [h1, h2]
      have hpref : Real.pi / (2 * (H₁ : ℝ)) ≤ 4 / r ^ 8 := by
        have hpi4 : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
        have hden : r ^ 8 ≤ 2 * (H₁ : ℝ) := by linarith only [hH₁_lb]
        calc Real.pi / (2 * (H₁ : ℝ))
            ≤ 4 / (2 * (H₁ : ℝ)) := div_le_div_of_nonneg_right hpi4 (by positivity)
          _ ≤ 4 / r ^ 8 := div_le_div_of_nonneg_left (by norm_num) (pow_pos hr_pos 8) hden
      have htot :
          (Real.pi / (2 * (H₁ : ℝ))) *
            (Real.sqrt ((N₁ : ℝ) *
              ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ))) +
              3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ)) ≤
          16 * r ^ 5 := by
        have hsum_le :
            Real.sqrt ((N₁ : ℝ) *
              ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ))) +
              3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) ≤ 4 * r ^ 13 := by
          linarith only [hsqrt_le, hbd_le]
        have hsum_nn :
            0 ≤ Real.sqrt ((N₁ : ℝ) *
              ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ))) +
              3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ) := by positivity
        calc (Real.pi / (2 * (H₁ : ℝ))) *
              (Real.sqrt ((N₁ : ℝ) *
                ((H₁ : ℝ) * S₂ + (H₁ : ℝ) * ((H₁ : ℝ) - 1) - (H₁ : ℝ) ^ 2 * S₁ ^ 2 / (N₁ : ℝ))) +
                3 * (H₁ : ℝ) ^ 2 * S₁ / (N : ℝ))
            ≤ (4 / r ^ 8) * (4 * r ^ 13) :=
              mul_le_mul hpref hsum_le hsum_nn (by positivity)
          _ = 16 * r ^ 5 := by field_simp [hr_pos.ne']; ring
      exact le_trans hsm htot
    · -- Large-frequency regime
      push Not at hsmall
      have hξ1 : 1 ≤ ξ := by
        by_contra h0
        have : ξ = 0 := by omega
        subst this; simp at hsmall
      have hlg := large_freq_eta_bound hN1 hH₁_pos hH₂_pos hμ0 hac hξ1 hξM hsmall
      set N₂ : ℕ := N + H₂ - 1
      have hN₂_le : (N₂ : ℝ) ≤ 2 * r ^ 12 := by
        have h1 : (N₂ : ℝ) ≤ (N : ℝ) + (H₂ : ℝ) := by
          exact_mod_cast (show N₂ ≤ N + H₂ by dsimp only [N₂]; omega)
        have hr9_le : r ^ 9 ≤ r ^ 12 := by
          calc r ^ 9 = r ^ 9 * 1 := (mul_one _).symm
            _ ≤ r ^ 9 * r ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith only [hr8])) (pow_nonneg hr_pos.le 9)
            _ = r ^ 12 := by ring
        rw [← hr12] at h1; linarith only [h1, hH₂_ub, hr9_le]
      have hN₂_sub_S₁sq : (N₂ : ℝ) - S₁ ^ 2 ≤ r ^ 10 := by
        have h1 : (N₂ : ℝ) ≤ r ^ 12 + r ^ 9 := by
          have : (N₂ : ℝ) ≤ (N : ℝ) + (H₂ : ℝ) := by
            exact_mod_cast (show N₂ ≤ N + H₂ by dsimp only [N₂]; omega)
          rw [← hr12] at this; linarith only [this, hH₂_ub]
        have h2K1 : 2 * K + 1 ≤ r := by linarith only [hr_ge, hK1]
        have h2 : (2 * K + 1) * r ^ 9 ≤ r * r ^ 9 :=
          mul_le_mul_of_nonneg_right h2K1 (pow_nonneg hr_pos.le 9)
        linarith only [h1, hS₁_sq_lb, h2]
      have hH1_div_H2 : ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 ≤ 4 / r ^ 2 := by
        have h1 : (H₁ : ℝ) / (H₂ : ℝ) ≤ 2 / r := by
          rw [div_le_div_iff₀ (Nat.cast_pos.mpr hH₂_pos) hr_pos]
          have : r ^ 8 * r = r ^ 9 := by ring
          nlinarith only [hH₁_ub, hH₂_lb, this, hr_pos]
        have hsq := pow_le_pow_left₀ (by positivity) h1 2
        have : (2 / r) ^ 2 = 4 / r ^ 2 := by ring
        linarith only [hsq, this]
      have hS2_div_H2 : 2 * (S₂ - 1) / (H₂ : ℝ) ≤ 2 / r ^ 2 := by
        rw [div_le_div_iff₀ (Nat.cast_pos.mpr hH₂_pos) (sq_pos_of_pos hr_pos)]
        have h1 : 2 * (S₂ - 1) * r ^ 2 ≤ 6 * r ^ 8 := by
          have : 2 * (S₂ - 1) ≤ 6 * r ^ 6 := by linarith only [hS₂_ub]
          have := mul_le_mul_of_nonneg_right this (sq_nonneg r)
          linarith only [this]
        have h2 : 6 * r ^ 8 ≤ r ^ 9 := by
          have := mul_le_mul_of_nonneg_right (show (6 : ℝ) ≤ r by linarith only [hr8])
            (pow_nonneg hr_pos.le 8)
          linarith only [this]
        have h3 : r ^ 9 ≤ 2 * (H₂ : ℝ) := by linarith only [hH₂_lb]
        linarith only [h1, h2, h3]
      have hW_le :
          (N₂ : ℝ) * (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2 ≤
          (4 * r ^ 5) ^ 2 := by
        have hrew :
            (N₂ : ℝ) * (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2 =
            ((N₂ : ℝ) - S₁ ^ 2) +
              (N₂ : ℝ) * (((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) := by ring
        rw [hrew]
        have hN₂_nn : (0 : ℝ) ≤ (N₂ : ℝ) := Nat.cast_nonneg _
        have hterm2 :
            (N₂ : ℝ) * (((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) ≤ 12 * r ^ 10 := by
          have hsum : ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ) ≤ 6 / r ^ 2 := by
            have h6 : 4 / r ^ 2 + 2 / r ^ 2 = 6 / r ^ 2 := by ring
            linarith only [hH1_div_H2, hS2_div_H2, h6]
          have h1 := mul_le_mul_of_nonneg_left hsum hN₂_nn
          have h2 := mul_le_mul_of_nonneg_right hN₂_le (show 0 ≤ 6 / r ^ 2 by positivity)
          have h3 : 2 * r ^ 12 * (6 / r ^ 2) = 12 * r ^ 10 := by
            field_simp [hr_pos.ne']; ring
          linarith only [h1, h2, h3]
        have hsq : 13 * r ^ 10 ≤ (4 * r ^ 5) ^ 2 := by
          have : (0 : ℝ) ≤ r ^ 10 := pow_nonneg hr_pos.le 10
          linarith only [this]
        linarith only [hN₂_sub_S₁sq, hterm2, hsq]
      have hsqrt_W :
          Real.sqrt ((N₂ : ℝ) *
            (1 + ((H₁ : ℝ) / (H₂ : ℝ)) ^ 2 + 2 * (S₂ - 1) / (H₂ : ℝ)) - S₁ ^ 2) ≤ 4 * r ^ 5 :=
        Real.sqrt_le_iff.mpr ⟨by positivity, hW_le⟩
      have hlin_le : S₁ * (H₁ : ℝ) / (N : ℝ) ≤ r ^ 5 := by
        rw [div_le_iff₀ hNpos, ← hr12]
        have h1 : S₁ * (H₁ : ℝ) ≤ (3 * r ^ 6) * r ^ 8 :=
          mul_le_mul hS₁_ub hH₁_ub (Nat.cast_nonneg _) (by positivity)
        have hr3_ge3 : (3 : ℝ) ≤ r ^ 3 := by
          have : (8 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr8 3
          linarith only [this]
        have h2 : 3 * r ^ 14 ≤ r ^ 5 * r ^ 12 := by
          have := mul_le_mul_of_nonneg_right hr3_ge3 (pow_nonneg hr_pos.le 14)
          linarith only [this]
        linarith only [h1, h2]
      have hr5_nn : 0 ≤ r ^ 5 := pow_nonneg hr_pos.le 5
      linarith only [hlg, hsqrt_W, hlin_le, hr5_nn]
  -- Apply `universal_3ap_free_superset_from_U` with `U = 16 * r^5`
  have hTbound := universal_3ap_free_superset_from_U hN1 hμ0 hS₁_pos hT h3ap
    (show 0 ≤ 16 * r ^ 5 by positivity) hU_all
  have hmain : (2 * (N : ℝ) / S₁) * (16 * r ^ 5) ≤ 64 * r ^ 11 := by
    have hdiv : 2 * (N : ℝ) / S₁ ≤ 4 * r ^ 6 := by
      rw [div_le_iff₀ hS₁_pos, ← hr12]
      nlinarith only [hS₁_lb, pow_pos hr_pos 6]
    have hmul := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ 16 * r ^ 5 by positivity)
    linarith only [hmul]
  have hsqrt2N : Real.sqrt (2 * (N : ℝ)) ≤ 2 * r ^ 11 := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [← hr12]
    have hr10_ge1 : (1 : ℝ) ≤ r ^ 10 := one_le_pow₀ (by linarith only [hr8])
    have : 2 * r ^ 12 ≤ 4 * r ^ 22 := by
      have h1 : r ^ 12 ≤ r ^ 22 := by
        calc r ^ 12 = r ^ 12 * 1 := (mul_one _).symm
          _ ≤ r ^ 12 * r ^ 10 := mul_le_mul_of_nonneg_left hr10_ge1 (pow_nonneg hr_pos.le 12)
          _ = r ^ 22 := by ring
      linarith only [h1, pow_nonneg hr_pos.le 12]
    linarith only [this]
  rw [← hr11]
  linarith only [hTbound, hmain, hsqrt2N]

end Erdos030
