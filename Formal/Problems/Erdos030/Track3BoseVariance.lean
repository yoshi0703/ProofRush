import Problems.Erdos030.Statement
import Problems.Erdos030.PeriodicDFT
import Mathlib.Tactic

/-!
# Track 3 Formal Theorems: Bose Sparse-Background Cross-Variance (T3-B) & Binary-Autocorrelation Rigidity (T3-A)

Formalizes:
1. **Theorem T3-B (`bose_sparse_background_cross_variance_of_flat`)**:
   Exact Parseval cross-variance lower bound for EVERY prime `p` (`M = p^2 - 1`) and ANY
   nonnegative `ν` on `range M` with linear autocorrelation `≤ 1`:
   `∑_{d < M} ((1_{S_p} ⋆_cyc ν)(d) - p ‖ν‖_1 / M)^2 ≥ (p(p-2)/(p-1)) (‖ν‖_2^2 - 2)`
   and for `supp(ν) ⊆ T` (`|T| ≥ 1`), `≥ (p(p-2)/(p-1)) (‖ν‖_1^2 / |T| - 2)`.
2. **Theorem T3-A (`binary_autocorr_counterexample_N3`, `binary_autocorr_endpoint_rigidity`)**:
   Strict counterexample `μ = (1, 1/2, 1)` at `N = 3` (`r_μ(1) = r_μ(2) = 1`, `∑ μ = 5/2 > 2 = h(3)`),
   plus exact endpoint rigidity `μ_a = μ_b = 1` for every binary-autocorrelation measure with
   `|supp(μ)| ≥ 2`.
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-! ### Part 1: Theorem T3-B — Exact Bose Sparse-Background Parseval Cross-Variance -/

/-- Helper: cyclic autocorrelation of a nonnegative measure with linear autocorrelation `≤ 1`
satisfies `cyclicXcorr M ν ν d ≤ 2` for every `1 ≤ d < M`. -/
lemma cyclicXcorr_le_two_of_linear_ac_le_one {M d : ℕ} (hd1 : 1 ≤ d) (hdM : d < M)
    {ν : ℕ → ℝ} (hν_ac : ∀ k, 1 ≤ k → k < M → ∑ x ∈ Finset.range (M - k), ν x * ν (x + k) ≤ 1) :
    cyclicXcorr M ν ν d ≤ 2 := by
  have hlin := linear_autocorr_eq_cyclic_sub_wrap hdM ν
  have hwrap : ∑ x ∈ Finset.Ico (M - d) M, ν x * ν (x + d - M) =
      ∑ y ∈ Finset.range (M - (M - d)), ν y * ν (y + (M - d)) := by
    refine Finset.sum_nbij (fun x => x + d - M) ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      dsimp only at hab; omega
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_range] at hy
      refine ⟨y + (M - d), Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
        by dsimp; omega⟩
    · intro x hx
      rw [Finset.mem_Ico] at hx
      rw [show x + d - M + (M - d) = x by omega, mul_comm]
  have h1 := hν_ac d hd1 hdM
  have h2 := hν_ac (M - d) (by omega) (by omega)
  linarith

/-- Theorem T3-B (Core): Exact Bose Sparse-Background Parseval Cross-Variance Lower Bound.
For EVERY prime `p` (`M = p^2 - 1`), Bose's Sidon set `S ⊆ range M` with `|S| = p` and
exact periodic Fourier flatness, and ANY nonnegative `ν : ℕ → ℝ` with linear autocorrelation `≤ 1`:
1. `((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) * ((∑ x < M, (ν x)^2) - 2) ≤`
   `∑ d < M, (cyclicConv M 1_S ν d - p * (∑ x < M, ν x) / M)^2`;
2. If additionally `T ⊆ range M`, `1 ≤ T.card`, and `∀ x < M, x ∉ T → ν x = 0`, then
   `((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) * ((∑ x < M, ν x)^2 / T.card - 2) ≤`
   `∑ d < M, (cyclicConv M 1_S ν d - p * (∑ x < M, ν x) / M)^2`. -/
theorem bose_sparse_background_cross_variance_of_flat {p : ℕ} (hp : p.Prime)
    {S : Finset ℕ} (hS_sub : S ⊆ Finset.range (p ^ 2 - 1)) (hS_card : S.card = p)
    (hflat : ∀ ξ : ℕ, 1 ≤ ξ → ξ < p ^ 2 - 1 →
      ‖∑ a ∈ S, (rootOfUnity (p ^ 2 - 1)) ^ (ξ * a)‖ ^ 2 =
        if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ))
    {ν : ℕ → ℝ} (hν_ac : ∀ d, 1 ≤ d → d < p ^ 2 - 1 →
      ∑ x ∈ Finset.range (p ^ 2 - 1 - d), ν x * ν (x + d) ≤ 1) :
    let M : ℕ := p ^ 2 - 1
    let indS : ℕ → ℝ := fun x => if x ∈ S then 1 else 0
    let V : ℝ := ∑ d ∈ Finset.range M,
      (cyclicConv M indS ν d - (p : ℝ) * (∑ x ∈ Finset.range M, ν x) / (M : ℝ)) ^ 2
    ((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2) ≤ V ∧
    ∀ T : Finset ℕ, T ⊆ Finset.range M → 1 ≤ T.card →
      (∀ x, x < M → x ∉ T → ν x = 0) →
      ((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
        ((∑ x ∈ Finset.range M, ν x) ^ 2 / (T.card : ℝ) - 2) ≤ V := by
  classical
  intro M indS V
  have hp2 : 2 ≤ p := hp.two_le
  have hM_fac : M = (p - 1) * (p + 1) := by
    dsimp only [M]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hM_pos : 0 < M := by rw [hM_fac]; exact Nat.mul_pos (by omega) (by omega)
  have hM_posR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hp_posR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp1_posR : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hM_facR : (M : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by
    have h1 : (M : ℝ) = ((p - 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ) := by exact_mod_cast hM_fac
    rw [h1, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  -- Step 1: Parseval for centered convolution `g(d) = (1_S ⋆_cyc ν)(d) - p * ‖ν‖_1 / M`
  let mean : ℝ := (p : ℝ) * (∑ x ∈ Finset.range M, ν x) / (M : ℝ)
  let g : ℕ → ℝ := fun d => cyclicConv M indS ν d - mean
  have hdft_indS : ∀ ξ, dft M indS ξ = ∑ a ∈ S, (rootOfUnity M) ^ (ξ * a) :=
    fun ξ => dft_indicator hS_sub ξ
  have hdft_g_zero : dft M g 0 = 0 := by
    dsimp only [g, mean]
    rw [dft_sub, dft_cyclicConv hM_pos, hdft_indS 0, dft_const hM_pos, if_pos (dvd_zero M),
      dft_zero]
    simp only [zero_mul, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hS_card]
    have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM_pos.ne'
    push_cast; field_simp [hMne]; ring
  have hdft_g_nz : ∀ ξ, 1 ≤ ξ → ξ < M → dft M g ξ = dft M indS ξ * dft M ν ξ := by
    intro ξ hξ1 hξM
    dsimp only [g]
    have hndvd : ¬ M ∣ ξ := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    rw [dft_sub, dft_cyclicConv hM_pos, dft_const hM_pos, if_neg hndvd, sub_zero]
  have hV_parseval : (M : ℝ) * V =
      ∑ ξ ∈ Finset.Ico 1 M, ‖dft M indS ξ‖ ^ 2 * ‖dft M ν ξ‖ ^ 2 := by
    have hpv := dft_parseval hM_pos g
    have hEqV : ∑ d ∈ Finset.range M, (g d) ^ 2 = V := rfl
    rw [hEqV, ← Finset.sum_range_add_sum_Ico _ hM_pos] at hpv
    have h0 : ∑ ξ ∈ Finset.range 1, ‖dft M g ξ‖ ^ 2 = 0 := by simp [hdft_g_zero]
    rw [h0, zero_add] at hpv
    rw [← hpv]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [Finset.mem_Ico] at hξ
    rw [hdft_g_nz ξ hξ.1 hξ.2, norm_mul, mul_pow]
  -- Step 2: Drop `(p - 1) ∣ ξ` modes and use `‖dft M indS ξ‖^2 = p` on `(p - 1) ∤ ξ`
  let A : Finset ℕ := (Finset.range M).filter (fun ξ => ¬ ((p - 1) ∣ ξ))
  let B : Finset ℕ := (Finset.range M).filter (fun ξ => (p - 1) ∣ ξ)
  have hMV_ge : (p : ℝ) * (∑ ξ ∈ A, ‖dft M ν ξ‖ ^ 2) ≤ (M : ℝ) * V := by
    rw [hV_parseval]
    have hA_sub : A ⊆ Finset.Ico 1 M := by
      intro ξ hξ
      rw [Finset.mem_filter, Finset.mem_range] at hξ
      refine Finset.mem_Ico.mpr ⟨?_, hξ.1⟩
      by_contra h0; have : ξ = 0 := by omega
      subst this; exact hξ.2 (dvd_zero _)
    have hA_eq : (p : ℝ) * ∑ ξ ∈ A, ‖dft M ν ξ‖ ^ 2 =
        ∑ ξ ∈ A, ‖dft M indS ξ‖ ^ 2 * ‖dft M ν ξ‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      have hIco := Finset.mem_Ico.mp (hA_sub hξ)
      have hndvd := (Finset.mem_filter.mp hξ).2
      rw [hdft_indS ξ, hflat ξ hIco.1 hIco.2, if_neg hndvd]
    rw [hA_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA_sub fun _ _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- Step 3: Exact evaluation of `∑ ξ ∈ B, ‖dft M ν ξ‖^2 = (p + 1) * ∑_{k < p - 1} AC_cyc(ν)(k*(p+1))`
  have hB_eq : B = (Finset.range (p + 1)).image (fun m => m * (p - 1)) := by
    ext ξ
    simp only [B, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hξM, m, rfl⟩
      refine ⟨m, ?_, by ring⟩
      rw [hM_fac] at hξM; nlinarith
    · rintro ⟨m, hm, rfl⟩
      refine ⟨?_, m, by ring⟩
      rw [hM_fac]; nlinarith
  have hB_sum_eq :
      ∑ ξ ∈ B, ‖dft M ν ξ‖ ^ 2 =
      ((p + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (p - 1), cyclicXcorr M ν ν (k * (p + 1)) := by
    rw [hB_eq, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right (by omega) h)]
    have hre : ∑ m ∈ Finset.range (p + 1), ‖dft M ν (m * (p - 1))‖ ^ 2 =
        (∑ m ∈ Finset.range (p + 1),
          dft M ν (m * (p - 1)) * starRingEnd ℂ (dft M ν (m * (p - 1)))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hre]
    have hsumC :
        ∑ m ∈ Finset.range (p + 1),
          dft M ν (m * (p - 1)) * starRingEnd ℂ (dft M ν (m * (p - 1))) =
        ((p + 1 : ℕ) : ℂ) * ((∑ k ∈ Finset.range (p - 1), cyclicXcorr M ν ν (k * (p + 1)) : ℝ) : ℂ) := by
      unfold dft
      have hexp :
          ∑ m ∈ Finset.range (p + 1),
            (∑ x ∈ Finset.range M, (ν x : ℂ) * (rootOfUnity M) ^ (m * (p - 1) * x)) *
              starRingEnd ℂ (∑ y ∈ Finset.range M, (ν y : ℂ) * (rootOfUnity M) ^ (m * (p - 1) * y)) =
          ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
            ((ν x : ℂ) * (ν y : ℂ)) *
              ∑ m ∈ Finset.range (p + 1), ((rootOfUnity M) ^ ((p - 1) * ((x + M - y) % M))) ^ m := by
        have h1 : ∀ m ∈ Finset.range (p + 1),
            (∑ x ∈ Finset.range M, (ν x : ℂ) * (rootOfUnity M) ^ (m * (p - 1) * x)) *
              starRingEnd ℂ (∑ y ∈ Finset.range M, (ν y : ℂ) * (rootOfUnity M) ^ (m * (p - 1) * y)) =
            ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
              ((ν x : ℂ) * (ν y : ℂ)) * ((rootOfUnity M) ^ ((p - 1) * ((x + M - y) % M))) ^ m := by
          intro m _
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [Finset.mem_range] at hy
          rw [map_mul, Complex.conj_ofReal]
          have hpow := rootOfUnity_conj_mul_eq hM_pos (m * (p - 1)) x y hy.le
          have hmul_pow : (rootOfUnity M) ^ (m * (p - 1) * ((x + M - y) % M)) =
              ((rootOfUnity M) ^ ((p - 1) * ((x + M - y) % M))) ^ m := by
            rw [← pow_mul]; congr 1; ring
          calc (ν x : ℂ) * (rootOfUnity M) ^ (m * (p - 1) * x) *
                ((ν y : ℂ) * starRingEnd ℂ ((rootOfUnity M) ^ (m * (p - 1) * y)))
              = ((ν x : ℂ) * (ν y : ℂ)) *
                  ((rootOfUnity M) ^ (m * (p - 1) * x) *
                    starRingEnd ℂ ((rootOfUnity M) ^ (m * (p - 1) * y))) := by ring
            _ = ((ν x : ℂ) * (ν y : ℂ)) * ((rootOfUnity M) ^ ((p - 1) * ((x + M - y) % M))) ^ m := by
                rw [hpow, hmul_pow]
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
      rw [hexp]
      have hortho_sub : ∀ d : ℕ,
          ∑ m ∈ Finset.range (p + 1), ((rootOfUnity M) ^ ((p - 1) * d)) ^ m =
          if (p + 1) ∣ d then ((p + 1 : ℕ) : ℂ) else 0 := by
        intro d
        by_cases hd : (p + 1) ∣ d
        · rw [if_pos hd]
          have h1 : (rootOfUnity M) ^ ((p - 1) * d) = 1 := by
            rw [rootOfUnity_pow_eq_one_iff_dvd hM_pos]
            rcases hd with ⟨k, rfl⟩
            exact ⟨k, by rw [hM_fac]; ring⟩
          simp [h1]
        · rw [if_neg hd]
          have hne : (rootOfUnity M) ^ ((p - 1) * d) ≠ 1 := by
            intro h1
            have hMdvd := (rootOfUnity_pow_eq_one_iff_dvd hM_pos _).mp h1
            rw [hM_fac] at hMdvd
            exact hd ((mul_dvd_mul_iff_left (by omega : p - 1 ≠ 0)).mp hMdvd)
          rw [geom_sum_eq hne, ← pow_mul,
            show (p - 1) * d * (p + 1) = M * d by rw [hM_fac]; ring,
            pow_mul, rootOfUnity_pow_M hM_pos, one_pow, sub_self, zero_div]
      -- Simplify inner sum via `hortho_sub` and reindex `y = (x + k * (p + 1)) % M`
      have hreidx :
          ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
            ((ν x : ℂ) * (ν y : ℂ)) *
              (if (p + 1) ∣ ((x + M - y) % M) then ((p + 1 : ℕ) : ℂ) else 0) =
          ((p + 1 : ℕ) : ℂ) *
            ∑ k ∈ Finset.range (p - 1), ∑ x ∈ Finset.range M,
              (ν x : ℂ) * (ν ((x + k * (p + 1)) % M) : ℂ) := by
        conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_range] at hx
        rw [Finset.mul_sum]
        -- Filter `y ∈ range M` with `(p + 1) ∣ ((x + M - y) % M)` and biject with `k ∈ range (p - 1)`
        have hstep_y :
            ∑ y ∈ Finset.range M,
              ((ν x : ℂ) * (ν y : ℂ)) *
                (if (p + 1) ∣ ((x + M - y) % M) then ((p + 1 : ℕ) : ℂ) else 0) =
            ∑ y ∈ (Finset.range M).filter (fun y => (p + 1) ∣ ((x + M - y) % M)),
              ((p + 1 : ℕ) : ℂ) * ((ν x : ℂ) * (ν y : ℂ)) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun y _ => by split_ifs <;> ring
        rw [hstep_y]
        symm
        refine Finset.sum_nbij (fun k => (x + k * (p + 1)) % M) ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
          refine ⟨Nat.mod_lt _ hM_pos, ?_⟩
          have hdvdM : (p + 1) ∣ M := ⟨p - 1, by rw [hM_fac]; ring⟩
          have h1 : (x + M - (x + k * (p + 1)) % M) % M = (M - (k * (p + 1)) % M) % M := by
            have hkM : k * (p + 1) < M := by rw [hM_fac]; nlinarith
            by_cases hsum : x + k * (p + 1) < M
            · rw [Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt hkM,
                show x + M - (x + k * (p + 1)) = M - k * (p + 1) by omega]
            · have hmod : (x + k * (p + 1)) % M = x + k * (p + 1) - M := by
                have hlt : x + k * (p + 1) - M < M := by omega
                have hadd : x + k * (p + 1) = (x + k * (p + 1) - M) + M := by omega
                conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
              rw [hmod, Nat.mod_eq_of_lt hkM,
                show x + M - (x + k * (p + 1) - M) = M + (M - k * (p + 1)) by omega,
                Nat.add_mod_left]
          rw [h1]
          have hkM : k * (p + 1) < M := by rw [hM_fac]; nlinarith
          rw [Nat.mod_eq_of_lt hkM]
          have hdvd_sub : (p + 1) ∣ (M - k * (p + 1)) := by
            refine ⟨p - 1 - k, ?_⟩
            have hmul : (p + 1) * (p - 1 - k) = (p + 1) * (p - 1) - (p + 1) * k :=
              Nat.mul_sub_left_distrib (p + 1) (p - 1) k
            have hcomm1 : (p + 1) * (p - 1) = M := by rw [hM_fac]; ring
            have hcomm2 : (p + 1) * k = k * (p + 1) := mul_comm _ _
            omega
          exact Nat.dvd_mod_iff hdvdM |>.mpr hdvd_sub
        · intro k₁ hk₁ k₂ hk₂ heq
          simp only [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
          dsimp only at heq
          have h1 : k₁ * (p + 1) < M := by rw [hM_fac]; nlinarith
          have h2 : k₂ * (p + 1) < M := by rw [hM_fac]; nlinarith
          have hmod1 : (x + k₁ * (p + 1)) % M =
              if x + k₁ * (p + 1) < M then x + k₁ * (p + 1) else x + k₁ * (p + 1) - M := by
            split_ifs with hlt
            · exact Nat.mod_eq_of_lt hlt
            · have hlt2 : x + k₁ * (p + 1) - M < M := by omega
              have hadd : x + k₁ * (p + 1) = (x + k₁ * (p + 1) - M) + M := by omega
              conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
          have hmod2 : (x + k₂ * (p + 1)) % M =
              if x + k₂ * (p + 1) < M then x + k₂ * (p + 1) else x + k₂ * (p + 1) - M := by
            split_ifs with hlt
            · exact Nat.mod_eq_of_lt hlt
            · have hlt2 : x + k₂ * (p + 1) - M < M := by omega
              have hadd : x + k₂ * (p + 1) = (x + k₂ * (p + 1) - M) + M := by omega
              conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
          rw [hmod1, hmod2] at heq
          have hkeq : k₁ * (p + 1) = k₂ * (p + 1) := by split_ifs at heq <;> omega
          exact Nat.eq_of_mul_eq_mul_right (by omega) hkeq
        · intro y hy
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hy
          rcases hy with ⟨hyM, hdvd⟩
          have hdvd2 : (p + 1) ∣ ((y + M - x) % M) := by
            have hdvdM : (p + 1) ∣ M := ⟨p - 1, by rw [hM_fac]; ring⟩
            by_cases h0 : (x + M - y) % M = 0
            · have hxy : x = y := by
                have h1 : (x + M - y) % M = if y ≤ x then x - y else x + M - y := by
                  split_ifs with hyx
                  · rw [show x + M - y = (x - y) + M by omega, Nat.add_mod_right,
                      Nat.mod_eq_of_lt (by omega)]
                  · exact Nat.mod_eq_of_lt (by omega)
                rw [h1] at h0; split_ifs at h0 <;> omega
              subst hxy; rw [show x + M - x = M by omega, Nat.mod_self]; exact dvd_zero _
            · have hcomp : (y + M - x) % M = M - (x + M - y) % M := by
                have h1 : (x + M - y) % M = if y ≤ x then x - y else x + M - y := by
                  split_ifs with hyx
                  · rw [show x + M - y = (x - y) + M by omega, Nat.add_mod_right,
                      Nat.mod_eq_of_lt (by omega)]
                  · exact Nat.mod_eq_of_lt (by omega)
                have h2 : (y + M - x) % M = if x ≤ y then y - x else y + M - x := by
                  split_ifs with hxy
                  · rw [show y + M - x = (y - x) + M by omega, Nat.add_mod_right,
                      Nat.mod_eq_of_lt (by omega)]
                  · exact Nat.mod_eq_of_lt (by omega)
                rw [h1] at h0 ⊢; rw [h2]; split_ifs at h0 ⊢ <;> omega
              rw [hcomp]
              exact Nat.dvd_sub hdvdM hdvd
          rcases hdvd2 with ⟨k, hk⟩
          have hk_lt : k < p - 1 := by
            have hlt : (y + M - x) % M < M := Nat.mod_lt _ hM_pos
            rw [hk, hM_fac] at hlt; nlinarith
          refine ⟨k, Finset.mem_coe.mpr (Finset.mem_range.mpr hk_lt), ?_⟩
          dsimp only
          have h1 : (x + k * (p + 1)) % M = (x + (y + M - x) % M) % M := by
            rw [hk, mul_comm]
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show x + (y + M - x) = y + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hyM]
        · intro k _; rfl
      calc ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
            ((ν x : ℂ) * (ν y : ℂ)) *
              ∑ m ∈ Finset.range (p + 1), ((rootOfUnity M) ^ ((p - 1) * ((x + M - y) % M))) ^ m
          = ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
              ((ν x : ℂ) * (ν y : ℂ)) *
                (if (p + 1) ∣ ((x + M - y) % M) then ((p + 1 : ℕ) : ℂ) else 0) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hortho_sub]
        _ = ((p + 1 : ℕ) : ℂ) *
              ∑ k ∈ Finset.range (p - 1), ∑ x ∈ Finset.range M,
                (ν x : ℂ) * (ν ((x + k * (p + 1)) % M) : ℂ) := hreidx
        _ = ((p + 1 : ℕ) : ℂ) *
              ((∑ k ∈ Finset.range (p - 1), cyclicXcorr M ν ν (k * (p + 1)) : ℝ) : ℂ) := by
            congr 1; unfold cyclicXcorr; push_cast; rfl
    rw [hsumC]
    simp
  -- Step 4: Bound `∑ ξ ∈ B, ‖dft M ν ξ‖^2 ≤ (p + 1) * (‖ν‖_2^2 + 2 * (p - 2))`
  have hB_le :
      ∑ ξ ∈ B, ‖dft M ν ξ‖ ^ 2 ≤
      ((p : ℝ) + 1) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) + 2 * ((p : ℝ) - 2)) := by
    rw [hB_sum_eq]
    have hsplit : ∑ k ∈ Finset.range (p - 1), cyclicXcorr M ν ν (k * (p + 1)) =
        cyclicXcorr M ν ν 0 + ∑ k ∈ Finset.Ico 1 (p - 1), cyclicXcorr M ν ν (k * (p + 1)) := by
      rw [← Finset.sum_range_add_sum_Ico _ (by omega : 1 ≤ p - 1)]
      simp
    have h0 : cyclicXcorr M ν ν 0 = ∑ x ∈ Finset.range M, (ν x) ^ 2 := by
      unfold cyclicXcorr
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx; rw [add_zero, Nat.mod_eq_of_lt hx, sq]
    have hrest : ∑ k ∈ Finset.Ico 1 (p - 1), cyclicXcorr M ν ν (k * (p + 1)) ≤ 2 * ((p : ℝ) - 2) := by
      calc ∑ k ∈ Finset.Ico 1 (p - 1), cyclicXcorr M ν ν (k * (p + 1))
          ≤ ∑ _k ∈ Finset.Ico 1 (p - 1), (2 : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [Finset.mem_Ico] at hk
            refine cyclicXcorr_le_two_of_linear_ac_le_one (by nlinarith) ?_ hν_ac
            rw [hM_fac]; nlinarith
        _ = ((p - 1 - 1 : ℕ) : ℝ) * 2 := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ = 2 * ((p : ℝ) - 2) := by
            have hsub : p - 1 - 1 = p - 2 := by omega
            rw [hsub, Nat.cast_sub hp2, Nat.cast_ofNat]; ring
    rw [hsplit, h0, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- Step 5: Combine with Parseval on `ν` to finish part 1!
  have hAB : ∑ ξ ∈ B, ‖dft M ν ξ‖ ^ 2 + ∑ ξ ∈ A, ‖dft M ν ξ‖ ^ 2 =
      (M : ℝ) * ∑ x ∈ Finset.range M, (ν x) ^ 2 := by
    rw [Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun ξ => (p - 1) ∣ ξ),
      dft_parseval hM_pos ν]
  have hA_ge : ((p : ℝ) + 1) * ((p : ℝ) - 2) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2) ≤
      ∑ ξ ∈ A, ‖dft M ν ξ‖ ^ 2 := by
    have halg : (M : ℝ) * (∑ x ∈ Finset.range M, (ν x) ^ 2) -
        ((p : ℝ) + 1) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) + 2 * ((p : ℝ) - 2)) =
        ((p : ℝ) + 1) * ((p : ℝ) - 2) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2) := by
      rw [hM_facR]; ring
    linarith
  have hpart1 : ((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
      ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2) ≤ V := by
    have hmul : (M : ℝ) * (((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
        ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2)) ≤ (M : ℝ) * V := by
      have hLHS_eq : (M : ℝ) * (((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
          ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2)) =
          (p : ℝ) * (((p : ℝ) + 1) * ((p : ℝ) - 2) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2)) := by
        rw [hM_facR]; field_simp [hp1_posR.ne']
      rw [hLHS_eq]
      exact (mul_le_mul_of_nonneg_left hA_ge hp_posR.le).trans hMV_ge
    exact le_of_mul_le_mul_left hmul hM_posR
  refine ⟨hpart1, ?_⟩
  -- Step 6: Cauchy-Schwarz on support `T` for part 2
  intro T hT_sub hT_card hT_supp
  have hsum1 : ∑ x ∈ Finset.range M, ν x = ∑ x ∈ T, ν x := by
    symm; refine Finset.sum_subset hT_sub fun x hx hxT => hT_supp x (Finset.mem_range.mp hx) hxT
  have hsum2 : ∑ x ∈ Finset.range M, (ν x) ^ 2 = ∑ x ∈ T, (ν x) ^ 2 := by
    symm; refine Finset.sum_subset hT_sub fun x hx hxT => by
      rw [hT_supp x (Finset.mem_range.mp hx) hxT, zero_pow (by norm_num)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) ν
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hTposR : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.mpr hT_card
  have hL2_ge : (∑ x ∈ Finset.range M, ν x) ^ 2 / (T.card : ℝ) ≤ ∑ x ∈ Finset.range M, (ν x) ^ 2 := by
    rw [hsum1, hsum2, div_le_iff₀ hTposR]; linarith
  have hcoeff_nn : 0 ≤ (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    exact div_nonneg (mul_nonneg hp_posR.le (by linarith)) hp1_posR.le
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hL2_ge 2) hcoeff_nn).trans hpart1

/-! ### Part 2: Theorem T3-A — Binary-Autocorrelation Counterexample & Endpoint Rigidity -/

/-- Exact evaluation `h(3) = 2` (attained by `{1, 2}`). -/
theorem h_3_eq_2 : h 3 = 2 := by
  classical
  have hle : h 3 ≤ 2 := by
    unfold h maxSidonSubsetCard
    refine Finset.sup_le fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    by_contra hgt; push Not at hgt
    have hAeq : A = Finset.Icc 1 3 :=
      Finset.eq_of_subset_of_card_le hA.1 (by rw [show (Finset.Icc 1 3).card = 3 by decide]; exact hgt)
    subst hAeq
    have h1 : 1 ∈ (Finset.Icc 1 3 : Set ℕ) := by simp
    have h2 : 2 ∈ (Finset.Icc 1 3 : Set ℕ) := by simp
    have h3 : 3 ∈ (Finset.Icc 1 3 : Set ℕ) := by simp
    have := hA.2 1 h1 3 h3 2 h2 2 h2 (by omega)
    omega
  have hge : 2 ≤ h 3 := by
    let A : Finset ℕ := {1, 2}
    have hsub : A ⊆ Finset.Icc 1 3 := by decide
    have hS : IsSidon (A : Set ℕ) := by
      intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
      simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha₁ hb₁ ha₂ hb₂
      rcases ha₁ with rfl | rfl <;> rcases hb₁ with rfl | rfl <;>
        rcases ha₂ with rfl | rfl <;> rcases hb₂ with rfl | rfl <;> omega
    have hmem : A ∈ (Finset.Icc 1 3).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hS⟩
    have hc : A.card = 2 := by decide
    rw [← hc]; exact Finset.le_sup (f := Finset.card) hmem
  omega

/-- Theorem T3-A (Counterexample): Binary autocorrelation `r_μ(d) ∈ {0, 1}` for all `1 ≤ d < N`
does NOT force `μ ∈ {0, 1}^N`: at `N = 3`, `μ = (1, 1/2, 1)` satisfies `r_μ(1) = r_μ(2) = 1`
and `∑ μ = 5/2 > 2 = h(3)`. -/
theorem binary_autocorr_counterexample_N3 :
    h 3 = 2 ∧
    ∃ μ : ℕ → ℝ,
      (∀ x, x < 3 → 0 ≤ μ x ∧ μ x ≤ 1) ∧
      (∀ d, 1 ≤ d → d < 3 →
        (∑ x ∈ Finset.range (3 - d), μ x * μ (x + d) = 0 ∨
         ∑ x ∈ Finset.range (3 - d), μ x * μ (x + d) = 1)) ∧
      (∃ x, x < 3 ∧ μ x ≠ 0 ∧ μ x ≠ 1) ∧
      ∑ x ∈ Finset.range 3, μ x = (5 : ℝ) / 2 := by
  refine ⟨h_3_eq_2, ?_⟩
  let μ : ℕ → ℝ := fun i => match i with | 0 => 1 | 1 => 1 / 2 | 2 => 1 | _ => 0
  refine ⟨μ, ?_, ?_, ⟨1, by omega, by norm_num [μ], by norm_num [μ]⟩, ?_⟩
  · intro x hx; interval_cases x <;> dsimp only [μ] <;> norm_num
  · intro d hd1 hd3; interval_cases d <;> right <;> simp [Finset.sum_range_succ, μ] <;> norm_num
  · simp [Finset.sum_range_succ, μ]; norm_num

/-- Theorem T3-A (Endpoint Rigidity): For ANY `μ : ℕ → ℝ` on `{0, ..., N - 1}` with `μ(x) ∈ [0, 1]`
and binary linear autocorrelation `r_μ(d) ∈ {0, 1}` for all `1 ≤ d < N`, if `supp(μ)` has
at least `2` elements, then the minimum and maximum elements `a < b` of `supp(μ)` both satisfy
`μ a = 1` and `μ b = 1`. -/
theorem binary_autocorr_endpoint_rigidity {N : ℕ} {μ : ℕ → ℝ}
    (hμ_box : ∀ x, x < N → 0 ≤ μ x ∧ μ x ≤ 1)
    (hμ_bin : ∀ d, 1 ≤ d → d < N →
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 0 ∨
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 1)
    (hsupp2 : 2 ≤ ((Finset.range N).filter (fun x => 0 < μ x)).card) :
    let supp := (Finset.range N).filter (fun x => 0 < μ x)
    have hne : supp.Nonempty := Finset.card_pos.mp (by dsimp only [supp]; omega)
    let a := supp.min' hne
    let b := supp.max' hne
    a < b ∧ μ a = 1 ∧ μ b = 1 := by
  classical
  intro supp hne a b
  have ha_mem : a ∈ supp := Finset.min'_mem supp hne
  have hb_mem : b ∈ supp := Finset.max'_mem supp hne
  have ha_ltN : a < N := Finset.mem_range.mp (Finset.mem_filter.mp ha_mem).1
  have hb_ltN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp hb_mem).1
  have ha_pos : 0 < μ a := (Finset.mem_filter.mp ha_mem).2
  have hb_pos : 0 < μ b := (Finset.mem_filter.mp hb_mem).2
  have hab_le : a ≤ b := Finset.min'_le supp b hb_mem
  have hab_ne : a ≠ b := by
    intro heq
    have hsub : supp ⊆ {a} := by
      intro x hx
      have h1 : a ≤ x := Finset.min'_le supp x hx
      have h2 : x ≤ b := Finset.le_max' supp x hx
      exact Finset.mem_singleton.mpr (by omega)
    have hle1 : supp.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
    have hge2 : 2 ≤ supp.card := hsupp2
    omega
  have hab : a < b := lt_of_le_of_ne hab_le hab_ne
  -- Evaluate `r_μ(b - a) = μ a * μ b`
  set d := b - a
  have hd1 : 1 ≤ d := by omega
  have hdN : d < N := by omega
  have hsum_single : ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = μ a * μ b := by
    rw [Finset.sum_eq_single a]
    · rw [show a + d = b by omega]
    · intro x hx hxa
      rw [Finset.mem_range] at hx
      rcases lt_or_gt_of_ne hxa with hlt | hgt
      · have hnot : x ∉ supp := fun h => by have := Finset.min'_le supp x h; omega
        have hx0 : μ x = 0 := by
          have hnn := (hμ_box x (by omega)).1
          have hle0 : ¬ 0 < μ x := fun hp => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
          linarith
        rw [hx0, zero_mul]
      · have hnot : x + d ∉ supp := fun h => by have := Finset.le_max' supp (x + d) h; omega
        have hxd0 : μ (x + d) = 0 := by
          have hnn := (hμ_box (x + d) (by omega)).1
          have hle0 : ¬ 0 < μ (x + d) := fun hp =>
            hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)
          linarith
        rw [hxd0, mul_zero]
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  have hprod_pos : 0 < μ a * μ b := mul_pos ha_pos hb_pos
  have hprod_eq1 : μ a * μ b = 1 := by
    rcases hμ_bin d hd1 hdN with h0 | h1
    · rw [hsum_single] at h0; linarith
    · rwa [hsum_single] at h1
  have ha_le1 : μ a ≤ 1 := (hμ_box a ha_ltN).2
  have hb_le1 : μ b ≤ 1 := (hμ_box b hb_ltN).2
  exact ⟨hab, by nlinarith, by nlinarith⟩

/-- Theorem T3-A (Outermost Fractional Shell Rigidity & Lag-`t` Zeroing):
For any `μ : ℕ → ℝ` on `{0, ..., N - 1}` with `μ(x) ∈ [0, 1]`, binary autocorrelation
`r_μ(d) ∈ {0, 1}` for all `1 ≤ d < N`, and `|supp(μ)| ≥ 2` (endpoints `a < b`),
if there exists any strictly fractional entry `0 < μ x < 1`, then the minimal distance
`t = min { min(x - a, b - x) : x < N, 0 < μ x < 1 }` satisfies `1 ≤ t ≤ (b - a) / 2`,
`0 < μ (a + t) < 1`, `0 < μ (b - t) < 1`, `μ (a + t) + μ (b - t) = 1`, AND
every other lag-`t` pair (`x ≠ a`, `x ≠ b - t`) vanishes: `μ x * μ (x + t) = 0`. -/
theorem binary_autocorr_outermost_shell_rigidity {N : ℕ} {μ : ℕ → ℝ}
    (hμ_box : ∀ x, x < N → 0 ≤ μ x ∧ μ x ≤ 1)
    (hμ_bin : ∀ d, 1 ≤ d → d < N →
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 0 ∨
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 1)
    (hsupp2 : 2 ≤ ((Finset.range N).filter (fun x => 0 < μ x)).card)
    (hfrac : ∃ x, x < N ∧ 0 < μ x ∧ μ x < 1) :
    let supp := (Finset.range N).filter (fun x => 0 < μ x)
    have hne : supp.Nonempty := Finset.card_pos.mp (by dsimp only [supp]; omega)
    let a := supp.min' hne
    let b := supp.max' hne
    ∃ t : ℕ, 1 ≤ t ∧ 2 * t ≤ b - a ∧
      0 < μ (a + t) ∧ μ (a + t) < 1 ∧
      0 < μ (b - t) ∧ μ (b - t) < 1 ∧
      μ (a + t) + μ (b - t) = 1 ∧
      ∀ x, x < N - t → x ≠ a → x ≠ b - t → μ x * μ (x + t) = 0 := by
  classical
  intro supp hne a b
  have hend := binary_autocorr_endpoint_rigidity hμ_box hμ_bin hsupp2
  have hab : a < b := hend.1
  have hμa : μ a = 1 := hend.2.1
  have hμb : μ b = 1 := hend.2.2
  have ha_ltN : a < N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.min'_mem supp hne)).1
  have hb_ltN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem supp hne)).1
  have hzero_out : ∀ y, y < N → (y < a ∨ b < y) → μ y = 0 := by
    intro y hyN hltgt
    have hnot : y ∉ supp := by
      intro hmem
      have h1 : a ≤ y := Finset.min'_le supp y hmem
      have h2 : y ≤ b := Finset.le_max' supp y hmem
      omega
    have hnn := (hμ_box y hyN).1
    have hnp : ¬ 0 < μ y := fun hp => hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyN, hp⟩)
    linarith
  set F : Finset ℕ := (Finset.range N).filter (fun x => 0 < μ x ∧ μ x < 1)
  have hFne : F.Nonempty := by
    rcases hfrac with ⟨x, hxN, hx0, hx1⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxN, hx0, hx1⟩⟩
  have hF_in_open : ∀ x ∈ F, a < x ∧ x < b := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    have hxsupp : x ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1, hx.2.1⟩
    have h1 : a ≤ x := Finset.min'_le supp x hxsupp
    have h2 : x ≤ b := Finset.le_max' supp x hxsupp
    have hnea : x ≠ a := fun h => by rw [h, hμa] at hx; linarith
    have hneb : x ≠ b := fun h => by rw [h, hμb] at hx; linarith
    omega
  set dists : Finset ℕ := F.image (fun x => min (x - a) (b - x))
  have hdists_ne : dists.Nonempty := hFne.image _
  set t : ℕ := dists.min' hdists_ne
  have ht_mem : t ∈ dists := Finset.min'_mem dists hdists_ne
  rcases Finset.mem_image.mp ht_mem with ⟨x₀, hx₀F, hx₀t⟩
  have hx₀_open := hF_in_open x₀ hx₀F
  have ht1 : 1 ≤ t := by omega
  have h2t : 2 * t ≤ b - a := by omega
  have hx₀_frac : 0 < μ x₀ ∧ μ x₀ < 1 := (Finset.mem_filter.mp hx₀F).2
  have hshell_one_frac : (0 < μ (a + t) ∧ μ (a + t) < 1) ∨ (0 < μ (b - t) ∧ μ (b - t) < 1) := by
    by_cases hle : x₀ - a ≤ b - x₀
    · left
      have : x₀ = a + t := by omega
      rwa [← this]
    · right
      have : x₀ = b - t := by omega
      rwa [← this]
  -- Every `y` strictly closer to an endpoint than `t` is `{0, 1}`-valued
  have hnear_bin : ∀ y, a < y → y < b → min (y - a) (b - y) < t → μ y = 0 ∨ μ y = 1 := by
    intro y hy1 hy2 hlt
    have hyN : y < N := by omega
    have hnotF : y ∉ F := by
      intro hyF
      have hmem : min (y - a) (b - y) ∈ dists := Finset.mem_image.mpr ⟨y, hyF, rfl⟩
      have hge := Finset.min'_le dists _ hmem
      omega
    rcases hμ_box y hyN with ⟨h0, h1⟩
    by_contra hneither
    push Not at hneither
    exact hnotF (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hyN,
      lt_of_le_of_ne h0 (Ne.symm hneither.1), lt_of_le_of_ne h1 hneither.2⟩)
  -- Analyze `d* = b - a - t`
  set dStar : ℕ := b - a - t
  have hdStar1 : 1 ≤ dStar := by omega
  have hdStarN : dStar < N := by omega
  -- Split `∑ u ∈ range (N - dStar), μ u * μ (u + dStar)`
  have hsum_dStar :
      ∑ u ∈ Finset.range (N - dStar), μ u * μ (u + dStar) =
      μ (b - t) + μ (a + t) + ∑ u ∈ Finset.Ioo a (a + t), μ u * μ (u + dStar) := by
    have hsub_Icc : Finset.Icc a (a + t) ⊆ Finset.range (N - dStar) := by
      intro u hu; rw [Finset.mem_Icc] at hu; rw [Finset.mem_range]; omega
    rw [← Finset.sum_subset hsub_Icc]
    · have hsplit1 : Finset.Icc a (a + t) = insert a (insert (a + t) (Finset.Ioo a (a + t))) := by
        ext u; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]; omega
      rw [hsplit1, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ioo]; omega),
        Finset.sum_insert (by simp only [Finset.mem_Ioo]; omega)]
      rw [show a + dStar = b - t by omega, show a + t + dStar = b by omega, hμa, hμb]
      ring
    · intro u hu huIcc
      rw [Finset.mem_range] at hu
      rw [Finset.mem_Icc] at huIcc
      by_cases hlt : u < a
      · rw [hzero_out u (by omega) (Or.inl hlt), zero_mul]
      · have hgt : b < u + dStar := by omega
        rw [hzero_out (u + dStar) (by omega) (Or.inr hgt), mul_zero]
  -- Every interior term `u ∈ Ioo a (a + t)` is in `{0, 1}`, so the interior sum is a natural number
  have hint_nat : ∃ k : ℕ, ∑ u ∈ Finset.Ioo a (a + t), μ u * μ (u + dStar) = (k : ℝ) := by
    have hterm_nat : ∀ u ∈ Finset.Ioo a (a + t), μ u * μ (u + dStar) = 0 ∨ μ u * μ (u + dStar) = 1 := by
      intro u hu
      rw [Finset.mem_Ioo] at hu
      have h1 := hnear_bin u hu.1 (by omega) (by omega)
      have h2 := hnear_bin (u + dStar) (by omega) (by omega) (by omega)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
    refine ⟨((Finset.Ioo a (a + t)).filter (fun u => μ u * μ (u + dStar) = 1)).card, ?_⟩
    have heq : ∑ u ∈ Finset.Ioo a (a + t), μ u * μ (u + dStar) =
        ∑ u ∈ Finset.Ioo a (a + t), if μ u * μ (u + dStar) = 1 then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rcases hterm_nat u hu with h0 | h1
      · rw [h0, if_neg (by norm_num)]
      · rw [h1, if_pos rfl]
    rw [heq, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rcases hint_nat with ⟨k, hk⟩
  have hμat_box := hμ_box (a + t) (by omega)
  have hμbt_box := hμ_box (b - t) (by omega)
  have hsum_pos : 0 < ∑ u ∈ Finset.range (N - dStar), μ u * μ (u + dStar) := by
    rw [hsum_dStar, hk]
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rcases hshell_one_frac with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hsum_eq1 : μ (b - t) + μ (a + t) + (k : ℝ) = 1 := by
    rcases hμ_bin dStar hdStar1 hdStarN with h0 | h1
    · linarith
    · rwa [hsum_dStar, hk] at h1
  have hk0 : k = 0 := by
    by_contra hkne
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hkne)
    rcases hshell_one_frac with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hsum_shell : μ (a + t) + μ (b - t) = 1 := by
    rw [hk0, Nat.cast_zero, add_zero] at hsum_eq1; linarith
  have hat_pos : 0 < μ (a + t) := by
    rcases hshell_one_frac with ⟨h1, _⟩ | ⟨_, h2⟩ <;> linarith
  have hat_lt1 : μ (a + t) < 1 := by
    rcases hshell_one_frac with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
  have hbt_pos : 0 < μ (b - t) := by linarith
  have hbt_lt1 : μ (b - t) < 1 := by linarith
  -- Lag-`t` zeroing for all `x ≠ a, b - t`
  have hzero_t : ∀ x, x < N - t → x ≠ a → x ≠ b - t → μ x * μ (x + t) = 0 := by
    intro x hxN hxa hxbt
    have htN : t < N := by omega
    have hrt_le1 : ∑ u ∈ Finset.range (N - t), μ u * μ (u + t) ≤ 1 := by
      rcases hμ_bin t ht1 htN with h0 | h1 <;> linarith
    have ha_ne_bt : a ≠ b - t := by omega
    have hpair_sub : ({a, b - t} : Finset ℕ) ⊆ Finset.range (N - t) := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rw [Finset.mem_range]; rcases hu with rfl | rfl <;> omega
    have hpair_sum : ∑ u ∈ ({a, b - t} : Finset ℕ), μ u * μ (u + t) = 1 := by
      rw [Finset.sum_pair ha_ne_bt, hμa, show b - t + t = b by omega, hμb]
      linarith
    have h3_sub : ({x, a, b - t} : Finset ℕ) ⊆ Finset.range (N - t) := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rw [Finset.mem_range]; rcases hu with rfl | rfl | rfl <;> omega
    have h3_sum : ∑ u ∈ ({x, a, b - t} : Finset ℕ), μ u * μ (u + t) ≤
        ∑ u ∈ Finset.range (N - t), μ u * μ (u + t) :=
      Finset.sum_le_sum_of_subset_of_nonneg h3_sub fun u hu _ =>
        mul_nonneg (hμ_box u (by have := Finset.mem_range.mp hu; omega)).1
          (hμ_box (u + t) (by have := Finset.mem_range.mp hu; omega)).1
    have hx_notin : x ∉ ({a, b - t} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hxa, hxbt⟩
    rw [Finset.sum_insert hx_notin, hpair_sum] at h3_sum
    have hx_nn : 0 ≤ μ x * μ (x + t) :=
      mul_nonneg (hμ_box x (by omega)).1 (hμ_box (x + t) (by omega)).1
    linarith
  exact ⟨t, ht1, h2t, hat_pos, hat_lt1, hbt_pos, hbt_lt1, hsum_shell, hzero_t⟩

/-- Theorem T3-A (Sidon Support Integrality Corollary):
If `μ : ℕ → ℝ` on `{0, ..., N - 1}` has `μ(x) ∈ [0, 1]`, binary autocorrelation
`r_μ(d) ∈ {0, 1}` for all `1 ≤ d < N`, `|supp(μ)| ≥ 2`, AND `supp(μ)` is a Sidon set,
then `μ` is strictly `{0, 1}`-valued on `range N`. -/
theorem binary_autocorr_sidon_support_integral {N : ℕ} {μ : ℕ → ℝ}
    (hμ_box : ∀ x, x < N → 0 ≤ μ x ∧ μ x ≤ 1)
    (hμ_bin : ∀ d, 1 ≤ d → d < N →
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 0 ∨
      ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) = 1)
    (hsupp2 : 2 ≤ ((Finset.range N).filter (fun x => 0 < μ x)).card)
    (hSidon : IsSidon (((Finset.range N).filter (fun x => 0 < μ x)) : Set ℕ)) :
    ∀ x, x < N → μ x = 0 ∨ μ x = 1 := by
  intro x hxN
  by_contra hneither
  push Not at hneither
  rcases hμ_box x hxN with ⟨h0, h1⟩
  have hfrac : ∃ y, y < N ∧ 0 < μ y ∧ μ y < 1 :=
    ⟨x, hxN, lt_of_le_of_ne h0 (Ne.symm hneither.1), lt_of_le_of_ne h1 hneither.2⟩
  let supp := (Finset.range N).filter (fun y => 0 < μ y)
  have hne : supp.Nonempty := Finset.card_pos.mp (by dsimp only [supp]; omega)
  let a := supp.min' hne
  let b := supp.max' hne
  have ha_mem : a ∈ (supp : Set ℕ) := Finset.mem_coe.mpr (Finset.min'_mem supp hne)
  have hb_mem : b ∈ (supp : Set ℕ) := Finset.mem_coe.mpr (Finset.max'_mem supp hne)
  have hb_ltN : b < N := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem supp hne)).1
  have hab : a < b := (binary_autocorr_endpoint_rigidity hμ_box hμ_bin hsupp2).1
  have hshell := binary_autocorr_outermost_shell_rigidity hμ_box hμ_bin hsupp2 hfrac
  dsimp only at hshell
  rcases hshell with ⟨t, ht1, h2t, hat_pos, _, hbt_pos, _, _, _⟩
  change 2 * t ≤ b - a at h2t
  change 0 < μ (a + t) at hat_pos
  change 0 < μ (b - t) at hbt_pos
  have hat_mem : a + t ∈ (supp : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hat_pos⟩)
  have hbt_mem : b - t ∈ (supp : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbt_pos⟩)
  have hcoll := hSidon a ha_mem b hb_mem (a + t) hat_mem (b - t) hbt_mem (by omega)
  omega

end Erdos030
