import Problems.Erdos030.PeriodicDFT
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Smooth-Bump Periodic Bose + Poisson Asymptotic Barrier Theorem

Elementary, Weil-sum-free formalization of the asymptotic fractional & Degree-1 Lasserre
barrier witness `μ = f + g_L + g_R` on `ℤ / Mℤ` (`M = p^2 - 1`) for every prime `p ≥ 10000`.
Uses only `PeriodicDFT`, `Real.pi_gt_three`, `Real.pi_lt_four`, `Real.add_one_le_exp`,
and `Real.abs_sin_le_abs`.
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-! ### Part 1: Periodic Poisson Kernel & Exact Algebraic Dip Identity -/

/-- Continuous Poisson factor `P_ρ(c) = (1 - ρ^2) / (1 - 2 ρ c + ρ^2)`. -/
noncomputable def poissonFactor (ρ c : ℝ) : ℝ :=
  (1 - ρ ^ 2) / (1 - 2 * ρ * c + ρ ^ 2)

/-- Periodic Poisson kernel on `ℤ / Mℤ` (`M = 2H` even) with exact DFT `ρ^(min(ξ, M - ξ))`. -/
noncomputable def poissonKernel (M : ℕ) (ρ : ℝ) (d : ℕ) : ℝ :=
  ((1 - (-1 : ℝ) ^ d * ρ ^ (M / 2)) / (M : ℝ)) *
    poissonFactor ρ (Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ)))

lemma poissonFactor_den_pos {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc1 : c ≤ 1) :
    0 < 1 - 2 * ρ * c + ρ ^ 2 := by
  have h1 : (1 - ρ) ^ 2 ≤ 1 - 2 * ρ * c + ρ ^ 2 := by nlinarith
  have h2 : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (by linarith)
  linarith

lemma poissonFactor_pos {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc1 : c ≤ 1) :
    0 < poissonFactor ρ c := by
  unfold poissonFactor
  exact div_pos (by nlinarith) (poissonFactor_den_pos hρ0 hρ1 hc1)

lemma poissonFactor_le {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc1 : c ≤ 1) :
    poissonFactor ρ c ≤ (1 + ρ) / (1 - ρ) := by
  unfold poissonFactor
  have hden_ge : (1 - ρ) ^ 2 ≤ 1 - 2 * ρ * c + ρ ^ 2 := by nlinarith
  have h1 : (1 - ρ ^ 2) / (1 - 2 * ρ * c + ρ ^ 2) ≤ (1 - ρ ^ 2) / (1 - ρ) ^ 2 :=
    div_le_div_of_nonneg_left (by nlinarith) (sq_pos_of_pos (by linarith)) hden_ge
  have h2 : (1 - ρ ^ 2) / (1 - ρ) ^ 2 = (1 + ρ) / (1 - ρ) := by
    have hne : 1 - ρ ≠ 0 := by linarith
    field_simp [hne]; ring
  linarith

/-- Exact algebraic identity for `2 P_ρ(c) - P_{ρ^2}(c)`. -/
lemma poissonFactor_dip_eq {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc1 : c ≤ 1) :
    2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c =
      (1 - ρ ^ 2) * (1 - ρ) ^ 2 * (1 + ρ ^ 2 + 2 * ρ * (1 + c)) /
        (((1 - ρ) ^ 2 + 2 * ρ * (1 - c)) * ((1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c))) := by
  unfold poissonFactor
  have hρ2_pos : 0 < ρ ^ 2 := sq_pos_of_pos hρ0
  have hρ2_lt : ρ ^ 2 < 1 := by nlinarith
  have hd1 : 1 - 2 * ρ * c + ρ ^ 2 ≠ 0 := (poissonFactor_den_pos hρ0 hρ1 hc1).ne'
  have hd2 : 1 - 2 * ρ ^ 2 * c + (ρ ^ 2) ^ 2 ≠ 0 :=
    (poissonFactor_den_pos hρ2_pos hρ2_lt hc1).ne'
  have hd1' : (1 - ρ) ^ 2 + 2 * ρ * (1 - c) = 1 - 2 * ρ * c + ρ ^ 2 := by ring
  have hd2' : (1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c) = 1 - 2 * ρ ^ 2 * c + (ρ ^ 2) ^ 2 := by ring
  rw [hd1', hd2', mul_div_assoc', div_sub_div _ _ hd1 hd2, div_eq_div_iff (mul_ne_zero hd1 hd2)
    (mul_ne_zero hd1 hd2)]
  ring

lemma poissonFactor_dip_pos {ρ c : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc0 : -1 ≤ c) (hc1 : c ≤ 1) :
    0 < 2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c := by
  rw [poissonFactor_dip_eq hρ0 hρ1 hc1]
  have hnum : 0 < (1 - ρ ^ 2) * (1 - ρ) ^ 2 * (1 + ρ ^ 2 + 2 * ρ * (1 + c)) := by
    have h1 : 0 < 1 - ρ ^ 2 := by nlinarith
    have h2 : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (by linarith)
    have h3 : 0 < 1 + ρ ^ 2 + 2 * ρ * (1 + c) := by nlinarith
    positivity
  have hden : 0 < ((1 - ρ) ^ 2 + 2 * ρ * (1 - c)) * ((1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c)) := by
    have h1 : 0 < (1 - ρ) ^ 2 + 2 * ρ * (1 - c) := by nlinarith
    have h2 : 0 < (1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c) := by nlinarith
    positivity
  exact div_pos hnum hden

/-- Exact inverse DFT of `ρ^(min(ξ, 2H - ξ))` equals `poissonKernel (2*H) ρ d`. -/
lemma poissonKernel_invDft {H : ℕ} (hH : 0 < H) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (d : ℕ) :
    invDft (2 * H) (fun ξ => ((ρ ^ (min ξ (2 * H - ξ)) : ℝ) : ℂ)) d =
      (poissonKernel (2 * H) ρ d : ℂ) := by
  set M := 2 * H
  have hM : 0 < M := by omega
  let ω := rootOfUnity M
  let z : ℂ := (ρ : ℂ) * starRingEnd ℂ (ω ^ d)
  have hnorm_z : ‖z‖ = ρ := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le, Complex.norm_conj,
      norm_rootOfUnity_pow, mul_one]
  have hz_ne1 : z ≠ 1 := by
    intro h1
    have := congrArg norm h1
    rw [hnorm_z, norm_one] at this
    linarith
  have hzbar_ne1 : starRingEnd ℂ z ≠ 1 := by
    intro h1
    have := congrArg norm h1
    rw [Complex.norm_conj, hnorm_z, norm_one] at this
    linarith
  have hωH : ω ^ H = -1 := by
    dsimp only [ω, rootOfUnity, M]
    rw [← Complex.exp_natCast_mul]
    have harg : (H : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((2 * H : ℕ) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      have hHne : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
      push_cast
      field_simp [hHne]
    rw [harg, Complex.exp_pi_mul_I]
  have hzH : z ^ H = ((-1 : ℝ) ^ d * ρ ^ H : ℝ) := by
    dsimp only [z]
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm d H, pow_mul, hωH]
    have hstar : starRingEnd ℂ ((-1 : ℂ) ^ d) = (-1 : ℂ) ^ d := by
      rw [map_pow, map_neg, map_one]
    rw [hstar]
    push_cast; ring
  have hzbarH : (starRingEnd ℂ z) ^ H = z ^ H := by
    rw [← map_pow, hzH, Complex.conj_ofReal]
  have hsplit :
      ∑ ξ ∈ Finset.range M, ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (ξ * d)) =
      1 + z ^ H + (∑ ξ ∈ Finset.Ico 1 H, z ^ ξ) +
        (∑ ξ ∈ Finset.Ico (H + 1) M, (starRingEnd ℂ z) ^ (M - ξ)) := by
    have h1 : Finset.range M = Finset.range H ∪ Finset.Ico H M := by
      ext ξ; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd1 : Disjoint (Finset.range H) (Finset.Ico H M) := by
      rw [Finset.disjoint_left]; intro ξ h1' h2'
      rw [Finset.mem_range] at h1'; rw [Finset.mem_Ico] at h2'; omega
    rw [h1, Finset.sum_union hd1, ← Finset.sum_range_add_sum_Ico _ hH]
    have hIcoH : Finset.Ico H M = insert H (Finset.Ico (H + 1) M) := by
      ext ξ; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hIcoH, Finset.sum_insert (by simp)]
    have h0 : ∑ ξ ∈ Finset.range 1,
        ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (ξ * d)) = 1 := by
      simp
    have hHterm : ((ρ ^ (min H (M - H)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (H * d)) = z ^ H := by
      have hmin : min H (M - H) = H := by omega
      rw [hmin]
      dsimp only [z]
      rw [mul_pow, ← map_pow, ← pow_mul, mul_comm d H]
      push_cast; rfl
    have hmid1 : ∑ ξ ∈ Finset.Ico 1 H,
        ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (ξ * d)) =
        ∑ ξ ∈ Finset.Ico 1 H, z ^ ξ := by
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [Finset.mem_Ico] at hξ
      have hmin : min ξ (M - ξ) = ξ := by omega
      rw [hmin]
      dsimp only [z]
      rw [mul_pow, ← map_pow, ← pow_mul, mul_comm d ξ]
      push_cast; rfl
    have hmid2 : ∑ ξ ∈ Finset.Ico (H + 1) M,
        ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (ξ * d)) =
        ∑ ξ ∈ Finset.Ico (H + 1) M, (starRingEnd ℂ z) ^ (M - ξ) := by
      refine Finset.sum_congr rfl fun ξ hξ => ?_
      rw [Finset.mem_Ico] at hξ
      have hmin : min ξ (M - ξ) = M - ξ := by omega
      rw [hmin]
      dsimp only [z]
      rw [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, mul_pow, ← pow_mul,
        mul_comm d (M - ξ)]
      have hstar_pow : starRingEnd ℂ (ω ^ (ξ * d)) = ω ^ ((M - ξ) * d) :=
        (rootOfUnity_pow_sub_eq_star hM hξ.2.le d).symm
      rw [hstar_pow]
      push_cast; rfl
    rw [h0, hHterm, hmid1, hmid2]
    ring
  have hgeom : ∀ w : ℂ, w ≠ 1 → ∑ k ∈ Finset.Ico 1 H, w ^ k = (w - w ^ H) / (1 - w) := by
    intro w hw
    have hshift : ∑ k ∈ Finset.Ico 1 H, w ^ k = w * ∑ j ∈ Finset.range (H - 1), w ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij (fun k => k - 1) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
        dsimp only at hab; omega
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_range] at hj
        refine ⟨j + 1, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by simp⟩
      · intro k hk
        rw [Finset.mem_Ico] at hk
        rw [← pow_succ', show k - 1 + 1 = k by omega]
    rw [hshift, geom_sum_eq hw]
    have hne1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    have hne2 : 1 - w ≠ 0 := sub_ne_zero.mpr hw.symm
    have hpow : w * w ^ (H - 1) = w ^ H := by
      rw [← pow_succ', Nat.sub_add_cancel hH]
    field_simp [hne1, hne2]
    linear_combination (1 - w) * hpow
  have hsum2 : ∑ ξ ∈ Finset.Ico (H + 1) M, (starRingEnd ℂ z) ^ (M - ξ) =
      ∑ k ∈ Finset.Ico 1 H, (starRingEnd ℂ z) ^ k := by
    refine Finset.sum_nbij (fun ξ => M - ξ) ?_ ?_ ?_ ?_
    · intro ξ hξ; simp only [Finset.mem_Ico] at hξ ⊢; omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      dsimp only at hab; omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Ico] at hk
      refine ⟨M - k, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp; omega⟩
    · intro ξ _; rfl
  have hsum_eq :
      ∑ ξ ∈ Finset.range M, ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * starRingEnd ℂ (ω ^ (ξ * d)) =
      ((1 - (-1 : ℝ) ^ d * ρ ^ H) * (1 - ρ ^ 2) /
        (1 - 2 * ρ * Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ)) + ρ ^ 2) : ℝ) := by
    rw [hsplit, hsum2, hgeom z hz_ne1, hgeom (starRingEnd ℂ z) hzbar_ne1, hzbarH]
    have h1mz : 1 - z ≠ 0 := sub_ne_zero.mpr hz_ne1.symm
    have h1mzb : 1 - starRingEnd ℂ z ≠ 0 := sub_ne_zero.mpr hzbar_ne1.symm
    have hcomb :
        1 + z ^ H + (z - z ^ H) / (1 - z) + (starRingEnd ℂ z - z ^ H) / (1 - starRingEnd ℂ z) =
        (1 - z ^ H) * (1 - z * starRingEnd ℂ z) / ((1 - z) * (1 - starRingEnd ℂ z)) := by
      field_simp [h1mz, h1mzb]
      ring
    rw [hcomb]
    have hzzb : z * starRingEnd ℂ z = ((ρ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm_z]
    have hz_add_zb : z + starRingEnd ℂ z =
        ((2 * ρ * Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.add_conj]
      set φ : ℝ := 2 * Real.pi * (d : ℝ) / (M : ℝ)
      have hre_z : z.re = ρ * Real.cos φ := by
        dsimp only [z, ω, rootOfUnity]
        rw [← Complex.exp_natCast_mul]
        have harg : (d : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) = (φ : ℂ) * Complex.I := by
          dsimp only [φ]; push_cast; ring
        rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
          Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
        ring
      rw [hre_z]
      push_cast; ring
    have hden_eq : (1 - z) * (1 - starRingEnd ℂ z) =
        ((1 - 2 * ρ * Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ)) + ρ ^ 2 : ℝ) : ℂ) := by
      have h1 : (1 - z) * (1 - starRingEnd ℂ z) =
          1 - (z + starRingEnd ℂ z) + z * starRingEnd ℂ z := by ring
      rw [h1, hz_add_zb, hzzb]
      push_cast; ring
    rw [hzH, hzzb, hden_eq]
    push_cast; rfl
  unfold invDft poissonKernel poissonFactor
  have hMdiv : M / 2 = H := by omega
  rw [hsum_eq, hMdiv]
  push_cast
  ring

/-- Exact DFT of `poissonKernel (2*H) ρ`. -/
lemma dft_poissonKernel {H : ℕ} (hH : 0 < H) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ξ : ℕ} (hξ : ξ < 2 * H) :
    dft (2 * H) (poissonKernel (2 * H) ρ) ξ = ((ρ ^ (min ξ (2 * H - ξ)) : ℝ) : ℂ) := by
  let F : ℕ → ℂ := fun η => ((ρ ^ (min η (2 * H - η)) : ℝ) : ℂ)
  have hF0 : (F 0).im = 0 := by simp [F]
  have hFsymm : ∀ η : ℕ, 1 ≤ η → η < 2 * H → F (2 * H - η) = starRingEnd ℂ (F η) := by
    intro η hη1 hηM
    dsimp only [F]
    rw [Complex.conj_ofReal]
    congr 2
    omega
  have hre : ∀ x : ℕ, (invDft (2 * H) F x).re = poissonKernel (2 * H) ρ x := fun x => by
    rw [poissonKernel_invDft hH hρ0 hρ1 x, Complex.ofReal_re]
  have hdft := dft_invDft_re_of_hermitian (by omega : 0 < 2 * H) hF0 hFsymm hξ
  rwa [show (fun x => (invDft (2 * H) F x).re) = poissonKernel (2 * H) ρ from funext hre] at hdft

/-- Conjugate form of the Poisson kernel DFT sum (with `ω^(ξ*d)` instead of `star (ω^(ξ*d))`). -/
lemma sum_poisson_freq_mul_pow {H : ℕ} (hH : 0 < H) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (d : ℕ) :
    ∑ ξ ∈ Finset.range (2 * H),
        ((ρ ^ (min ξ (2 * H - ξ)) : ℝ) : ℂ) * (rootOfUnity (2 * H)) ^ (ξ * d) =
      (((2 * H : ℕ) : ℝ) * poissonKernel (2 * H) ρ d : ℝ) := by
  have hinv := poissonKernel_invDft hH hρ0 hρ1 d
  unfold invDft at hinv
  have hMne : ((2 * H : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmul : ∑ ξ ∈ Finset.range (2 * H),
      ((ρ ^ (min ξ (2 * H - ξ)) : ℝ) : ℂ) * starRingEnd ℂ ((rootOfUnity (2 * H)) ^ (ξ * d)) =
      (((2 * H : ℕ) : ℝ) * poissonKernel (2 * H) ρ d : ℝ) := by
    have h1 := congrArg (fun z : ℂ => ((2 * H : ℕ) : ℂ) * z) hinv
    dsimp only at h1
    rw [← mul_assoc, mul_one_div_cancel hMne, one_mul] at h1
    push_cast at h1 ⊢
    exact h1
  have hconj := congrArg (starRingEnd ℂ) hmul
  rw [map_sum, Complex.conj_ofReal] at hconj
  convert hconj using 2 with ξ
  rw [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]

/-! ### Part 2: Smooth Triangle (Fejér) Boundary Bumps `g_L`, `g_R`, `g` -/

/-- Box indicator `1_{[0, L0)}`. -/
def boxInd (L0 : ℕ) (x : ℕ) : ℝ :=
  if x < L0 then 1 else 0

/-- Discrete triangle bump `T = 1_{[0, L0)} ⋆_M 1_{[0, L0)}`. -/
noncomputable def triBump (M L0 : ℕ) (x : ℕ) : ℝ :=
  cyclicConv M (boxInd L0) (boxInd L0) x

lemma triBump_nonneg (M L0 x : ℕ) : 0 ≤ triBump M L0 x := by
  unfold triBump cyclicConv boxInd
  refine Finset.sum_nonneg fun y _ => ?_
  split_ifs <;> positivity

lemma triBump_le {M L0 : ℕ} (hLM : L0 ≤ M) (x : ℕ) : triBump M L0 x ≤ (L0 : ℝ) := by
  unfold triBump cyclicConv
  calc ∑ y ∈ Finset.range M, boxInd L0 y * boxInd L0 ((x + M - y) % M)
      ≤ ∑ y ∈ Finset.range M, boxInd L0 y := by
        refine Finset.sum_le_sum fun y _ => ?_
        have h1 : 0 ≤ boxInd L0 y := by unfold boxInd; split_ifs <;> positivity
        have h2 : boxInd L0 ((x + M - y) % M) ≤ 1 := by unfold boxInd; split_ifs <;> norm_num
        nlinarith
    _ = (L0 : ℝ) := by
        rw [← Finset.sum_subset (Finset.range_mono hLM)]
        · have : ∀ y ∈ Finset.range L0, boxInd L0 y = 1 := fun y hy => by
            unfold boxInd; rw [Finset.mem_range] at hy; simp [hy]
          rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        · intro y _ hy; unfold boxInd; rw [Finset.mem_range] at hy; simp [hy]

lemma triBump_eq_zero_of_ge {M L0 x : ℕ} (hL0 : 1 ≤ L0) (h2L : 2 * L0 ≤ M)
    (hx1 : 2 * L0 - 1 ≤ x) (hxM : x < M) :
    triBump M L0 x = 0 := by
  unfold triBump cyclicConv
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finset.mem_range] at hy
  by_cases hyL : y < L0
  · have hmod : (x + M - y) % M = x - y := by
      have hadd : x + M - y = (x - y) + M := by omega
      rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hge : ¬ (x - y < L0) := by omega
    unfold boxInd
    simp [hmod, hge]
  · unfold boxInd
    simp [hyL]

lemma sum_boxInd {M L0 : ℕ} (hLM : L0 ≤ M) :
    ∑ y ∈ Finset.range M, boxInd L0 y = (L0 : ℝ) := by
  rw [← Finset.sum_subset (Finset.range_mono hLM)]
  · have : ∀ y ∈ Finset.range L0, boxInd L0 y = 1 := fun y hy => by
      unfold boxInd; rw [Finset.mem_range] at hy; simp [hy]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro y _ hy; unfold boxInd; rw [Finset.mem_range] at hy; simp [hy]

lemma sum_triBump {M L0 : ℕ} (hM : 0 < M) (hLM : L0 ≤ M) :
    ∑ x ∈ Finset.range M, triBump M L0 x = (L0 : ℝ) ^ 2 := by
  have h0 := dft_zero M (triBump M L0)
  have hconv : dft M (triBump M L0) 0 = dft M (boxInd L0) 0 * dft M (boxInd L0) 0 :=
    dft_cyclicConv hM (boxInd L0) (boxInd L0) 0
  rw [hconv, dft_zero, sum_boxInd hLM] at h0
  have hre := congrArg Complex.re h0
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  nlinarith

/-- Exact `L^1` Fourier norm of `triBump` via 1-line Parseval. -/
lemma sum_norm_dft_triBump {M L0 : ℕ} (hM : 0 < M) (hLM : L0 ≤ M) :
    ∑ ξ ∈ Finset.range M, ‖dft M (triBump M L0) ξ‖ = (M : ℝ) * (L0 : ℝ) := by
  have hsq : ∑ ξ ∈ Finset.range M, ‖dft M (triBump M L0) ξ‖ =
      ∑ ξ ∈ Finset.range M, ‖dft M (boxInd L0) ξ‖ ^ 2 := by
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hconv : dft M (triBump M L0) ξ = dft M (boxInd L0) ξ * dft M (boxInd L0) ξ :=
      dft_cyclicConv hM (boxInd L0) (boxInd L0) ξ
    rw [hconv, norm_mul, sq]
  rw [hsq, dft_parseval hM]
  congr 1
  have hbox_sq : ∑ x ∈ Finset.range M, (boxInd L0 x) ^ 2 = ∑ x ∈ Finset.range M, boxInd L0 x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold boxInd; split_ifs <;> norm_num
  rw [hbox_sq, sum_boxInd hLM]

/-- Left boundary triangle bump `g_L`. -/
noncomputable def gLeft (M L0 : ℕ) (A : ℝ) (p : ℕ) (x : ℕ) : ℝ :=
  (A * (p : ℝ) / ((M : ℝ) * (L0 : ℝ))) * triBump M L0 x

/-- Right boundary triangle bump `g_R(x) = g_L(M - 1 - x)` on `range M`. -/
noncomputable def gRight (M L0 : ℕ) (A : ℝ) (p : ℕ) (x : ℕ) : ℝ :=
  if x < M then gLeft M L0 A p (M - 1 - x) else 0

/-- Combined smooth boundary bump `g = g_L + g_R`. -/
noncomputable def gBump (M L0 : ℕ) (A : ℝ) (p : ℕ) (x : ℕ) : ℝ :=
  gLeft M L0 A p x + gRight M L0 A p x

lemma gLeft_nonneg {M L0 p : ℕ} {A : ℝ} (hA : 0 ≤ A) (x : ℕ) :
    0 ≤ gLeft M L0 A p x := by
  unfold gLeft
  exact mul_nonneg (by positivity) (triBump_nonneg M L0 x)

lemma gRight_nonneg {M L0 p : ℕ} {A : ℝ} (hA : 0 ≤ A) (x : ℕ) :
    0 ≤ gRight M L0 A p x := by
  unfold gRight
  split_ifs
  · exact gLeft_nonneg hA _
  · exact le_refl 0

lemma gLeft_eq_zero_of_ge {M L0 p : ℕ} {A : ℝ} (hL0 : 1 ≤ L0) (h2L : 2 * L0 ≤ M)
    {x : ℕ} (hx1 : 2 * L0 - 1 ≤ x) (hxM : x < M) :
    gLeft M L0 A p x = 0 := by
  unfold gLeft
  rw [triBump_eq_zero_of_ge hL0 h2L hx1 hxM, mul_zero]

lemma gRight_eq_zero_of_le {M L0 p : ℕ} {A : ℝ} (hL0 : 1 ≤ L0) (h2L : 2 * L0 ≤ M)
    {x : ℕ} (hx : x ≤ M - 2 * L0) :
    gRight M L0 A p x = 0 := by
  unfold gRight
  by_cases hxM : x < M
  · simp only [hxM, ↓reduceIte]
    exact gLeft_eq_zero_of_ge hL0 h2L (by omega) (by omega)
  · simp [hxM]

lemma gBump_le {M L0 p : ℕ} {A : ℝ} (hL0 : 1 ≤ L0) (h4L : 4 * L0 ≤ M) (hA : 0 ≤ A)
    {x : ℕ} (hxM : x < M) :
    gBump M L0 A p x ≤ A * (p : ℝ) / (M : ℝ) := by
  have hL0pos : (0 : ℝ) < (L0 : ℝ) := Nat.cast_pos.mpr hL0
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbound : ∀ y, gLeft M L0 A p y ≤ A * (p : ℝ) / (M : ℝ) := fun y => by
    unfold gLeft
    calc (A * (p : ℝ) / ((M : ℝ) * (L0 : ℝ))) * triBump M L0 y
        ≤ (A * (p : ℝ) / ((M : ℝ) * (L0 : ℝ))) * (L0 : ℝ) :=
          mul_le_mul_of_nonneg_left (triBump_le (by omega) y) (by positivity)
      _ = A * (p : ℝ) / (M : ℝ) := by field_simp [hL0pos.ne', hMpos.ne']
  unfold gBump
  by_cases hx : x ≤ M - 2 * L0
  · rw [gRight_eq_zero_of_le hL0 (by omega) hx, add_zero]
    exact hbound x
  · rw [gLeft_eq_zero_of_ge hL0 (by omega) (by omega) hxM, zero_add]
    unfold gRight
    simp only [hxM, ↓reduceIte]
    exact hbound (M - 1 - x)

lemma sum_gLeft {M L0 p : ℕ} {A : ℝ} (hM : 0 < M) (hL0 : 1 ≤ L0) (hLM : L0 ≤ M) :
    ∑ x ∈ Finset.range M, gLeft M L0 A p x = A * (p : ℝ) * (L0 : ℝ) / (M : ℝ) := by
  unfold gLeft
  rw [← Finset.mul_sum, sum_triBump hM hLM]
  have hL0ne : (L0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp [hL0ne, hMne]

lemma sum_gRight {M L0 p : ℕ} {A : ℝ} (hM : 0 < M) (hL0 : 1 ≤ L0) (hLM : L0 ≤ M) :
    ∑ x ∈ Finset.range M, gRight M L0 A p x = A * (p : ℝ) * (L0 : ℝ) / (M : ℝ) := by
  have heq : ∑ x ∈ Finset.range M, gRight M L0 A p x = ∑ y ∈ Finset.range M, gLeft M L0 A p y := by
    refine Finset.sum_nbij (fun x => M - 1 - x) ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_range] at ha hb
      dsimp only at hab; omega
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_range] at hy
      refine ⟨M - 1 - y, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
    · intro x hx
      rw [Finset.mem_range] at hx
      unfold gRight
      simp [hx]
  rw [heq, sum_gLeft hM hL0 hLM]

lemma sum_norm_dft_gLeft {M L0 p : ℕ} {A : ℝ} (hM : 0 < M) (hL0 : 1 ≤ L0) (hLM : L0 ≤ M)
    (hA : 0 ≤ A) :
    ∑ ξ ∈ Finset.range M, ‖dft M (gLeft M L0 A p) ξ‖ = A * (p : ℝ) := by
  have hscale : ∀ ξ, ‖dft M (gLeft M L0 A p) ξ‖ =
      (A * (p : ℝ) / ((M : ℝ) * (L0 : ℝ))) * ‖dft M (triBump M L0) ξ‖ := by
    intro ξ
    unfold gLeft
    rw [dft_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl fun ξ _ => hscale ξ, ← Finset.mul_sum, sum_norm_dft_triBump hM hLM]
  have hL0ne : (L0 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp [hL0ne, hMne]

lemma sum_norm_dft_gRight {M L0 p : ℕ} {A : ℝ} (hM : 0 < M) (hL0 : 1 ≤ L0) (hLM : L0 ≤ M)
    (hA : 0 ≤ A) :
    ∑ ξ ∈ Finset.range M, ‖dft M (gRight M L0 A p) ξ‖ = A * (p : ℝ) := by
  have hcongr : ∑ ξ ∈ Finset.range M, ‖dft M (gRight M L0 A p) ξ‖ =
      ∑ ξ ∈ Finset.range M, ‖dft M (gLeft M L0 A p) ξ‖ :=
    Finset.sum_congr rfl fun ξ _ => norm_dft_reflect hM (gLeft M L0 A p) ξ
  rw [hcongr, sum_norm_dft_gLeft hM hL0 hLM hA]

/-! ### Part 3: Elementary Real-Analytic Helpers -/

lemma one_sub_cos_le_sq_div_two (t : ℝ) : 1 - Real.cos t ≤ t ^ 2 / 2 := by
  have hcos : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul' (t / 2)
    have hsc := Real.sin_sq_add_cos_sq (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    linarith
  have hsin : |Real.sin (t / 2)| ≤ |t / 2| := @Real.abs_sin_le_abs (t / 2)
  have hsq : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := sq_le_sq.mpr hsin
  nlinarith

lemma exp_neg_le_inv_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 4 / y ^ 2 := by
  have h1 : y / 2 ≤ Real.exp (y / 2) := by
    have := Real.add_one_le_exp (y / 2)
    linarith
  have hsq : (y / 2) ^ 2 ≤ Real.exp y := by
    have h2 : (y / 2) ^ 2 ≤ Real.exp (y / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [← Real.exp_natCast_mul] at h2
    have harg : ((2 : ℕ) : ℝ) * (y / 2) = y := by push_cast; ring
    rwa [harg] at h2
  rw [Real.exp_neg]
  have hpos : 0 < (y / 2) ^ 2 := by positivity
  calc (Real.exp y)⁻¹ ≤ ((y / 2) ^ 2)⁻¹ := inv_anti₀ hpos hsq
    _ = 4 / y ^ 2 := by field_simp [hy.ne']; ring

lemma exp_neg_le_inv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 1 / y := by
  have h1 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hy h1

/-! ### Part 4: Modular Steps for `p ≥ 10000` -/

/-- Step D elementary tail & overhead bound for `p ≥ 10000`. -/
private lemma smooth_bump_overhead_bound {p H : ℕ} (hp10k : 10000 ≤ p)
    (hM_eq : p ^ 2 - 1 = 2 * H) :
    let M : ℕ := p ^ 2 - 1
    let sp : ℝ := Real.sqrt (p : ℝ)
    let θ : ℝ := 2 * Real.pi / sp
    let ρ : ℝ := Real.exp (-θ)
    1 / (M : ℝ) + 1 / (4 * ((p : ℝ) + 1)) + (1 / 2 : ℝ) * ρ ^ (p - 1) +
      (1 / 4 : ℝ) * (p : ℝ) * (2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ))) ≤
    1 / (200 * sp) := by
  intro M sp θ ρ
  have hpR_ge : (10000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp10k
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hMR_eq : (M : ℝ) = (p : ℝ) ^ 2 - 1 := by
    dsimp only [M]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2), Nat.cast_pow, Nat.cast_one]
  have hM_posR : (0 : ℝ) < (M : ℝ) := by nlinarith
  have hsp_sq : sp ^ 2 = (p : ℝ) := Real.sq_sqrt hp_pos.le
  have hsp_ge : (100 : ℝ) ≤ sp := by
    have h1 : Real.sqrt (10000 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hpR_ge
    have h2 : Real.sqrt (10000 : ℝ) = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsp_pos : 0 < sp := by linarith
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hθ_pos : 0 < θ := by dsimp only [θ]; positivity
  have hρ_lt1 : ρ < 1 := by dsimp only [ρ]; rw [Real.exp_lt_one_iff]; linarith
  have hρ_div_le : ρ / (1 - ρ) ≤ 1 / θ := by
    have hexp : θ ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
    have heq : ρ / (1 - ρ) = 1 / (Real.exp θ - 1) := by
      dsimp only [ρ]
      have hne1 : 1 - Real.exp (-θ) ≠ 0 := by linarith [hρ_lt1]
      have hne2 : Real.exp θ - 1 ≠ 0 := by linarith
      rw [Real.exp_neg]
      have hne3 : Real.exp θ ≠ 0 := (Real.exp_pos θ).ne'
      field_simp [hne1, hne2, hne3]
    rw [heq]
    exact one_div_le_one_div_of_le hθ_pos hexp
  have hρ_p1_bound : ρ ^ (p - 1) ≤ (p : ℝ) / (9 * ((p : ℝ) - 1) ^ 2) := by
    have harg : ρ ^ (p - 1) = Real.exp (-(((p - 1 : ℕ) : ℝ) * θ)) := by
      dsimp only [ρ]; rw [← Real.exp_natCast_mul]; congr 1; ring
    rw [harg]
    have hp1_eq : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hy_pos : 0 < ((p - 1 : ℕ) : ℝ) * θ := by rw [hp1_eq]; nlinarith only [hpR_ge, hθ_pos]
    have hexp := exp_neg_le_inv_sq hy_pos
    rw [hp1_eq] at hexp ⊢
    calc Real.exp (-(((p : ℝ) - 1) * θ))
        ≤ 4 / (((p : ℝ) - 1) * θ) ^ 2 := hexp
      _ = (p : ℝ) / (Real.pi ^ 2 * ((p : ℝ) - 1) ^ 2) := by
          dsimp only [θ]
          have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
          have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp [hpi_ne, hp1_ne, hsp_pos.ne']
          rw [hsp_sq]; ring
      _ ≤ (p : ℝ) / (9 * ((p : ℝ) - 1) ^ 2) := by
          refine div_le_div_of_nonneg_left hp_pos.le (by nlinarith) ?_
          have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [hpi3]
          nlinarith [sq_nonneg ((p : ℝ) - 1)]
  have hρH_tail : 2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ)) ≤ 4 * (p : ℝ) / (9 * (M : ℝ) ^ 2) := by
    have harg : ρ ^ H = Real.exp (-((H : ℝ) * θ)) := by
      dsimp only [ρ]; rw [← Real.exp_natCast_mul]; congr 1; ring
    have hHθ_eq : (H : ℝ) * θ = Real.pi * (M : ℝ) / sp := by
      have h2H : (M : ℝ) = 2 * (H : ℝ) := by exact_mod_cast hM_eq
      dsimp only [θ]; rw [h2H]; field_simp [hsp_pos.ne']
    have hρH_le : ρ ^ H ≤ sp / (3 * (M : ℝ)) := by
      rw [harg, hHθ_eq]
      have h1 := exp_neg_le_inv (by positivity : 0 < Real.pi * (M : ℝ) / sp)
      rw [one_div_div] at h1
      exact h1.trans (div_le_div_of_nonneg_left hsp_pos.le (by positivity) (by nlinarith [hpi3]))
    have hfac_le : (1 + ρ) / (1 - ρ) ≤ 2 * sp / 3 := by
      have h1 : (1 + ρ) / (1 - ρ) = 1 + 2 * (ρ / (1 - ρ)) := by
        have hne : 1 - ρ ≠ 0 := by linarith
        field_simp [hne]; ring
      rw [h1]
      have h2 : 1 / θ ≤ sp / 6 := by
        dsimp only [θ]
        rw [one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hpi3]
      have h3 : ρ / (1 - ρ) ≤ sp / 6 := hρ_div_le.trans h2
      linarith [hsp_ge]
    calc 2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ))
        ≤ 2 * (sp / (3 * (M : ℝ))) / (M : ℝ) * (2 * sp / 3) := by
          refine mul_le_mul ?_ hfac_le (by positivity) (by positivity)
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hρH_le (by norm_num)) hM_posR.le
      _ = 4 * sp ^ 2 / (9 * (M : ℝ) ^ 2) := by ring
      _ = 4 * (p : ℝ) / (9 * (M : ℝ) ^ 2) := by rw [hsp_sq]
  have ht1 : 1 / (M : ℝ) ≤ 1 / (10 * (p : ℝ)) := by
    rw [div_le_div_iff₀ hM_posR (by positivity)]; nlinarith [hMR_eq, hpR_ge]
  have ht2 : 1 / (4 * ((p : ℝ) + 1)) ≤ 1 / (4 * (p : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have ht3 : (1 / 2 : ℝ) * ρ ^ (p - 1) ≤ 1 / (10 * (p : ℝ)) := by
    have h1 : (1 / 2 : ℝ) * ρ ^ (p - 1) ≤ (p : ℝ) / (18 * ((p : ℝ) - 1) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hρ_p1_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hrew : (1 / 2 : ℝ) * ((p : ℝ) / (9 * ((p : ℝ) - 1) ^ 2)) =
          (p : ℝ) / (18 * ((p : ℝ) - 1) ^ 2) := by
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith only [hpR_ge]
        field_simp [hne]; ring
      linarith only [hmul, hrew]
    have h2 : (p : ℝ) / (18 * ((p : ℝ) - 1) ^ 2) ≤ 1 / (10 * (p : ℝ)) := by
      rw [div_le_div_iff₀ (by nlinarith only [hpR_ge]) (by positivity)]
      nlinarith only [hpR_ge]
    exact h1.trans h2
  have ht4 : (1 / 4 : ℝ) * (p : ℝ) * (2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ))) ≤
      1 / (20 * (p : ℝ)) := by
    have h1 : (1 / 4 : ℝ) * (p : ℝ) * (2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ))) ≤
        (p : ℝ) ^ 2 / (9 * (M : ℝ) ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_left hρH_tail (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * (p : ℝ))
      have hrew : (1 / 4 : ℝ) * (p : ℝ) * (4 * (p : ℝ) / (9 * (M : ℝ) ^ 2)) =
          (p : ℝ) ^ 2 / (9 * (M : ℝ) ^ 2) := by ring
      linarith only [hmul, hrew]
    have h2 : (p : ℝ) ^ 2 / (9 * (M : ℝ) ^ 2) ≤ 1 / (20 * (p : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hM_ge : (1 / 2 : ℝ) * (p : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hMR_eq, hpR_ge]
      have hM2_ge : (1 / 4 : ℝ) * (p : ℝ) ^ 4 ≤ (M : ℝ) ^ 2 := by nlinarith only [hM_ge, hp_pos]
      nlinarith only [hM2_ge, hpR_ge]
    exact h1.trans h2
  have hsum_p : 1 / (10 * (p : ℝ)) + 1 / (4 * (p : ℝ)) + 1 / (10 * (p : ℝ)) + 1 / (20 * (p : ℝ)) =
      1 / (2 * (p : ℝ)) := by field_simp [hp_pos.ne']; ring
  have hp_vs_sp : 1 / (2 * (p : ℝ)) ≤ 1 / (200 * sp) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsp_sq, hsp_ge]
  linarith

/-- Step E (Case 2) algebraic Poisson dip lower bound:
for `p ≥ 10000` and `1 ≤ d < 2 L0`, `2 P_ρ(cos(2π d / M)) - P_{ρ^2}(cos(2π d / M)) ≥ (5/28) √p`. -/
private lemma smooth_bump_poisson_dip_case2 {p d : ℕ} (hp10k : 10000 ≤ p)
    (hd_ub : (d : ℝ) ≤ (1 / 2 : ℝ) * (p : ℝ) * Real.sqrt (p : ℝ)) :
    let M : ℕ := p ^ 2 - 1
    let sp : ℝ := Real.sqrt (p : ℝ)
    let θ : ℝ := 2 * Real.pi / sp
    let ρ : ℝ := Real.exp (-θ)
    let c : ℝ := Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ))
    (5 / 28 : ℝ) * sp ≤ 2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c := by
  intro M sp θ ρ c
  have hpR_ge : (10000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp10k
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hMR_eq : (M : ℝ) = (p : ℝ) ^ 2 - 1 := by
    dsimp only [M]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2), Nat.cast_pow, Nat.cast_one]
  have hM_posR : (0 : ℝ) < (M : ℝ) := by nlinarith
  have hsp_sq : sp ^ 2 = (p : ℝ) := Real.sq_sqrt hp_pos.le
  have hsp_ge : (100 : ℝ) ≤ sp := by
    have h1 : Real.sqrt (10000 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hpR_ge
    have h2 : Real.sqrt (10000 : ℝ) = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsp_pos : 0 < sp := by linarith
  have hpi4 : Real.pi < (4 : ℝ) := Real.pi_lt_four
  have hθ_pos : 0 < θ := by dsimp only [θ]; positivity
  have hθ_le : θ ≤ 2 / 25 := by dsimp only [θ]; rw [div_le_iff₀ hsp_pos]; nlinarith
  have hρ_pos : 0 < ρ := Real.exp_pos _
  have hρ_lt1 : ρ < 1 := by dsimp only [ρ]; rw [Real.exp_lt_one_iff]; linarith
  have h1mρ_le : 1 - ρ ≤ θ := one_sub_exp_neg_le θ
  have hρ_ge : 1 - θ ≤ ρ := by linarith
  have h1mρ_ge : θ / (1 + θ) ≤ 1 - ρ := by
    have hexp : 1 + θ ≤ Real.exp θ := by linarith [Real.add_one_le_exp θ]
    have hρ_le : ρ ≤ 1 / (1 + θ) := by
      dsimp only [ρ]; rw [Real.exp_neg, one_div]; exact inv_anti₀ (by linarith) hexp
    have h1 : 1 - 1 / (1 + θ) = θ / (1 + θ) := by
      have hne : (1 + θ) ≠ 0 := by linarith
      field_simp [hne]; ring
    linarith
  have hc_le : c ≤ 1 := Real.cos_le_one _
  have h1mc_le : 1 - c ≤ (13 / 100 : ℝ) * θ ^ 2 := by
    have hcos_b := one_sub_cos_le_sq_div_two (2 * Real.pi * (d : ℝ) / (M : ℝ))
    have hstep1 : (2 * Real.pi * (d : ℝ) / (M : ℝ)) ^ 2 / 2 ≤
        (Real.pi ^ 2 * (p : ℝ) ^ 3) / (2 * (M : ℝ) ^ 2) := by
      have hd2 : (d : ℝ) ^ 2 ≤ (1 / 4 : ℝ) * (p : ℝ) ^ 3 := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg d) hd_ub 2
        nlinarith only [this, hsp_sq, hp_pos]
      have hrew : (2 * Real.pi * (d : ℝ) / (M : ℝ)) ^ 2 / 2 =
          (2 * Real.pi ^ 2 / (M : ℝ) ^ 2) * (d : ℝ) ^ 2 := by ring
      have hrew2 : (Real.pi ^ 2 * (p : ℝ) ^ 3) / (2 * (M : ℝ) ^ 2) =
          (2 * Real.pi ^ 2 / (M : ℝ) ^ 2) * ((1 / 4 : ℝ) * (p : ℝ) ^ 3) := by ring
      rw [hrew, hrew2]
      exact mul_le_mul_of_nonneg_left hd2 (by positivity)
    have hstep2 : (Real.pi ^ 2 * (p : ℝ) ^ 3) / (2 * (M : ℝ) ^ 2) ≤ (13 / 100 : ℝ) * θ ^ 2 := by
      have hθ2 : θ ^ 2 = 4 * Real.pi ^ 2 / (p : ℝ) := by
        dsimp only [θ]; rw [div_pow, hsp_sq]; ring
      rw [hθ2]
      have hrew : (13 / 100 : ℝ) * (4 * Real.pi ^ 2 / (p : ℝ)) =
          (13 / 25 : ℝ) * Real.pi ^ 2 / (p : ℝ) := by ring
      rw [hrew, div_le_div_iff₀ (by positivity) hp_pos]
      have hM_ge : (999 / 1000 : ℝ) * (p : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hMR_eq, hpR_ge]
      have hM2_ge : (99 / 100 : ℝ) * (p : ℝ) ^ 4 ≤ (M : ℝ) ^ 2 := by
        nlinarith only [hM_ge, hp_pos]
      have hpi2_nn : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      have hmain : (p : ℝ) ^ 4 ≤ (26 / 25 : ℝ) * (M : ℝ) ^ 2 := by nlinarith only [hM2_ge, hp_pos]
      have hmul := mul_le_mul_of_nonneg_left hmain hpi2_nn
      linarith only [hmul]
    exact (hcos_b.trans hstep1).trans hstep2
  have h1mc_le_001 : 1 - c ≤ 1 / 100 := by
    have hθ2_le : θ ^ 2 ≤ (2 / 25 : ℝ) ^ 2 := pow_le_pow_left₀ hθ_pos.le hθ_le 2
    linarith only [h1mc_le, hθ2_le]
  rw [poissonFactor_dip_eq hρ_pos hρ_lt1 hc_le]
  have h1pθ_le : 1 + θ ≤ 27 / 25 := by linarith only [hθ_le]
  have h1mρ_ge_c : (25 / 27 : ℝ) * θ ≤ 1 - ρ := by
    have h1 : θ / (27 / 25 : ℝ) ≤ θ / (1 + θ) :=
      div_le_div_of_nonneg_left hθ_pos.le (by linarith only [hθ_pos]) h1pθ_le
    linarith only [h1, h1mρ_ge]
  have h1mρ2_ge_c : (48 / 27 : ℝ) * θ ≤ 1 - ρ ^ 2 := by
    have h1 : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
    have h2 : 48 / 25 ≤ 1 + ρ := by linarith only [hρ_ge, hθ_le]
    rw [h1]
    nlinarith only [h1mρ_ge_c, h2, hθ_pos]
  have hnum_mid : (11 / 2 : ℝ) ≤ 1 + ρ ^ 2 + 2 * ρ * (1 + c) := by
    have hρ_ge92 : (23 / 25 : ℝ) ≤ ρ := by linarith only [hρ_ge, hθ_le]
    have h1pc_ge : (199 / 100 : ℝ) ≤ 1 + c := by linarith only [h1mc_le_001]
    nlinarith only [hρ_ge92, h1pc_ge]
  have hnum_lb :
      (48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) * θ ^ 3 ≤
      (1 - ρ ^ 2) * (1 - ρ) ^ 2 * (1 + ρ ^ 2 + 2 * ρ * (1 + c)) := by
    have h1 : ((25 / 27 : ℝ) * θ) ^ 2 ≤ (1 - ρ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1mρ_ge_c 2
    have h1mρ2_nn : 0 ≤ 1 - ρ ^ 2 := by nlinarith only [hρ_pos, hρ_lt1]
    have h2 : (48 / 27 : ℝ) * θ * ((25 / 27 : ℝ) * θ) ^ 2 ≤ (1 - ρ ^ 2) * (1 - ρ) ^ 2 :=
      mul_le_mul h1mρ2_ge_c h1 (by positivity) h1mρ2_nn
    have h3 : (48 / 27 : ℝ) * θ * ((25 / 27 : ℝ) * θ) ^ 2 * (11 / 2 : ℝ) ≤
        (1 - ρ ^ 2) * (1 - ρ) ^ 2 * (1 + ρ ^ 2 + 2 * ρ * (1 + c)) :=
      mul_le_mul h2 hnum_mid (by norm_num) (mul_nonneg h1mρ2_nn (sq_nonneg _))
    linarith only [h3]
  have hden1_ub : (1 - ρ) ^ 2 + 2 * ρ * (1 - c) ≤ (126 / 100 : ℝ) * θ ^ 2 := by
    have h1 : (1 - ρ) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ (by linarith only [hρ_lt1]) h1mρ_le 2
    have h2 : 2 * ρ * (1 - c) ≤ 2 * (1 - c) := by nlinarith only [hc_le, hρ_lt1]
    linarith only [h1, h2, h1mc_le]
  have hden2_ub : (1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c) ≤ (426 / 100 : ℝ) * θ ^ 2 := by
    have h1mρ2_le : 1 - ρ ^ 2 ≤ 2 * θ := by nlinarith only [h1mρ_le, hρ_lt1]
    have h1mρ2_nn : 0 ≤ 1 - ρ ^ 2 := by nlinarith only [hρ_pos, hρ_lt1]
    have h1 : (1 - ρ ^ 2) ^ 2 ≤ (2 * θ) ^ 2 := pow_le_pow_left₀ h1mρ2_nn h1mρ2_le 2
    have hρ2_le1 : ρ ^ 2 ≤ 1 := by nlinarith only [hρ_pos, hρ_lt1]
    have h2 : 2 * ρ ^ 2 * (1 - c) ≤ 2 * (1 - c) := by nlinarith only [hc_le, hρ2_le1]
    linarith only [h1, h2, h1mc_le]
  have hden_pos : 0 < ((1 - ρ) ^ 2 + 2 * ρ * (1 - c)) *
      ((1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c)) := by
    have h1 : 0 < (1 - ρ) ^ 2 + 2 * ρ * (1 - c) := by
      have : 0 < (1 - ρ) ^ 2 := sq_pos_of_pos (by linarith only [hρ_lt1])
      nlinarith only [this, hρ_pos, hc_le]
    have h2 : 0 < (1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c) := by
      have : 0 < (1 - ρ ^ 2) ^ 2 := sq_pos_of_pos (by nlinarith only [hρ_pos, hρ_lt1])
      nlinarith only [this, hρ_pos, hc_le]
    exact mul_pos h1 h2
  have hden_ub : ((1 - ρ) ^ 2 + 2 * ρ * (1 - c)) *
      ((1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c)) ≤
      ((126 / 100 : ℝ) * (426 / 100 : ℝ)) * θ ^ 4 := by
    have h2nn : 0 ≤ (1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c) := by
      have : 0 ≤ 2 * ρ ^ 2 * (1 - c) := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ρ))
        (by linarith only [hc_le])
      linarith only [sq_nonneg (1 - ρ ^ 2), this]
    have := mul_le_mul hden1_ub hden2_ub h2nn (by positivity)
    linarith only [this]
  have hratio :
      ((48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) * θ ^ 3) /
        (((126 / 100 : ℝ) * (426 / 100 : ℝ)) * θ ^ 4) ≤
      ((1 - ρ ^ 2) * (1 - ρ) ^ 2 * (1 + ρ ^ 2 + 2 * ρ * (1 + c))) /
        (((1 - ρ) ^ 2 + 2 * ρ * (1 - c)) * ((1 - ρ ^ 2) ^ 2 + 2 * ρ ^ 2 * (1 - c))) :=
    div_le_div₀
      (le_trans (by positivity) hnum_lb) hnum_lb hden_pos hden_ub
  have hconst_ge : (5 / 28 : ℝ) * sp ≤
      ((48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) * θ ^ 3) /
        (((126 / 100 : ℝ) * (426 / 100 : ℝ)) * θ ^ 4) := by
    have hsimp :
        ((48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) * θ ^ 3) /
          (((126 / 100 : ℝ) * (426 / 100 : ℝ)) * θ ^ 4) =
        ((48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) /
          ((126 / 100 : ℝ) * (426 / 100 : ℝ))) * (1 / θ) := by
      field_simp [hθ_pos.ne']
    rw [hsimp]
    have h1θ_ge : sp / 8 ≤ 1 / θ := by
      dsimp only [θ]
      rw [one_div_div, div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith [hpi4]
    have hrat_ge : (10 / 7 : ℝ) ≤
        (48 / 27 : ℝ) * (25 / 27 : ℝ) ^ 2 * (11 / 2 : ℝ) /
          ((126 / 100 : ℝ) * (426 / 100 : ℝ)) := by norm_num
    nlinarith
  exact hconst_ge.trans hratio

/-- Step C: Exact cyclic autocorrelation upper bound on the bulk high-pass function `f`. -/
private lemma smooth_bump_f_ac_cyc {p H : ℕ} (hp10k : 10000 ≤ p)
    (hM_eq : p ^ 2 - 1 = 2 * H)
    {S : Finset ℕ} (hS_sub : S ⊆ Finset.range (p ^ 2 - 1)) (hS_card : S.card = p)
    (hflat : ∀ ξ : ℕ, 1 ≤ ξ → ξ < p ^ 2 - 1 →
      ‖∑ a ∈ S, (rootOfUnity (p ^ 2 - 1)) ^ (ξ * a)‖ ^ 2 =
        if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ))
    {d : ℕ} (hd1 : 1 ≤ d) (hdM : d < p ^ 2 - 1) :
    let M : ℕ := p ^ 2 - 1
    let sp : ℝ := Real.sqrt (p : ℝ)
    let ρ : ℝ := Real.exp (-(2 * Real.pi / sp))
    let indS : ℕ → ℝ := fun x => if x ∈ S then 1 else 0
    let f : ℕ → ℝ := fun x => (p : ℝ) / (M : ℝ) + (1 / 2 : ℝ) * (indS x - cyclicConv M indS (poissonKernel M ρ) x)
    cyclicXcorr M f f d ≤
      1 + 1 / (200 * sp) -
        (1 / 4 : ℝ) * (p : ℝ) *
          ((2 * poissonFactor ρ (Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ))) -
            poissonFactor (ρ ^ 2) (Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ)))) / (M : ℝ)) := by
  classical
  intro M sp ρ indS f
  have hM_ge2 : 2 ≤ M := by
    dsimp only [M]
    have : 10000 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp10k 2
    omega
  have hH_pos : 0 < H := by omega
  have hM_pos : 0 < M := by omega
  have hM_fac : M = (p - 1) * (p + 1) := by
    dsimp only [M]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hpR_ge : (10000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp10k
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hMR_eq : (M : ℝ) = (p : ℝ) ^ 2 - 1 := by
    dsimp only [M]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2), Nat.cast_pow, Nat.cast_one]
  have hM_posR : (0 : ℝ) < (M : ℝ) := by nlinarith
  have hsp_pos : 0 < sp := Real.sqrt_pos.mpr hp_pos
  have hρ_pos : 0 < ρ := Real.exp_pos _
  have hM_eq2 : M = 2 * H := hM_eq
  have hρ_lt1 : ρ < 1 := by
    dsimp only [ρ]; rw [Real.exp_lt_one_iff]
    have hpos : 0 < 2 * Real.pi / sp := div_pos (mul_pos (by norm_num) Real.pi_pos) hsp_pos
    linarith only [hpos]
  have hdft_indS : ∀ ξ, dft M indS ξ = ∑ a ∈ S, (rootOfUnity M) ^ (ξ * a) :=
    fun ξ => dft_indicator hS_sub ξ
  have hdft_hρ : ∀ ξ, ξ < M → dft M (poissonKernel M ρ) ξ = ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) := by
    intro ξ hξ; rw [hM_eq2] at hξ ⊢; exact dft_poissonKernel hH_pos hρ_pos hρ_lt1 hξ
  have hdft_f_zero : dft M f 0 = (p : ℂ) := by
    dsimp only [f]
    rw [dft_add, dft_const hM_pos, if_pos (dvd_zero M), dft_smul, dft_sub,
      dft_cyclicConv hM_pos, hdft_hρ 0 hM_pos]
    simp only [Nat.min_eq_left (Nat.zero_le _), pow_zero, Complex.ofReal_one, mul_one, sub_self,
      mul_zero, add_zero]
    have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM_pos.ne'
    push_cast; field_simp [hMne]
  have hdft_f_nz : ∀ ξ, 1 ≤ ξ → ξ < M →
      dft M f ξ = ((1 / 2 : ℝ) : ℂ) * dft M indS ξ * ((1 - ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) := by
    intro ξ hξ1 hξM
    dsimp only [f]
    have hndvd : ¬ M ∣ ξ := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    rw [dft_add, dft_const hM_pos, if_neg hndvd, zero_add, dft_smul, dft_sub,
      dft_cyclicConv hM_pos, hdft_hρ ξ hξM]
    push_cast; ring
  rw [cyclicXcorr_eq_dft hM_pos, ← Finset.sum_range_add_sum_Ico _ hM_pos]
  have h0term : (∑ ξ ∈ Finset.range 1,
      dft M f ξ * starRingEnd ℂ (dft M f ξ) * (rootOfUnity M) ^ (ξ * d)).re = (p : ℝ) ^ 2 := by
    simp [hdft_f_zero, sq]
  rw [Complex.add_re, h0term, mul_add]
  let multP : Finset ℕ := (Finset.Ico 1 M).filter (fun ξ => (p - 1) ∣ ξ)
  have hsplit_nz :
      (∑ ξ ∈ Finset.Ico 1 M,
        dft M f ξ * starRingEnd ℂ (dft M f ξ) * (rootOfUnity M) ^ (ξ * d)) =
      ((1 / 4 : ℝ) * (p : ℝ) : ℂ) *
        (∑ ξ ∈ Finset.Ico 1 M,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)) -
      ((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℂ) *
        (∑ ξ ∈ multP,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have hsub_fil :
        ∑ ξ ∈ multP,
          ((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℂ) *
            ((((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)) =
        ∑ ξ ∈ Finset.Ico 1 M,
          if (p - 1) ∣ ξ then
            ((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℂ) *
              ((((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d))
          else 0 := Finset.sum_filter _ _
    rw [hsub_fil, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [Finset.mem_Ico] at hξ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hnsq : ‖dft M f ξ‖ ^ 2 =
        (1 / 4 : ℝ) * (if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ)) *
          (1 - ρ ^ (min ξ (M - ξ))) ^ 2 := by
      rw [hdft_f_nz ξ hξ.1 hξ.2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
        hdft_indS ξ, hflat ξ hξ.1 hξ.2]
      ring
    rw [hnsq]
    by_cases hdvd : (p - 1) ∣ ξ <;> simp only [hdvd, ↓reduceIte] <;> push_cast <;> ring
  have hsum_main :
      ∑ ξ ∈ Finset.Ico 1 M,
        (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) =
      (-((M : ℝ) * (2 * poissonKernel M ρ d - poissonKernel M (ρ ^ 2) d)) : ℝ) := by
    have hadd0 :
        ∑ ξ ∈ Finset.Ico 1 M,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) =
        ∑ ξ ∈ Finset.range M,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) := by
      rw [← Finset.sum_range_add_sum_Ico _ hM_pos]; simp
    rw [hadd0]
    have hexp :
        ∑ ξ ∈ Finset.range M,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) =
        (∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * d)) -
        2 * (∑ ξ ∈ Finset.range M, ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)) +
        (∑ ξ ∈ Finset.range M, (((ρ ^ 2) ^ (min ξ (M - ξ)) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      have hpow2 : (ρ ^ 2) ^ (min ξ (M - ξ)) = (ρ ^ (min ξ (M - ξ))) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]
      rw [hpow2]; push_cast; ring
    rw [hexp]
    have hndvd_d : ¬ M ∣ d := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    have hzero_sum : ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * d) = 0 := by
      rw [sum_rootOfUnity_ortho hM_pos d, if_neg hndvd_d]
    have hP1 : ∑ ξ ∈ Finset.range M,
        ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) =
        ((M : ℝ) * poissonKernel M ρ d : ℝ) := by
      rw [hM_eq2]; exact sum_poisson_freq_mul_pow hH_pos hρ_pos hρ_lt1 d
    have hP2 : ∑ ξ ∈ Finset.range M,
        (((ρ ^ 2) ^ (min ξ (M - ξ)) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d) =
        ((M : ℝ) * poissonKernel M (ρ ^ 2) d : ℝ) := by
      rw [hM_eq2]; exact sum_poisson_freq_mul_pow hH_pos (sq_pos_of_pos hρ_pos)
        (by nlinarith only [hρ_pos, hρ_lt1]) d
    rw [hzero_sum, hP1, hP2]; push_cast; ring
  have hsum_multP_re :
      -(1 : ℝ) - 2 * (p : ℝ) * ρ ^ (p - 1) ≤
      (∑ ξ ∈ multP,
        (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re := by
    have hmultP_eq : multP = (Finset.Ico 1 (p + 1)).image (fun m => m * (p - 1)) := by
      ext ξ
      simp only [multP, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
      constructor
      · rintro ⟨⟨hξ1, hξM⟩, m, rfl⟩
        refine ⟨m, ⟨?_, ?_⟩, by ring⟩
        · by_contra hm0; have : m = 0 := by omega
          subst this; simp at hξ1
        · rw [hM_fac] at hξM; nlinarith
      · rintro ⟨m, ⟨hm1, hmp⟩, rfl⟩
        refine ⟨⟨by nlinarith, by rw [hM_fac]; nlinarith⟩, m, by ring⟩
    rw [hmultP_eq, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_right (by omega) h)]
    have hdecomp :
        ∑ m ∈ Finset.Ico 1 (p + 1),
          (((1 - ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2 : ℝ) : ℂ) *
            (rootOfUnity M) ^ (m * (p - 1) * d) =
        (∑ m ∈ Finset.Ico 1 (p + 1), (rootOfUnity M) ^ (m * (p - 1) * d)) -
        (∑ m ∈ Finset.Ico 1 (p + 1),
          (((2 * ρ ^ (min (m * (p - 1)) (M - m * (p - 1))) -
              (ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2) : ℝ) : ℂ) *
            (rootOfUnity M) ^ (m * (p - 1) * d)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast; ring
    rw [hdecomp, Complex.sub_re]
    have hpiece1 : -(1 : ℝ) ≤ (∑ m ∈ Finset.Ico 1 (p + 1), (rootOfUnity M) ^ (m * (p - 1) * d)).re := by
      set ζ : ℂ := (rootOfUnity M) ^ ((p - 1) * d)
      have hpow_m : ∀ m : ℕ, (rootOfUnity M) ^ (m * (p - 1) * d) = ζ ^ m := fun m => by
        dsimp only [ζ]; rw [← pow_mul]; congr 1; ring
      rw [Finset.sum_congr rfl fun m _ => hpow_m m]
      have hadd0 : (∑ m ∈ Finset.Ico 1 (p + 1), ζ ^ m) = (∑ m ∈ Finset.range (p + 1), ζ ^ m) - 1 := by
        rw [← Finset.sum_range_add_sum_Ico _ (by omega : 1 ≤ p + 1)]; simp
      rw [hadd0]
      by_cases hζ1 : ζ = 1
      · rw [hζ1]; simp; linarith
      · have hζpow : ζ ^ (p + 1) = 1 := by
          dsimp only [ζ]
          rw [← pow_mul, show (p - 1) * d * (p + 1) = M * d by rw [hM_fac]; ring,
            pow_mul, rootOfUnity_pow_M hM_pos, one_pow]
        rw [geom_sum_eq hζ1, hζpow, sub_self, zero_div, zero_sub]; simp
    have hpiece2 :
        (∑ m ∈ Finset.Ico 1 (p + 1),
          (((2 * ρ ^ (min (m * (p - 1)) (M - m * (p - 1))) -
              (ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2) : ℝ) : ℂ) *
            (rootOfUnity M) ^ (m * (p - 1) * d)).re ≤
        2 * (p : ℝ) * ρ ^ (p - 1) := by
      calc (∑ m ∈ Finset.Ico 1 (p + 1),
            (((2 * ρ ^ (min (m * (p - 1)) (M - m * (p - 1))) -
                (ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2) : ℝ) : ℂ) *
              (rootOfUnity M) ^ (m * (p - 1) * d)).re
          ≤ ‖∑ m ∈ Finset.Ico 1 (p + 1),
            (((2 * ρ ^ (min (m * (p - 1)) (M - m * (p - 1))) -
                (ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2) : ℝ) : ℂ) *
              (rootOfUnity M) ^ (m * (p - 1) * d)‖ := Complex.re_le_norm _
        _ ≤ ∑ m ∈ Finset.Ico 1 (p + 1),
            ‖(((2 * ρ ^ (min (m * (p - 1)) (M - m * (p - 1))) -
                (ρ ^ (min (m * (p - 1)) (M - m * (p - 1)))) ^ 2) : ℝ) : ℂ) *
              (rootOfUnity M) ^ (m * (p - 1) * d)‖ := norm_sum_le _ _
        _ ≤ ∑ m ∈ Finset.Ico 1 (p + 1), 2 * ρ ^ (p - 1) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [Finset.mem_Ico] at hm
            rw [norm_mul, Complex.norm_real, norm_rootOfUnity_pow, mul_one]
            set k := min (m * (p - 1)) (M - m * (p - 1))
            have hk_ge : p - 1 ≤ k := by
              dsimp only [k]
              have h1 : p - 1 ≤ m * (p - 1) := Nat.le_mul_of_pos_left _ (by omega)
              have h2 : p - 1 ≤ M - m * (p - 1) := by
                rw [hM_fac]
                have : (m + 1) * (p - 1) ≤ (p + 1) * (p - 1) :=
                  Nat.mul_le_mul_right _ (by omega)
                have hmul : (m + 1) * (p - 1) = m * (p - 1) + (p - 1) := by ring
                have hcomm : (p - 1) * (p + 1) = (p + 1) * (p - 1) := mul_comm _ _
                omega
              exact le_min h1 h2
            have hρk_le : ρ ^ k ≤ ρ ^ (p - 1) := pow_le_pow_of_le_one hρ_pos.le hρ_lt1.le hk_ge
            have hρk_nn : 0 ≤ ρ ^ k := pow_nonneg hρ_pos.le k
            have hρk_le1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ_pos.le hρ_lt1.le
            have hval_nn : 0 ≤ 2 * ρ ^ k - (ρ ^ k) ^ 2 := by nlinarith
            rw [Real.norm_of_nonneg hval_nn]; nlinarith
        _ = 2 * (p : ℝ) * ρ ^ (p - 1) := by
            rw [Finset.sum_const, Nat.card_Ico, show p + 1 - 1 = p by omega, nsmul_eq_mul]; ring
    linarith
  rw [hsplit_nz, Complex.sub_re]
  have hre1 : (((1 / 4 : ℝ) * (p : ℝ) : ℂ) *
      ∑ ξ ∈ Finset.Ico 1 M,
        (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re =
      -(1 / 4 : ℝ) * (p : ℝ) * (M : ℝ) * (2 * poissonKernel M ρ d - poissonKernel M (ρ ^ 2) d) := by
    rw [hsum_main]
    have : ((1 / 4 : ℝ) * (p : ℝ) : ℂ) = (((1 / 4 : ℝ) * (p : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  have hre2 : (((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℂ) *
      ∑ ξ ∈ multP,
        (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re =
      (1 / 4 : ℝ) * ((p : ℝ) - 1) *
        (∑ ξ ∈ multP,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re := by
    have : ((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℂ) = (((1 / 4 : ℝ) * ((p : ℝ) - 1) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hre1, hre2]
  set c : ℝ := Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ))
  have hc_ge : -1 ≤ c := Real.neg_one_le_cos _
  have hc_le : c ≤ 1 := Real.cos_le_one _
  have hQ_lb :
      (2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c) / (M : ℝ) -
        2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ)) ≤
      2 * poissonKernel M ρ d - poissonKernel M (ρ ^ 2) d := by
    unfold poissonKernel
    have hMdiv : M / 2 = H := by omega
    have hpow2 : (ρ ^ 2) ^ H = (ρ ^ H) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
    rw [hMdiv, hpow2]
    have hdiff_eq :
        2 * ((1 - (-1 : ℝ) ^ d * ρ ^ H) / (M : ℝ) * poissonFactor ρ c) -
          (1 - (-1 : ℝ) ^ d * (ρ ^ H) ^ 2) / (M : ℝ) * poissonFactor (ρ ^ 2) c =
        (2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c) / (M : ℝ) -
          ((-1 : ℝ) ^ d * ρ ^ H / (M : ℝ)) *
            (2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c) := by ring
    rw [hdiff_eq]
    have hP1_pos := poissonFactor_pos hρ_pos hρ_lt1 hc_le
    have hP2_pos := poissonFactor_pos (sq_pos_of_pos hρ_pos) (by nlinarith) hc_le
    have hdip_pos := poissonFactor_dip_pos hρ_pos hρ_lt1 hc_ge hc_le
    have hρH_le1 : ρ ^ H ≤ 1 := pow_le_one₀ hρ_pos.le hρ_lt1.le
    have hρH_nn : 0 ≤ ρ ^ H := pow_nonneg hρ_pos.le H
    have hmid_nn : 0 ≤ 2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c := by nlinarith
    have hmid_le : 2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c ≤
        2 * ((1 + ρ) / (1 - ρ)) := by
      have := poissonFactor_le hρ_pos hρ_lt1 hc_le
      nlinarith
    have hsign : |(-1 : ℝ) ^ d| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have habs :
        ((-1 : ℝ) ^ d * ρ ^ H / (M : ℝ)) *
          (2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c) ≤
        2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ)) := by
      calc ((-1 : ℝ) ^ d * ρ ^ H / (M : ℝ)) *
            (2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c)
          ≤ |((-1 : ℝ) ^ d * ρ ^ H / (M : ℝ)) *
              (2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c)| := le_abs_self _
        _ = (ρ ^ H / (M : ℝ)) * (2 * poissonFactor ρ c - ρ ^ H * poissonFactor (ρ ^ 2) c) := by
            rw [abs_mul, abs_div, abs_mul, hsign, one_mul, abs_of_nonneg hρH_nn,
              abs_of_pos hM_posR, abs_of_nonneg hmid_nn]
        _ ≤ (ρ ^ H / (M : ℝ)) * (2 * ((1 + ρ) / (1 - ρ))) :=
            mul_le_mul_of_nonneg_left hmid_le (by positivity)
        _ = 2 * ρ ^ H / (M : ℝ) * ((1 + ρ) / (1 - ρ)) := by ring
    linarith
  have hM_facR : (M : ℝ) = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by linarith only [hMR_eq]
  have hp2_M : (1 / (M : ℝ)) * (p : ℝ) ^ 2 = 1 + 1 / (M : ℝ) := by
    have hMne : (M : ℝ) ≠ 0 := hM_posR.ne'
    field_simp [hMne]; linarith only [hMR_eq]
  have hrem_le :
      -(1 / (M : ℝ)) * ((1 / 4 : ℝ) * ((p : ℝ) - 1) *
        (∑ ξ ∈ multP,
          (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re) ≤
      1 / (4 * ((p : ℝ) + 1)) + (1 / 2 : ℝ) * ρ ^ (p - 1) := by
    have hfac_eq : (1 / (M : ℝ)) * ((1 / 4 : ℝ) * ((p : ℝ) - 1)) = 1 / (4 * ((p : ℝ) + 1)) := by
      rw [hM_facR]
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith only [hpR_ge]
      have h2 : (p : ℝ) + 1 ≠ 0 := by linarith only [hpR_ge]
      field_simp [h1, h2]
    set S_re : ℝ := (∑ ξ ∈ multP,
      (((1 - ρ ^ (min ξ (M - ξ))) ^ 2 : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * d)).re
    have hstep :
        -(1 / (M : ℝ)) * ((1 / 4 : ℝ) * ((p : ℝ) - 1) * S_re) =
        -(1 / (4 * ((p : ℝ) + 1))) * S_re := by
      have := congrArg (fun t => -t * S_re) hfac_eq
      linarith only [this]
    rw [hstep]
    have hmul := mul_le_mul_of_nonneg_left hsum_multP_re
      (by positivity : (0 : ℝ) ≤ 1 / (4 * ((p : ℝ) + 1)))
    have hp_div : 1 / (4 * ((p : ℝ) + 1)) * (2 * (p : ℝ) * ρ ^ (p - 1)) ≤
        (1 / 2 : ℝ) * ρ ^ (p - 1) := by
      have hle : (p : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith only [hpR_ge])]; linarith only [hpR_ge]
      have hrew : 1 / (4 * ((p : ℝ) + 1)) * (2 * (p : ℝ) * ρ ^ (p - 1)) =
          (1 / 2 : ℝ) * ((p : ℝ) / ((p : ℝ) + 1)) * ρ ^ (p - 1) := by
        have hp1ne : (p : ℝ) + 1 ≠ 0 := by linarith only [hpR_ge]
        field_simp [hp1ne]; ring
      rw [hrew]
      have hρ_nn : 0 ≤ ρ ^ (p - 1) := pow_nonneg hρ_pos.le _
      nlinarith only [hle, hρ_nn]
    linarith only [hmul, hp_div]
  have hmain_simpl :
      (1 / (M : ℝ)) * (-(1 / 4 : ℝ) * (p : ℝ) * (M : ℝ) *
        (2 * poissonKernel M ρ d - poissonKernel M (ρ ^ 2) d)) =
      -(1 / 4 : ℝ) * (p : ℝ) * (2 * poissonKernel M ρ d - poissonKernel M (ρ ^ 2) d) := by
    have hMne : (M : ℝ) ≠ 0 := hM_posR.ne'
    field_simp [hMne]
  have hQ_mul := mul_le_mul_of_nonneg_left hQ_lb (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * (p : ℝ))
  have hov := smooth_bump_overhead_bound hp10k hM_eq
  linarith only [hp2_M, hmain_simpl, hQ_mul, hrem_le, hov]

/-- Generic Smooth-Bump Periodic Bose + Poisson Barrier Theorem:
Given ANY prime `p ≥ 10000` (`M = p^2 - 1`) and ANY subset `S ⊆ range M` of size `p`
satisfying Bose's periodic Fourier flatness `‖∑ a ∈ S, ω^(ξ*a)‖^2 = if (p-1) ∣ ξ then 1 else p`,
the explicit witness `μ = f + g_L + g_R` satisfies:
1. `0 ≤ μ x` and `μ x ≤ 1 / √3` for all `x < M`;
2. `∑ x ∈ range (M - d), μ x * μ (x + d) ≤ 1` for all `1 ≤ d < M`;
3. `∑ x ∈ range M, μ x ≥ p + (1 / 250) * √p`. -/
theorem smooth_bump_periodic_barrier_of_bose_flat {p : ℕ} (hp : p.Prime) (hp10k : 10000 ≤ p)
    {S : Finset ℕ} (hS_sub : S ⊆ Finset.range (p ^ 2 - 1)) (hS_card : S.card = p)
    (hflat : ∀ ξ : ℕ, 1 ≤ ξ → ξ < p ^ 2 - 1 →
      ‖∑ a ∈ S, (rootOfUnity (p ^ 2 - 1)) ^ (ξ * a)‖ ^ 2 =
        if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ)) :
    let M : ℕ := p ^ 2 - 1
    ∃ μ : ℕ → ℝ,
      (∀ x, x < M → 0 ≤ μ x ∧ μ x ≤ 1 / Real.sqrt 3) ∧
      (∀ d, 1 ≤ d → d < M → ∑ x ∈ Finset.range (M - d), μ x * μ (x + d) ≤ 1) ∧
      (p : ℝ) + (1 / 250 : ℝ) * Real.sqrt (p : ℝ) ≤ ∑ x ∈ Finset.range M, μ x := by
  classical
  intro M
  have hp_odd : p % 2 = 1 := by
    have h2 : p ≠ 2 := by omega
    rcases hp.eq_two_or_odd with rfl | hodd
    · exact False.elim (h2 rfl)
    · exact hodd
  have hM_fac : M = (p - 1) * (p + 1) := by
    dsimp only [M]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hM_even : 2 ∣ M := by rw [hM_fac]; exact dvd_mul_of_dvd_left (by omega) _
  set H : ℕ := M / 2
  have hM_eq_2H : M = 2 * H := by dsimp only [H]; omega
  have hM_ge2 : 2 ≤ M := by
    dsimp only [M]
    have : 10000 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp10k 2
    omega
  have hH_pos : 0 < H := by omega
  have hM_pos : 0 < M := by omega
  have hpR_ge : (10000 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp10k
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hMR_eq : (M : ℝ) = (p : ℝ) ^ 2 - 1 := by
    dsimp only [M]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2), Nat.cast_pow, Nat.cast_one]
  have hM_posR : (0 : ℝ) < (M : ℝ) := by nlinarith
  set sp : ℝ := Real.sqrt (p : ℝ)
  have hsp_sq : sp ^ 2 = (p : ℝ) := Real.sq_sqrt hp_pos.le
  have hsp_ge : (100 : ℝ) ≤ sp := by
    have h1 : Real.sqrt (10000 : ℝ) ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hpR_ge
    have h2 : Real.sqrt (10000 : ℝ) = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have hsp_pos : 0 < sp := by linarith
  set θ : ℝ := 2 * Real.pi / sp
  have hθ_pos : 0 < θ := by dsimp only [θ]; positivity
  set ρ : ℝ := Real.exp (-θ)
  have hρ_pos : 0 < ρ := Real.exp_pos _
  have hρ_lt1 : ρ < 1 := by dsimp only [ρ]; rw [Real.exp_lt_one_iff]; linarith
  have hρ_div_le : ρ / (1 - ρ) ≤ 1 / θ := by
    have hexp : θ ≤ Real.exp θ - 1 := by linarith [Real.add_one_le_exp θ]
    have heq : ρ / (1 - ρ) = 1 / (Real.exp θ - 1) := by
      dsimp only [ρ]
      have hne1 : 1 - Real.exp (-θ) ≠ 0 := by linarith
      have hne2 : Real.exp θ - 1 ≠ 0 := by linarith
      rw [Real.exp_neg]
      have hne3 : Real.exp θ ≠ 0 := (Real.exp_pos θ).ne'
      field_simp [hne1, hne2, hne3]
    rw [heq]
    exact one_div_le_one_div_of_le hθ_pos hexp
  set L0 : ℕ := Nat.floor ((1 / 4 : ℝ) * (p : ℝ) * sp)
  have hL0_leR : (L0 : ℝ) ≤ (1 / 4 : ℝ) * (p : ℝ) * sp := Nat.floor_le (by positivity)
  have hL0_gtR : (1 / 4 : ℝ) * (p : ℝ) * sp - 1 < (L0 : ℝ) := by
    linarith [Nat.lt_floor_add_one ((1 / 4 : ℝ) * (p : ℝ) * sp)]
  have hL0_ge1 : 1 ≤ L0 := by
    have : (1 : ℝ) ≤ (L0 : ℝ) := by nlinarith
    exact_mod_cast this
  have h4L0_leM : 4 * L0 ≤ M := by
    have hreal : ((4 * L0 : ℕ) : ℝ) ≤ (M : ℝ) := by
      push_cast; nlinarith [hL0_leR, hMR_eq, hsp_sq, hsp_ge]
    exact_mod_cast hreal
  -- Define `indS`, `Sh`, `f`, `gL`, `gR`, `g`, `μ`
  let indS : ℕ → ℝ := fun x => if x ∈ S then 1 else 0
  let hρ : ℕ → ℝ := poissonKernel M ρ
  let Sh : ℕ → ℝ := cyclicConv M indS hρ
  let f : ℕ → ℝ := fun x => (p : ℝ) / (M : ℝ) + (1 / 2 : ℝ) * (indS x - Sh x)
  let gL : ℕ → ℝ := gLeft M L0 (1 / 100 : ℝ) p
  let gR : ℕ → ℝ := gRight M L0 (1 / 100 : ℝ) p
  let g : ℕ → ℝ := gBump M L0 (1 / 100 : ℝ) p
  let μ : ℕ → ℝ := fun x => f x + g x
  -- Basic DFT properties of `indS`, `Sh`, `f`
  have hdft_indS : ∀ ξ, dft M indS ξ = ∑ a ∈ S, (rootOfUnity M) ^ (ξ * a) :=
    fun ξ => dft_indicator hS_sub ξ
  have hnorm_indS_le : ∀ ξ, 1 ≤ ξ → ξ < M → ‖dft M indS ξ‖ ≤ sp := by
    intro ξ hξ1 hξM
    have hsq : ‖dft M indS ξ‖ ^ 2 ≤ (p : ℝ) := by
      rw [hdft_indS ξ, hflat ξ hξ1 hξM]
      split_ifs
      · exact_mod_cast (show 1 ≤ p by omega)
      · exact le_refl _
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hdft_hρ : ∀ ξ, ξ < M → dft M hρ ξ = ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) := by
    intro ξ hξ; dsimp only [hρ]; rw [hM_eq_2H] at hξ ⊢; exact dft_poissonKernel hH_pos hρ_pos hρ_lt1 hξ
  have hdft_Sh : ∀ ξ, ξ < M → dft M Sh ξ = dft M indS ξ * ((ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) := by
    intro ξ hξ; dsimp only [Sh]; rw [dft_cyclicConv hM_pos, hdft_hρ ξ hξ]
  have hdft_f_zero : dft M f 0 = (p : ℂ) := by
    dsimp only [f]
    rw [dft_add, dft_const hM_pos, if_pos (dvd_zero M), dft_smul, dft_sub, hdft_Sh 0 hM_pos]
    simp only [Nat.min_eq_left (Nat.zero_le _), pow_zero, Complex.ofReal_one, mul_one, sub_self,
      mul_zero, add_zero]
    have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM_pos.ne'
    push_cast; field_simp [hMne]
  have hsum_f : ∑ x ∈ Finset.range M, f x = (p : ℝ) := by
    have h := hdft_f_zero; rw [dft_zero] at h; exact_mod_cast congrArg Complex.re h
  have hnorm_f_nz : ∀ ξ, 1 ≤ ξ → ξ < M → ‖dft M f ξ‖ ≤ (1 / 2 : ℝ) * sp := by
    intro ξ hξ1 hξM
    have hd : dft M f ξ = ((1 / 2 : ℝ) : ℂ) * dft M indS ξ * ((1 - ρ ^ (min ξ (M - ξ)) : ℝ) : ℂ) := by
      dsimp only [f]
      have hndvd : ¬ M ∣ ξ := fun h => by have := Nat.le_of_dvd (by omega) h; omega
      rw [dft_add, dft_const hM_pos, if_neg hndvd, zero_add, dft_smul, dft_sub, hdft_Sh ξ hξM]
      push_cast; ring
    rw [hd, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    have h1 : 0 ≤ 1 - ρ ^ (min ξ (M - ξ)) := by linarith [pow_le_one₀ hρ_pos.le hρ_lt1.le (n := min ξ (M - ξ))]
    have h2 : 1 - ρ ^ (min ξ (M - ξ)) ≤ 1 := by linarith [pow_nonneg hρ_pos.le (min ξ (M - ξ))]
    rw [Real.norm_of_nonneg (by norm_num), Real.norm_of_nonneg h1]
    have hi := hnorm_indS_le ξ hξ1 hξM
    nlinarith
  -- Step A: `|Sh x - p / M| ≤ (1 / 3) * (p / M)`
  have hSh_dev : ∀ x, x < M → |Sh x - (p : ℝ) / (M : ℝ)| ≤ (1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ)) := by
    intro x hx
    have hinv := congrArg Complex.re (dft_inversion hM_pos Sh hx)
    simp only [Complex.ofReal_re] at hinv
    have h0 : (dft M Sh 0).re = (p : ℝ) := by rw [hdft_Sh 0 hM_pos, hdft_indS 0]; simp [hS_card]
    have hdev := invDft_re_sub_zero_le hM_pos (dft M Sh) x
    rw [hinv, h0] at hdev
    have hsum_ρ : ∑ ξ ∈ Finset.Ico 1 M, ρ ^ (min ξ (M - ξ)) ≤ 2 * (ρ / (1 - ρ)) := by
      have h1 : Finset.Ico 1 M = Finset.Ico 1 H ∪ Finset.Ico H M := by
        ext ξ; simp only [Finset.mem_Ico, Finset.mem_union]; omega
      have hd1 : Disjoint (Finset.Ico 1 H) (Finset.Ico H M) := by
        rw [Finset.disjoint_left]; intro ξ a b; rw [Finset.mem_Ico] at a b; omega
      have h2 : Finset.Ico H M = insert H (Finset.Ico (H + 1) M) := by
        ext ξ; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [h1, Finset.sum_union hd1, h2, Finset.sum_insert (by simp)]
      have hpart1 : ∑ ξ ∈ Finset.Ico 1 H, ρ ^ (min ξ (M - ξ)) = ∑ k ∈ Finset.Ico 1 H, ρ ^ k :=
        Finset.sum_congr rfl fun ξ hξ => by
          rw [Finset.mem_Ico] at hξ; rw [show min ξ (M - ξ) = ξ by omega]
      have hpart2 : ∑ ξ ∈ Finset.Ico (H + 1) M, ρ ^ (min ξ (M - ξ)) =
          ∑ k ∈ Finset.Ico 1 H, ρ ^ k := by
        refine Finset.sum_nbij (fun ξ => M - ξ) ?_ ?_ ?_ ?_
        · intro ξ hξ; simp only [Finset.mem_Ico] at hξ ⊢; omega
        · intro a ha b hb hab; simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
          dsimp only at hab; omega
        · intro k hk; simp only [Finset.mem_coe, Finset.mem_Ico] at hk
          refine ⟨M - k, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
            by dsimp; omega⟩
        · intro ξ hξ; rw [Finset.mem_Ico] at hξ; rw [show min ξ (M - ξ) = M - ξ by omega]
      have hmid : ρ ^ (min H (M - H)) = ρ ^ H := by rw [show min H (M - H) = H by omega]
      rw [hpart1, hpart2, hmid]
      have haddH : (∑ k ∈ Finset.Ico 1 H, ρ ^ k) + ρ ^ H = ∑ k ∈ Finset.Ico 1 (H + 1), ρ ^ k :=
        (Finset.sum_Ico_succ_top hH_pos (fun k => ρ ^ k)).symm
      have hge0 : 0 ≤ ρ ^ H := pow_nonneg hρ_pos.le H
      have hgeom := sum_geom_Ico_le hρ_pos.le hρ_lt1 (H + 1)
      linarith
    have hsum_dft : ∑ ξ ∈ Finset.Ico 1 M, ‖dft M Sh ξ‖ ≤ sp * (2 * (ρ / (1 - ρ))) := by
      calc ∑ ξ ∈ Finset.Ico 1 M, ‖dft M Sh ξ‖
          ≤ ∑ ξ ∈ Finset.Ico 1 M, sp * ρ ^ (min ξ (M - ξ)) := by
            refine Finset.sum_le_sum fun ξ hξ => ?_
            rw [Finset.mem_Ico] at hξ
            rw [hdft_Sh ξ hξ.2, norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (pow_nonneg hρ_pos.le _)]
            exact mul_le_mul_of_nonneg_right (hnorm_indS_le ξ hξ.1 hξ.2) (pow_nonneg hρ_pos.le _)
        _ = sp * ∑ ξ ∈ Finset.Ico 1 M, ρ ^ (min ξ (M - ξ)) := (Finset.mul_sum ..).symm
        _ ≤ sp * (2 * (ρ / (1 - ρ))) := mul_le_mul_of_nonneg_left hsum_ρ hsp_pos.le
    have hbound2 : sp * (2 * (ρ / (1 - ρ))) ≤ (p : ℝ) / 3 := by
      have h1 : 1 / θ ≤ sp / 6 := by
        dsimp only [θ]; rw [one_div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [Real.pi_gt_three]
      have h2 : ρ / (1 - ρ) ≤ sp / 6 := hρ_div_le.trans h1
      nlinarith [hsp_sq]
    calc |Sh x - (p : ℝ) / (M : ℝ)|
        ≤ (1 / (M : ℝ)) * (sp * (2 * (ρ / (1 - ρ)))) :=
          hdev.trans (mul_le_mul_of_nonneg_left hsum_dft (by positivity))
      _ ≤ (1 / (M : ℝ)) * ((p : ℝ) / 3) := mul_le_mul_of_nonneg_left hbound2 (by positivity)
      _ = (1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ)) := by ring
  have hf_lower : ∀ x, x < M → (1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ)) ≤ f x := by
    intro x hx
    have hdev := (abs_le.mp (hSh_dev x hx)).2
    have hind : 0 ≤ indS x := by dsimp only [indS]; split_ifs <;> positivity
    dsimp only [f]; linarith
  have hf_nonneg : ∀ x, x < M → 0 ≤ f x := fun x hx =>
    (by positivity : (0 : ℝ) ≤ (1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))).trans (hf_lower x hx)
  have hμ_bounds : ∀ x, x < M → 0 ≤ μ x ∧ μ x ≤ 1 / Real.sqrt 3 := by
    intro x hx
    have hgnn : 0 ≤ g x := add_nonneg (gLeft_nonneg (by norm_num) x) (gRight_nonneg (by norm_num) x)
    refine ⟨add_nonneg (hf_nonneg x hx) hgnn, ?_⟩
    have hdev := (abs_le.mp (hSh_dev x hx)).1
    have hind : indS x ≤ 1 := by dsimp only [indS]; split_ifs <;> norm_num
    have hgle : g x ≤ (1 / 100 : ℝ) * ((p : ℝ) / (M : ℝ)) := by
      rw [← mul_div_assoc]
      exact gBump_le hL0_ge1 h4L0_leM (A := (1 / 100 : ℝ)) (p := p) (by norm_num) hx
    have hf_ub : f x ≤ 1 / 2 + (2 / 3 : ℝ) * ((p : ℝ) / (M : ℝ)) := by
      dsimp only [f]; linarith only [hdev, hind]
    have hpM_le : (p : ℝ) / (M : ℝ) ≤ (2 : ℝ) / 10000 := by
      rw [div_le_div_iff₀ hM_posR (by norm_num)]
      nlinarith only [hMR_eq, hpR_ge]
    have hμ_le_num : μ x ≤ (5002 : ℝ) / 10000 := by
      dsimp only [μ]; linarith only [hf_ub, hgle, hpM_le]
    have hnum_lt : (5002 : ℝ) / 10000 ≤ 1 / Real.sqrt 3 := by
      rw [le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      have hsq : ((5002 : ℝ) / 10000 * Real.sqrt 3) ^ 2 ≤ 1 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith only [hsq, Real.sqrt_nonneg 3]
    linarith only [hμ_le_num, hnum_lt]
  -- Step B: Excess mass
  have hmass : (p : ℝ) + (1 / 250 : ℝ) * sp ≤ ∑ x ∈ Finset.range M, μ x := by
    have hsum_g : ∑ x ∈ Finset.range M, g x = 2 * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) := by
      dsimp only [g, gBump]
      rw [Finset.sum_add_distrib, sum_gLeft hM_pos hL0_ge1 (by omega),
        sum_gRight hM_pos hL0_ge1 (by omega)]; ring
    have hsum_μ : ∑ x ∈ Finset.range M, μ x = (p : ℝ) + (1 / 50 : ℝ) * ((p : ℝ) * (L0 : ℝ) / (M : ℝ)) := by
      dsimp only [μ]; rw [Finset.sum_add_distrib, hsum_f, hsum_g]; ring
    rw [hsum_μ]
    have h1 : (p : ℝ) * ((1 / 4 : ℝ) * (p : ℝ) * sp - 1) ≤ (p : ℝ) * (L0 : ℝ) :=
      mul_le_mul_of_nonneg_left hL0_gtR.le hp_pos.le
    have h2 : (p : ℝ) * ((1 / 4 : ℝ) * (p : ℝ) * sp - 1) / (M : ℝ) ≤ (p : ℝ) * (L0 : ℝ) / (M : ℝ) :=
      div_le_div_of_nonneg_right h1 hM_posR.le
    have h3 : (1 / 5 : ℝ) * sp ≤ (p : ℝ) * ((1 / 4 : ℝ) * (p : ℝ) * sp - 1) / (M : ℝ) := by
      rw [le_div_iff₀ hM_posR]; nlinarith only [hMR_eq, hpR_ge, hsp_ge]
    linarith only [h2, h3]
  -- Step E helpers: `g * g` and single cross-term
  have hg_ac_le : ∀ d, 1 ≤ d → d < M →
      ∑ x ∈ Finset.range (M - d), g x * g (x + d) ≤ 1 / (10000 * sp) := by
    intro d _ hdM
    have h1 : ∑ x ∈ Finset.range (M - d), g x * g (x + d) ≤
        ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) * ∑ x ∈ Finset.range M, g x := by
      calc ∑ x ∈ Finset.range (M - d), g x * g (x + d)
          ≤ ∑ x ∈ Finset.range (M - d), g x * ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) := by
            refine Finset.sum_le_sum fun x hx => ?_
            rw [Finset.mem_range] at hx
            exact mul_le_mul_of_nonneg_left (gBump_le hL0_ge1 h4L0_leM (by norm_num) (by omega))
              (add_nonneg (gLeft_nonneg (by norm_num) x) (gRight_nonneg (by norm_num) x))
        _ = ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) * ∑ x ∈ Finset.range (M - d), g x := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) * ∑ x ∈ Finset.range M, g x :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le M d))
                fun x _ _ => add_nonneg (gLeft_nonneg (by norm_num) x) (gRight_nonneg (by norm_num) x))
              (by positivity)
    have hsum_g : ∑ x ∈ Finset.range M, g x = 2 * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) := by
      dsimp only [g, gBump]
      rw [Finset.sum_add_distrib, sum_gLeft hM_pos hL0_ge1 (by omega),
        sum_gRight hM_pos hL0_ge1 (by omega)]; ring
    rw [hsum_g] at h1
    have h2 : ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) *
        (2 * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ))) ≤ 1 / (10000 * sp) := by
      have hL0_mul : (p : ℝ) ^ 2 * (L0 : ℝ) ≤ (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp := by
        have := mul_le_mul_of_nonneg_left hL0_leR (sq_nonneg (p : ℝ))
        linarith only [this]
      have hrew : ((1 / 100 : ℝ) * (p : ℝ) / (M : ℝ)) *
          (2 * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ))) =
          (2 / 10000 : ℝ) * ((p : ℝ) ^ 2 * (L0 : ℝ)) / (M : ℝ) ^ 2 := by ring
      rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
      have hM_ge : (99 / 100 : ℝ) * (p : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hMR_eq, hpR_ge]
      have hM2_ge : (1 / 2 : ℝ) * (p : ℝ) ^ 4 ≤ (M : ℝ) ^ 2 := by nlinarith only [hM_ge, hp_pos]
      have hstep : (2 / 10000 : ℝ) * ((p : ℝ) ^ 2 * (L0 : ℝ)) * (10000 * sp) ≤
          (1 / 2 : ℝ) * (p : ℝ) ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hL0_mul hsp_pos.le
        have hrew2 : (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp * sp = (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp ^ 2 := by ring
        rw [hrew2, hsp_sq] at hm
        linarith only [hm]
      linarith only [hstep, hM2_ge]
    exact h1.trans h2
  have hcross_single : ∀ (b : ℕ → ℝ),
      (∑ x ∈ Finset.range M, b x = (1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) →
      (∑ ξ ∈ Finset.range M, ‖dft M b ξ‖ = (1 / 100 : ℝ) * (p : ℝ)) →
      ∀ d : ℕ,
        cyclicXcorr M f b d ≤ 8 / (1000 * sp) ∧ cyclicXcorr M b f d ≤ 8 / (1000 * sp) := by
    intro b hsum_b hL1_b d
    have hIco_b : ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ ≤ (1 / 100 : ℝ) * (p : ℝ) := by
      rw [← hL1_b]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun ξ hξ => Finset.mem_range.mpr (Finset.mem_Ico.mp hξ).2) (fun _ _ _ => norm_nonneg _)
    have hcommon :
        (p : ℝ) * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) / (M : ℝ) +
          (1 / (M : ℝ)) * ((1 / 2 : ℝ) * sp * ((1 / 100 : ℝ) * (p : ℝ))) ≤
        8 / (1000 * sp) := by
      have ht1 : (p : ℝ) * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) / (M : ℝ) ≤
          26 / (10000 * sp) := by
        have hrew : (p : ℝ) * ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) / (M : ℝ) =
            (1 / 100 : ℝ) * ((p : ℝ) ^ 2 * (L0 : ℝ)) / (M : ℝ) ^ 2 := by ring
        rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
        have hL0_mul : (p : ℝ) ^ 2 * (L0 : ℝ) ≤ (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp := by
          have := mul_le_mul_of_nonneg_left hL0_leR (sq_nonneg (p : ℝ))
          linarith only [this]
        have hM_ge : (999 / 1000 : ℝ) * (p : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hMR_eq, hpR_ge]
        have hM2_ge : (99 / 100 : ℝ) * (p : ℝ) ^ 4 ≤ (M : ℝ) ^ 2 := by nlinarith only [hM_ge, hp_pos]
        have hm := mul_le_mul_of_nonneg_right hL0_mul hsp_pos.le
        have hrew2 : (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp * sp = (1 / 4 : ℝ) * (p : ℝ) ^ 3 * sp ^ 2 := by ring
        rw [hrew2, hsp_sq] at hm
        have hrew3 : (1 / 100 : ℝ) * ((p : ℝ) ^ 2 * (L0 : ℝ)) * (10000 * sp) =
            100 * ((p : ℝ) ^ 2 * (L0 : ℝ) * sp) := by ring
        have hrew4 : (1 / 4 : ℝ) * (p : ℝ) ^ 3 * (p : ℝ) = (1 / 4 : ℝ) * (p : ℝ) ^ 4 := by ring
        rw [hrew4] at hm
        rw [hrew3]
        have hp4_nn : (0 : ℝ) ≤ (p : ℝ) ^ 4 := pow_nonneg hp_pos.le 4
        linarith only [hm, hM2_ge, hp4_nn]
      have ht2 : (1 / (M : ℝ)) * ((1 / 2 : ℝ) * sp * ((1 / 100 : ℝ) * (p : ℝ))) ≤
          51 / (10000 * sp) := by
        have hrew : (1 / (M : ℝ)) * ((1 / 2 : ℝ) * sp * ((1 / 100 : ℝ) * (p : ℝ))) =
            (1 / 200 : ℝ) * ((p : ℝ) * sp) / (M : ℝ) := by ring
        rw [hrew, div_le_div_iff₀ hM_posR (by positivity)]
        have hM_ge : (999 / 1000 : ℝ) * (p : ℝ) ^ 2 ≤ (M : ℝ) := by nlinarith only [hMR_eq, hpR_ge]
        have hrew2 : (1 / 200 : ℝ) * ((p : ℝ) * sp) * (10000 * sp) = 50 * (p : ℝ) * sp ^ 2 := by ring
        rw [hrew2, hsp_sq]
        nlinarith only [hM_ge, hpR_ge]
      have hadd : 26 / (10000 * sp) + 51 / (10000 * sp) ≤ 8 / (1000 * sp) := by
        rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith only [hsp_pos]
      linarith only [ht1, ht2, hadd]
    constructor
    · have hxc := (abs_le.mp (cyclicXcorr_sub_mean_le hM_pos f b d)).2
      rw [hsum_f, hsum_b] at hxc
      have hsum_bd : ∑ ξ ∈ Finset.Ico 1 M, ‖dft M f ξ‖ * ‖dft M b ξ‖ ≤
          (1 / 2 : ℝ) * sp * ((1 / 100 : ℝ) * (p : ℝ)) := by
        calc ∑ ξ ∈ Finset.Ico 1 M, ‖dft M f ξ‖ * ‖dft M b ξ‖
            ≤ ∑ ξ ∈ Finset.Ico 1 M, ((1 / 2 : ℝ) * sp) * ‖dft M b ξ‖ :=
              Finset.sum_le_sum fun ξ hξ => by
                rw [Finset.mem_Ico] at hξ
                exact mul_le_mul_of_nonneg_right (hnorm_f_nz ξ hξ.1 hξ.2) (norm_nonneg _)
          _ = ((1 / 2 : ℝ) * sp) * ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ := (Finset.mul_sum ..).symm
          _ ≤ ((1 / 2 : ℝ) * sp) * ((1 / 100 : ℝ) * (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hIco_b (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hsum_bd (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))
      linarith only [hxc, hmul, hcommon]
    · have hxc := (abs_le.mp (cyclicXcorr_sub_mean_le hM_pos b f d)).2
      rw [hsum_f, hsum_b, mul_comm ((1 / 100 : ℝ) * (p : ℝ) * (L0 : ℝ) / (M : ℝ)) (p : ℝ)] at hxc
      have hsum_bd : ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ * ‖dft M f ξ‖ ≤
          (1 / 2 : ℝ) * sp * ((1 / 100 : ℝ) * (p : ℝ)) := by
        calc ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ * ‖dft M f ξ‖
            ≤ ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ * ((1 / 2 : ℝ) * sp) :=
              Finset.sum_le_sum fun ξ hξ => by
                rw [Finset.mem_Ico] at hξ
                exact mul_le_mul_of_nonneg_left (hnorm_f_nz ξ hξ.1 hξ.2) (norm_nonneg _)
          _ = ((1 / 2 : ℝ) * sp) * ∑ ξ ∈ Finset.Ico 1 M, ‖dft M b ξ‖ := by
              rw [← Finset.sum_mul, mul_comm]
          _ ≤ ((1 / 2 : ℝ) * sp) * ((1 / 100 : ℝ) * (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hIco_b (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hsum_bd (by positivity : (0 : ℝ) ≤ 1 / (M : ℝ))
      linarith only [hxc, hmul, hcommon]
  have hlin_le_cyc : ∀ (a b : ℕ → ℝ) (d : ℕ), d < M →
      (∀ x, x < M → 0 ≤ a x) → (∀ x, x < M → 0 ≤ b x) →
      ∑ x ∈ Finset.range (M - d), a x * b (x + d) ≤ cyclicXcorr M a b d := by
    intro a b d hd ha hb
    unfold cyclicXcorr
    rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le M d)]
    have hleft : ∑ x ∈ Finset.range (M - d), a x * b ((x + d) % M) =
        ∑ x ∈ Finset.range (M - d), a x * b (x + d) :=
      Finset.sum_congr rfl fun x hx => by
        rw [Finset.mem_range] at hx; rw [Nat.mod_eq_of_lt (by omega)]
    have hright : 0 ≤ ∑ x ∈ Finset.Ico (M - d) M, a x * b ((x + d) % M) :=
      Finset.sum_nonneg fun x hx => by
        rw [Finset.mem_Ico] at hx; exact mul_nonneg (ha x hx.2) (hb _ (Nat.mod_lt _ hM_pos))
    linarith
  have hsum_gL := sum_gLeft (A := (1 / 100 : ℝ)) (p := p) hM_pos hL0_ge1 (by omega)
  have hsum_gR := sum_gRight (A := (1 / 100 : ℝ)) (p := p) hM_pos hL0_ge1 (by omega)
  have hL1_gL := sum_norm_dft_gLeft (A := (1 / 100 : ℝ)) (p := p) hM_pos hL0_ge1 (by omega) (by norm_num)
  have hL1_gR := sum_norm_dft_gRight (A := (1 / 100 : ℝ)) (p := p) hM_pos hL0_ge1 (by omega) (by norm_num)
  -- Final linear autocorrelation bound for all `1 ≤ d < M`
  have hac_lin : ∀ d, 1 ≤ d → d < M → ∑ x ∈ Finset.range (M - d), μ x * μ (x + d) ≤ 1 := by
    intro d hd1 hdM
    have hdecomp :
        ∑ x ∈ Finset.range (M - d), μ x * μ (x + d) =
        (∑ x ∈ Finset.range (M - d), f x * f (x + d)) +
        (∑ x ∈ Finset.range (M - d), f x * gL (x + d)) +
        (∑ x ∈ Finset.range (M - d), gL x * f (x + d)) +
        (∑ x ∈ Finset.range (M - d), f x * gR (x + d)) +
        (∑ x ∈ Finset.range (M - d), gR x * f (x + d)) +
        (∑ x ∈ Finset.range (M - d), g x * g (x + d)) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by dsimp only [μ, g, gBump, gL, gR]; ring
    rw [hdecomp, linear_autocorr_eq_cyclic_sub_wrap hdM f]
    have hwrap_lb : (d : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 ≤
        ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) := by
      calc (d : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2
          = ∑ _x ∈ Finset.Ico (M - d) M, ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 := by
            rw [Finset.sum_const, Nat.card_Ico, show M - (M - d) = d by omega, nsmul_eq_mul]
        _ ≤ ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) :=
            Finset.sum_le_sum fun x hx => by
              rw [Finset.mem_Ico] at hx; rw [sq]
              exact mul_le_mul (hf_lower x hx.2) (hf_lower (x + d - M) (by omega))
                (by positivity) (hf_nonneg x hx.2)
    have hfac_cyc := smooth_bump_f_ac_cyc hp10k hM_eq_2H hS_sub hS_card hflat hd1 hdM
    have hgg := hg_ac_le d hd1 hdM
    have hc1 := hcross_single gL hsum_gL hL1_gL d
    have hc2 := hcross_single gR hsum_gR hL1_gR d
    have hfgL_le : ∑ x ∈ Finset.range (M - d), f x * gL (x + d) ≤ 8 / (1000 * sp) :=
      (hlin_le_cyc f gL d hdM hf_nonneg (fun x _ => gLeft_nonneg (by norm_num) x)).trans hc1.1
    have hgLf_le : ∑ x ∈ Finset.range (M - d), gL x * f (x + d) ≤ 8 / (1000 * sp) :=
      (hlin_le_cyc gL f d hdM (fun x _ => gLeft_nonneg (by norm_num) x) hf_nonneg).trans hc1.2
    have hfgR_le : ∑ x ∈ Finset.range (M - d), f x * gR (x + d) ≤ 8 / (1000 * sp) :=
      (hlin_le_cyc f gR d hdM hf_nonneg (fun x _ => gRight_nonneg (by norm_num) x)).trans hc2.1
    have hgRf_le : ∑ x ∈ Finset.range (M - d), gR x * f (x + d) ≤ 8 / (1000 * sp) :=
      (hlin_le_cyc gR f d hdM (fun x _ => gRight_nonneg (by norm_num) x) hf_nonneg).trans hc2.2
    set c : ℝ := Real.cos (2 * Real.pi * (d : ℝ) / (M : ℝ))
    by_cases hd_large : 2 * L0 ≤ d
    · have hfgL_zero : ∑ x ∈ Finset.range (M - d), f x * gL (x + d) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [Finset.mem_range] at hx
          dsimp only [gL]
          rw [gLeft_eq_zero_of_ge hL0_ge1 (by omega) (by omega) (by omega), mul_zero]
      have hgRf_zero : ∑ x ∈ Finset.range (M - d), gR x * f (x + d) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [Finset.mem_range] at hx
          dsimp only [gR]
          rw [gRight_eq_zero_of_le hL0_ge1 (by omega) (by omega), zero_mul]
      have hdip_nn : 0 ≤ (1 / 4 : ℝ) * (p : ℝ) *
          ((2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c) / (M : ℝ)) :=
        mul_nonneg (by positivity)
          (div_nonneg (poissonFactor_dip_pos hρ_pos hρ_lt1 (Real.neg_one_le_cos _) (Real.cos_le_one _)).le
            hM_posR.le)
      have hwrap_ge : 1 / (20 * sp) ≤ (d : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 := by
        have hdR : 2 * (L0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_large
        have h1 : 2 * (L0 : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 ≤
            (d : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_right hdR (sq_nonneg _)
        have h2 : 1 / (20 * sp) ≤ 2 * (L0 : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 := by
          have hrew : 2 * (L0 : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2 =
              2 * (L0 : ℝ) * (p : ℝ) ^ 2 / (9 * (M : ℝ) ^ 2) := by ring
          rw [hrew, div_le_div_iff₀ (by positivity) (by positivity)]
          have hM2_le : (M : ℝ) ^ 2 ≤ (p : ℝ) ^ 4 := by nlinarith only [hMR_eq, hpR_ge]
          have hL0_sp : (1 / 4 : ℝ) * (p : ℝ) ^ 2 - sp ≤ (L0 : ℝ) * sp := by
            have hm := mul_le_mul_of_nonneg_right hL0_gtR.le hsp_pos.le
            have hrew2 : ((1 / 4 : ℝ) * (p : ℝ) * sp - 1) * sp =
                (1 / 4 : ℝ) * (p : ℝ) * sp ^ 2 - sp := by ring
            rw [hrew2, hsp_sq] at hm
            linarith only [hm]
          have hL0_p2 : (1 / 4 : ℝ) * (p : ℝ) ^ 4 - (p : ℝ) ^ 2 * sp ≤
              (L0 : ℝ) * sp * (p : ℝ) ^ 2 := by
            have hm := mul_le_mul_of_nonneg_right hL0_sp (sq_nonneg (p : ℝ))
            linarith only [hm]
          have hsp_le_p : sp ≤ (p : ℝ) := by nlinarith only [hsp_sq, hsp_ge]
          have hp3_le : (p : ℝ) ^ 2 * sp ≤ (1 / 100 : ℝ) * (p : ℝ) ^ 4 := by
            have h1 : (p : ℝ) ^ 2 * sp ≤ (p : ℝ) ^ 3 := by
              have hm := mul_le_mul_of_nonneg_left hsp_le_p (sq_nonneg (p : ℝ))
              have hr : (p : ℝ) ^ 2 * (p : ℝ) = (p : ℝ) ^ 3 := by ring
              linarith only [hm, hr]
            have h2 : (p : ℝ) ^ 3 ≤ (1 / 100 : ℝ) * (p : ℝ) ^ 4 := by
              have hp3_nn : (0 : ℝ) ≤ (p : ℝ) ^ 3 := pow_nonneg hp_pos.le 3
              have hm := mul_le_mul_of_nonneg_left hpR_ge hp3_nn
              have hr : (p : ℝ) ^ 3 * (p : ℝ) = (p : ℝ) ^ 4 := by ring
              linarith only [hm, hr, hp3_nn]
            linarith only [h1, h2]
          have hrew3 : 2 * (L0 : ℝ) * (p : ℝ) ^ 2 * (20 * sp) =
              40 * ((L0 : ℝ) * sp * (p : ℝ) ^ 2) := by ring
          rw [hrew3]
          have hp4_nn : (0 : ℝ) ≤ (p : ℝ) ^ 4 := pow_nonneg hp_pos.le 4
          linarith only [hM2_le, hL0_p2, hp3_le, hp4_nn]
        exact h2.trans h1
      have hnum_cmp :
          1 / (200 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) + 1 / (10000 * sp) ≤
          1 / (20 * sp) := by
        have hL : 1 / (200 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) + 1 / (10000 * sp) =
            211 / (10000 * sp) := by field_simp [hsp_pos.ne']; ring
        have hR : 1 / (20 * sp) = 500 / (10000 * sp) := by field_simp [hsp_pos.ne']; ring
        rw [hL, hR]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
      linarith only [hfac_cyc, hwrap_lb, hwrap_ge, hdip_nn, hfgL_zero, hgLf_le, hfgR_le,
        hgRf_zero, hgg, hnum_cmp]
    · push Not at hd_large
      have hwrap_nn : 0 ≤ ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) :=
        (by positivity : (0 : ℝ) ≤ (d : ℝ) * ((1 / 3 : ℝ) * ((p : ℝ) / (M : ℝ))) ^ 2).trans hwrap_lb
      have hd_ub : (d : ℝ) ≤ (1 / 2 : ℝ) * (p : ℝ) * sp := by
        have hdR : (d : ℝ) ≤ 2 * (L0 : ℝ) := by exact_mod_cast hd_large.le
        linarith only [hdR, hL0_leR]
      have hdip_ge := smooth_bump_poisson_dip_case2 hp10k hd_ub
      have hsavings : (5 / 112 : ℝ) / sp ≤
          (1 / 4 : ℝ) * (p : ℝ) * ((2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c) / (M : ℝ)) := by
        have h1 : (1 / 4 : ℝ) * (p : ℝ) * (((5 / 28 : ℝ) * sp) / (M : ℝ)) ≤
            (1 / 4 : ℝ) * (p : ℝ) * ((2 * poissonFactor ρ c - poissonFactor (ρ ^ 2) c) / (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdip_ge hM_posR.le) (by positivity)
        have h2 : (5 / 112 : ℝ) / sp ≤ (1 / 4 : ℝ) * (p : ℝ) * (((5 / 28 : ℝ) * sp) / (M : ℝ)) := by
          have hrew : (1 / 4 : ℝ) * (p : ℝ) * (((5 / 28 : ℝ) * sp) / (M : ℝ)) =
              (5 / 112 : ℝ) * ((p : ℝ) * sp) / (M : ℝ) := by ring
          rw [hrew, div_le_div_iff₀ hsp_pos hM_posR]
          have hrew2 : (5 / 112 : ℝ) * ((p : ℝ) * sp) * sp = (5 / 112 : ℝ) * (p : ℝ) * sp ^ 2 := by ring
          rw [hrew2, hsp_sq]
          nlinarith only [hMR_eq]
        exact h2.trans h1
      have hnum_cmp :
          1 / (200 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) +
            8 / (1000 * sp) + 1 / (10000 * sp) ≤
          (5 / 112 : ℝ) / sp := by
        have hL :
            1 / (200 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) + 8 / (1000 * sp) +
              8 / (1000 * sp) + 1 / (10000 * sp) =
            (371 / 10000 : ℝ) / sp := by field_simp [hsp_pos.ne']; ring
        rw [hL]
        exact div_le_div_of_nonneg_right (by norm_num) hsp_pos.le
      linarith only [hfac_cyc, hwrap_nn, hsavings, hfgL_le, hgLf_le, hfgR_le, hgRf_le, hgg, hnum_cmp]
  exact ⟨μ, hμ_bounds, hac_lin, hmass⟩

end Erdos030
