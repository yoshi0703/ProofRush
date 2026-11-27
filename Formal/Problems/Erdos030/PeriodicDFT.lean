import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Periodic Discrete Fourier Transform Toolkit on `ℤ / Mℤ`

Self-contained periodic DFT infrastructure matching the convention of
`Erdos030.bose_periodic_fourier_flatness` (`ω = exp(2πi / M)`), providing:
- Primitive `M`-th root of unity algebra and orthogonality;
- `dft`, `invDft`, inversion, Hermitian-symmetry realness, and `L^∞` Fourier bound;
- Cyclic convolution (`dft_cyclicConv`), cyclic shift (`dft_cyclicShift`), pointwise product
  convolution in frequency space (`dft_pointwise_mul`), and cyclic cross-correlation
  (`cyclicXcorr_eq_dft`, `cyclicXcorr_sub_mean_le`);
- Exact linear-vs-cyclic autocorrelation relations;
- Jordan lower bound `4 * min(ξ, M - ξ) / M ≤ ‖ω^ξ - 1‖` and box DFT decay bounds;
- Elementary quadratic tail and geometric sum bounds for smooth-bump and Poisson kernels.
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-- Primitive `M`-th root of unity `ω = exp(2πi / M)`. -/
noncomputable def rootOfUnity (M : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))

/-- Discrete Fourier transform on `Finset.range M` matching `bose_periodic_fourier_flatness`. -/
noncomputable def dft (M : ℕ) (f : ℕ → ℝ) (ξ : ℕ) : ℂ :=
  ∑ x ∈ Finset.range M, (f x : ℂ) * (rootOfUnity M) ^ (ξ * x)

/-- Inverse discrete Fourier transform on `Finset.range M`. -/
noncomputable def invDft (M : ℕ) (F : ℕ → ℂ) (x : ℕ) : ℂ :=
  (1 / (M : ℂ)) *
    ∑ ξ ∈ Finset.range M, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))

/-- Cyclic convolution `(f ⋆_M g)(x) = ∑_{y < M} f(y) g((x + M - y) % M)`. -/
noncomputable def cyclicConv (M : ℕ) (f g : ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ y ∈ Finset.range M, f y * g ((x + M - y) % M)

/-- Cyclic cross-correlation `∑_{x < M} f(x) g((x + d) % M)`. -/
noncomputable def cyclicXcorr (M : ℕ) (f g : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ x ∈ Finset.range M, f x * g ((x + d) % M)

/-- Cyclic shift right by `s` modulo `M`. -/
def cyclicShift (M s : ℕ) (f : ℕ → ℝ) (x : ℕ) : ℝ :=
  f ((x + M - s % M) % M)

/-! ### Part 1: Root of Unity Algebra & Orthogonality -/

lemma rootOfUnity_ne_zero (M : ℕ) : rootOfUnity M ≠ 0 :=
  Complex.exp_ne_zero _

lemma norm_rootOfUnity (M : ℕ) : ‖rootOfUnity M‖ = 1 := by
  unfold rootOfUnity
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I / (M : ℂ) =
      ((2 * Real.pi / (M : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

lemma norm_rootOfUnity_pow (M k : ℕ) : ‖(rootOfUnity M) ^ k‖ = 1 := by
  rw [norm_pow, norm_rootOfUnity, one_pow]

lemma star_rootOfUnity (M : ℕ) : starRingEnd ℂ (rootOfUnity M) = (rootOfUnity M)⁻¹ := by
  unfold rootOfUnity
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

lemma rootOfUnity_pow_eq_one_iff_dvd {M : ℕ} (hM : 0 < M) (k : ℕ) :
    (rootOfUnity M) ^ k = 1 ↔ M ∣ k := by
  unfold rootOfUnity
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  have h2piI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  constructor
  · rintro ⟨n, hn⟩
    have hmul : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        (n : ℂ) * (M : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have := congrArg (· * (M : ℂ)) hn
      have hL : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) * (M : ℂ) =
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by field_simp
      rw [hL] at this
      linear_combination this
    have hkC : (k : ℂ) = (n : ℂ) * (M : ℂ) := mul_right_cancel₀ h2piI hmul
    have hkZ : (k : ℤ) = n * (M : ℤ) := by
      have := congrArg Complex.re hkC
      simp only [Complex.natCast_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.natCast_im, mul_zero, sub_zero] at this
      exact_mod_cast this
    have hn_nonneg : 0 ≤ n := by nlinarith
    refine ⟨n.toNat, ?_⟩
    have : (k : ℤ) = (M : ℤ) * (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hn_nonneg, mul_comm]; exact hkZ
    exact_mod_cast this
  · rintro ⟨q, rfl⟩
    refine ⟨(q : ℤ), ?_⟩
    push_cast
    field_simp

lemma rootOfUnity_pow_M {M : ℕ} (hM : 0 < M) : (rootOfUnity M) ^ M = 1 :=
  (rootOfUnity_pow_eq_one_iff_dvd hM M).mpr (dvd_refl M)

lemma rootOfUnity_pow_mod {M : ℕ} (hM : 0 < M) (n : ℕ) :
    (rootOfUnity M) ^ n = (rootOfUnity M) ^ (n % M) := by
  conv_lhs => rw [← Nat.div_add_mod n M]
  rw [pow_add, pow_mul, rootOfUnity_pow_M hM, one_pow, one_mul]

lemma rootOfUnity_pow_sub_eq_star {M : ℕ} (hM : 0 < M) {ξ : ℕ} (hξ : ξ ≤ M) (a : ℕ) :
    (rootOfUnity M) ^ ((M - ξ) * a) = starRingEnd ℂ ((rootOfUnity M) ^ (ξ * a)) := by
  rw [map_pow, star_rootOfUnity, inv_pow]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, ← add_mul, Nat.sub_add_cancel hξ, pow_mul, rootOfUnity_pow_M hM, one_pow]

lemma rootOfUnity_conj_mul_eq {M : ℕ} (hM : 0 < M) (ξ a b : ℕ) (hb : b ≤ M) :
    (rootOfUnity M) ^ (ξ * a) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * b)) =
      (rootOfUnity M) ^ (ξ * ((a + M - b) % M)) := by
  rw [map_pow, star_rootOfUnity, inv_pow]
  have heq : (rootOfUnity M) ^ (ξ * a) * ((rootOfUnity M) ^ (ξ * b))⁻¹ =
      (rootOfUnity M) ^ (ξ * (a + M - b)) := by
    rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ (rootOfUnity_ne_zero M)), ← pow_add]
    have h1 : ξ * (a + M - b) + ξ * b = ξ * a + M * ξ := by
      have hsub : a + M - b + b = a + M := by omega
      calc ξ * (a + M - b) + ξ * b = ξ * (a + M - b + b) := by ring
        _ = ξ * (a + M) := by rw [hsub]
        _ = ξ * a + M * ξ := by ring
    rw [h1, pow_add, show (rootOfUnity M) ^ (M * ξ) = ((rootOfUnity M) ^ M) ^ ξ by rw [pow_mul],
      rootOfUnity_pow_M hM, one_pow, mul_one]
  rw [heq, rootOfUnity_pow_mod hM (ξ * (a + M - b)),
    rootOfUnity_pow_mod hM (ξ * ((a + M - b) % M))]
  congr 1
  rw [Nat.mul_mod ξ (a + M - b), Nat.mul_mod ξ ((a + M - b) % M), Nat.mod_mod]

lemma sum_rootOfUnity_ortho {M : ℕ} (hM : 0 < M) (k : ℕ) :
    ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * k) = if M ∣ k then (M : ℂ) else 0 := by
  have hpow : ∀ ξ : ℕ, (rootOfUnity M) ^ (ξ * k) = ((rootOfUnity M) ^ k) ^ ξ :=
    fun ξ => by rw [mul_comm, pow_mul]
  rw [Finset.sum_congr rfl fun ξ _ => hpow ξ]
  by_cases hk : M ∣ k
  · simp [hk, (rootOfUnity_pow_eq_one_iff_dvd hM k).mpr hk]
  · simp only [hk, ↓reduceIte]
    have hne : (rootOfUnity M) ^ k ≠ 1 :=
      fun h => hk ((rootOfUnity_pow_eq_one_iff_dvd hM k).mp h)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, rootOfUnity_pow_M hM, one_pow,
      sub_self, zero_div]

/-! ### Part 2: DFT Properties, Inversion, and Hermitian Realness -/

lemma dft_add (M : ℕ) (f g : ℕ → ℝ) (ξ : ℕ) :
    dft M (fun x => f x + g x) ξ = dft M f ξ + dft M g ξ := by
  unfold dft
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast; ring

lemma dft_sub (M : ℕ) (f g : ℕ → ℝ) (ξ : ℕ) :
    dft M (fun x => f x - g x) ξ = dft M f ξ - dft M g ξ := by
  unfold dft
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast; ring

lemma dft_smul (M : ℕ) (c : ℝ) (f : ℕ → ℝ) (ξ : ℕ) :
    dft M (fun x => c * f x) ξ = (c : ℂ) * dft M f ξ := by
  unfold dft
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast; ring

lemma dft_const {M : ℕ} (hM : 0 < M) (c : ℝ) (ξ : ℕ) :
    dft M (fun _ => c) ξ = if M ∣ ξ then (M : ℂ) * (c : ℂ) else 0 := by
  unfold dft
  rw [← Finset.mul_sum]
  have hcomm : ∑ x ∈ Finset.range M, (rootOfUnity M) ^ (ξ * x) =
      ∑ x ∈ Finset.range M, (rootOfUnity M) ^ (x * ξ) :=
    Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hcomm, sum_rootOfUnity_ortho hM ξ]
  split_ifs <;> ring

lemma dft_zero (M : ℕ) (f : ℕ → ℝ) :
    dft M f 0 = ((∑ x ∈ Finset.range M, f x : ℝ) : ℂ) := by
  unfold dft
  simp

lemma dft_indicator {M : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range M) (ξ : ℕ) :
    dft M (fun x => if x ∈ S then (1 : ℝ) else 0) ξ = ∑ a ∈ S, (rootOfUnity M) ^ (ξ * a) := by
  unfold dft
  rw [← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun a ha => ?_
    simp [ha]
  · intro x _ hx
    simp [hx]

lemma dft_mod {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) (ξ : ℕ) :
    dft M f (ξ % M) = dft M f ξ := by
  unfold dft
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [rootOfUnity_pow_mod hM (ξ % M * x), rootOfUnity_pow_mod hM (ξ * x)]
  congr 1
  rw [Nat.mul_mod (ξ % M) x, Nat.mod_mod, ← Nat.mul_mod]

lemma dft_symm {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) {ξ : ℕ} (hξ : ξ ≤ M) :
    dft M f (M - ξ) = starRingEnd ℂ (dft M f ξ) := by
  unfold dft
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_ofReal, rootOfUnity_pow_sub_eq_star hM hξ x]

lemma norm_dft_symm {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) {ξ : ℕ} (hξ : ξ ≤ M) :
    ‖dft M f (M - ξ)‖ = ‖dft M f ξ‖ := by
  rw [dft_symm hM f hξ, Complex.norm_conj]

lemma dft_inversion {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) {x : ℕ} (hx : x < M) :
    invDft M (dft M f) x = (f x : ℂ) := by
  unfold invDft dft
  have hre : ∑ ξ ∈ Finset.range M,
      (∑ y ∈ Finset.range M, (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
        starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x)) =
      ∑ y ∈ Finset.range M, (f y : ℂ) *
        ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((y + M - x) % M)) := by
    have h1 : ∀ ξ ∈ Finset.range M,
        (∑ y ∈ Finset.range M, (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
          starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x)) =
        ∑ y ∈ Finset.range M, (f y : ℂ) * (rootOfUnity M) ^ (ξ * ((y + M - x) % M)) := by
      intro ξ _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_assoc, rootOfUnity_conj_mul_eq hM ξ y x hx.le]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
  rw [hre]
  have hsingle : ∑ y ∈ Finset.range M, (f y : ℂ) *
      ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((y + M - x) % M)) = (f x : ℂ) * (M : ℂ) := by
    rw [Finset.sum_eq_single x]
    · rw [show x + M - x = M by omega, Nat.mod_self, sum_rootOfUnity_ortho hM 0]
      simp
    · intro y hy hyx
      rw [Finset.mem_range] at hy
      rw [sum_rootOfUnity_ortho hM]
      have hndvd : ¬ M ∣ ((y + M - x) % M) := by
        intro hdvd
        have hmod0 : (y + M - x) % M = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hM)
        rcases Nat.dvd_of_mod_eq_zero hmod0 with ⟨q, hq⟩
        have hq1 : q = 1 := by
          by_contra hqne
          rcases lt_or_gt_of_ne hqne with hlt | hgt
          · have : q = 0 := by omega
            subst this; omega
          · have : 2 ≤ q := by omega
            have : 2 * M ≤ M * q := by nlinarith
            omega
        subst hq1; omega
      simp [hndvd]
    · intro hx'; exact False.elim (hx' (Finset.mem_range.mpr hx))
  rw [hsingle]
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp

/-- If `F` is Hermitian-symmetric on `range M`, its inverse DFT is purely real everywhere. -/
lemma invDft_im_zero_of_hermitian {M : ℕ} (hM : 0 < M) {F : ℕ → ℂ}
    (hF0 : (F 0).im = 0)
    (hFsymm : ∀ ξ : ℕ, 1 ≤ ξ → ξ < M → F (M - ξ) = starRingEnd ℂ (F ξ))
    (x : ℕ) :
    (invDft M F x).im = 0 := by
  have hconj : starRingEnd ℂ (invDft M F x) = invDft M F x := by
    unfold invDft
    rw [map_mul, map_div₀, map_one, map_natCast, map_sum]
    congr 1
    rw [← Finset.sum_range_add_sum_Ico _ hM, ← Finset.sum_range_add_sum_Ico _ hM]
    congr 1
    · simp only [Finset.range_one, Finset.sum_singleton, zero_mul, pow_zero, map_one, mul_one]
      exact Complex.conj_eq_iff_im.mpr hF0
    · refine Finset.sum_nbij (fun ξ => M - ξ) ?_ ?_ ?_ ?_
      · intro ξ hξ
        simp only [Finset.mem_coe, Finset.mem_Ico] at hξ ⊢
        omega
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
        dsimp only at hab
        omega
      · intro η hη
        simp only [Finset.mem_coe, Finset.mem_Ico] at hη
        refine ⟨M - η, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by dsimp; omega⟩
      · intro ξ hξ
        rw [Finset.mem_Ico] at hξ
        rw [map_mul, starRingEnd_self_apply, hFsymm ξ hξ.1 hξ.2,
          rootOfUnity_pow_sub_eq_star hM hξ.2.le x, starRingEnd_self_apply]
  exact Complex.conj_eq_iff_im.mp hconj

/-- The DFT of the real part of a Hermitian-symmetric inverse DFT recovers `F` exactly. -/
lemma dft_invDft_re_of_hermitian {M : ℕ} (hM : 0 < M) {F : ℕ → ℂ}
    (hF0 : (F 0).im = 0)
    (hFsymm : ∀ ξ : ℕ, 1 ≤ ξ → ξ < M → F (M - ξ) = starRingEnd ℂ (F ξ))
    {ξ : ℕ} (hξ : ξ < M) :
    dft M (fun x => (invDft M F x).re) ξ = F ξ := by
  unfold dft
  have hcast : ∀ x ∈ Finset.range M, ((invDft M F x).re : ℂ) = invDft M F x := by
    intro x _
    exact Complex.ext (by simp) (by simp [invDft_im_zero_of_hermitian hM hF0 hFsymm x])
  rw [Finset.sum_congr rfl fun x hx => by rw [hcast x hx]]
  unfold invDft
  have hpull :
      ∑ x ∈ Finset.range M,
        (1 / (M : ℂ)) * (∑ η ∈ Finset.range M, F η * starRingEnd ℂ ((rootOfUnity M) ^ (η * x))) *
          (rootOfUnity M) ^ (ξ * x) =
      (1 / (M : ℂ)) * ∑ η ∈ Finset.range M, F η *
        ∑ x ∈ Finset.range M, (rootOfUnity M) ^ (x * ((ξ + M - η) % M)) := by
    have h1 : ∀ x ∈ Finset.range M,
        (1 / (M : ℂ)) * (∑ η ∈ Finset.range M, F η * starRingEnd ℂ ((rootOfUnity M) ^ (η * x))) *
          (rootOfUnity M) ^ (ξ * x) =
        (1 / (M : ℂ)) * ∑ η ∈ Finset.range M,
          F η * (rootOfUnity M) ^ (x * ((ξ + M - η) % M)) := by
      intro x _
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun η hη => ?_
      rw [Finset.mem_range] at hη
      rw [mul_assoc, mul_comm (starRingEnd ℂ _)]
      have hmul : (rootOfUnity M) ^ (ξ * x) * starRingEnd ℂ ((rootOfUnity M) ^ (η * x)) =
          (rootOfUnity M) ^ (x * ((ξ + M - η) % M)) := by
        rw [mul_comm ξ x, mul_comm η x]
        exact rootOfUnity_conj_mul_eq hM x ξ η hη.le
      rw [hmul]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => (Finset.mul_sum (Finset.range M) _ (F η)).symm
  rw [hpull]
  have hsingle :
      ∑ η ∈ Finset.range M, F η * ∑ x ∈ Finset.range M, (rootOfUnity M) ^ (x * ((ξ + M - η) % M)) =
      F ξ * (M : ℂ) := by
    rw [Finset.sum_eq_single ξ]
    · rw [show ξ + M - ξ = M by omega, Nat.mod_self, sum_rootOfUnity_ortho hM 0]
      simp
    · intro η hη hηξ
      rw [Finset.mem_range] at hη
      rw [sum_rootOfUnity_ortho hM]
      have hndvd : ¬ M ∣ ((ξ + M - η) % M) := by
        intro hdvd
        have hmod0 : (ξ + M - η) % M = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hM)
        rcases Nat.dvd_of_mod_eq_zero hmod0 with ⟨q, hq⟩
        have hq1 : q = 1 := by
          by_contra hqne
          rcases lt_or_gt_of_ne hqne with hlt | hgt
          · have : q = 0 := by omega
            subst this; omega
          · have : 2 ≤ q := by omega
            have : 2 * M ≤ M * q := by nlinarith
            omega
        subst hq1; omega
      simp [hndvd]
    · intro hξ'; exact False.elim (hξ' (Finset.mem_range.mpr hξ))
  rw [hsingle]
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp

/-- Elementary `L^∞` Fourier inversion deviation bound:
`|(invDft M F x).re - (F 0).re / M| ≤ (1 / M) * ∑_{1 ≤ ξ < M} ‖F ξ‖`. -/
lemma invDft_re_sub_zero_le {M : ℕ} (hM : 0 < M) (F : ℕ → ℂ) (x : ℕ) :
    |(invDft M F x).re - (F 0).re / (M : ℝ)| ≤
      (1 / (M : ℝ)) * ∑ ξ ∈ Finset.Ico 1 M, ‖F ξ‖ := by
  unfold invDft
  rw [← Finset.sum_range_add_sum_Ico _ hM]
  have h0 : ∑ ξ ∈ Finset.range 1, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x)) = F 0 := by
    simp
  rw [h0, mul_add]
  have hre_div : ((1 / (M : ℂ)) * F 0).re = (F 0).re / (M : ℝ) := by
    have : (1 / (M : ℂ)) * F 0 = ((1 / (M : ℝ) : ℝ) : ℂ) * F 0 := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]; ring
  rw [Complex.add_re, hre_div, add_sub_cancel_left]
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hmul_re : ((1 / (M : ℂ)) *
      ∑ ξ ∈ Finset.Ico 1 M, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))).re =
      (1 / (M : ℝ)) *
        (∑ ξ ∈ Finset.Ico 1 M, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))).re := by
    have : (1 / (M : ℂ)) = ((1 / (M : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hmul_re, abs_mul, abs_of_pos (div_pos one_pos hMpos)]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one hMpos.le)
  calc |(∑ ξ ∈ Finset.Ico 1 M, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))).re|
      ≤ ‖∑ ξ ∈ Finset.Ico 1 M, F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ ξ ∈ Finset.Ico 1 M, ‖F ξ * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * x))‖ :=
        norm_sum_le _ _
    _ = ∑ ξ ∈ Finset.Ico 1 M, ‖F ξ‖ := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [norm_mul, Complex.norm_conj, norm_rootOfUnity_pow, mul_one]

/-! ### Part 3: Cyclic Convolution, Shift, Product, and Cross-Correlation -/

lemma dft_cyclicConv {M : ℕ} (hM : 0 < M) (f g : ℕ → ℝ) (ξ : ℕ) :
    dft M (cyclicConv M f g) ξ = dft M f ξ * dft M g ξ := by
  unfold dft cyclicConv
  have hstep :
      ∑ x ∈ Finset.range M,
        ((∑ y ∈ Finset.range M, f y * g ((x + M - y) % M) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * x) =
      ∑ y ∈ Finset.range M, ((f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
        ∑ x ∈ Finset.range M,
          (g ((x + M - y) % M) : ℂ) * (rootOfUnity M) ^ (ξ * ((x + M - y) % M)) := by
    have h1 : ∀ x ∈ Finset.range M,
        ((∑ y ∈ Finset.range M, f y * g ((x + M - y) % M) : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * x) =
        ∑ y ∈ Finset.range M,
          ((f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
            ((g ((x + M - y) % M) : ℂ) * (rootOfUnity M) ^ (ξ * ((x + M - y) % M))) := by
      intro x _
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Finset.mem_range] at hy
      have hpow : (rootOfUnity M) ^ (ξ * x) =
          (rootOfUnity M) ^ (ξ * y) * (rootOfUnity M) ^ (ξ * ((x + M - y) % M)) := by
        rw [← pow_add, ← mul_add, rootOfUnity_pow_mod hM (ξ * x),
          rootOfUnity_pow_mod hM (ξ * (y + (x + M - y) % M))]
        congr 1
        rw [Nat.mul_mod ξ (y + (x + M - y) % M), Nat.mul_mod ξ x]
        congr 1
        have hadd : (y + (x + M - y) % M) % M = (y + (x + M - y)) % M := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [hadd, show y + (x + M - y) = x + M by omega, Nat.add_mod_right]
      rw [hpow]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
  rw [hstep, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_range] at hy
  congr 1
  refine Finset.sum_nbij (fun x => (x + M - y) % M) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hM))
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    dsimp only at hab
    have h1 : (a + M - y) % M = (if y ≤ a then a - y else a + M - y) := by
      split_ifs with hya
      · rw [show a + M - y = (a - y) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    have h2 : (b + M - y) % M = (if y ≤ b then b - y else b + M - y) := by
      split_ifs with hyb
      · rw [show b + M - y = (b - y) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2] at hab
    split_ifs at hab <;> omega
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_range] at hz
    refine ⟨(z + y) % M, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hM)), ?_⟩
    dsimp only
    by_cases hzy : z + y < M
    · rw [Nat.mod_eq_of_lt hzy, show z + y + M - y = z + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hz]
    · have hmod : (z + y) % M = z + y - M := by
        have hlt : z + y - M < M := by omega
        have hadd : z + y = (z + y - M) + M := by omega
        conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rw [hmod, show z + y - M + M - y = z by omega, Nat.mod_eq_of_lt hz]
  · intro x _; rfl

lemma dft_cyclicShift {M : ℕ} (hM : 0 < M) (s : ℕ) (f : ℕ → ℝ) (ξ : ℕ) :
    dft M (cyclicShift M s f) ξ = (rootOfUnity M) ^ (ξ * s) * dft M f ξ := by
  unfold dft cyclicShift
  rw [Finset.mul_sum]
  set r := s % M
  have hr : r < M := Nat.mod_lt s hM
  refine Finset.sum_nbij (fun x => (x + M - r) % M) ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hM))
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_range] at ha hb
    dsimp only at hab
    have h1 : (a + M - r) % M = if r ≤ a then a - r else a + M - r := by
      split_ifs with hra
      · rw [show a + M - r = (a - r) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    have h2 : (b + M - r) % M = if r ≤ b then b - r else b + M - r := by
      split_ifs with hrb
      · rw [show b + M - r = (b - r) + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [h1, h2] at hab
    split_ifs at hab <;> omega
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_range] at hz
    refine ⟨(z + r) % M, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hM)), ?_⟩
    dsimp only
    by_cases hzr : z + r < M
    · rw [Nat.mod_eq_of_lt hzr, show z + r + M - r = z + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hz]
    · have hmod : (z + r) % M = z + r - M := by
        have hlt : z + r - M < M := by omega
        have hadd : z + r = (z + r - M) + M := by omega
        conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rw [hmod, show z + r - M + M - r = z by omega, Nat.mod_eq_of_lt hz]
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_range] at hx
    have hpow : (rootOfUnity M) ^ (ξ * x) =
        (rootOfUnity M) ^ (ξ * s) * (rootOfUnity M) ^ (ξ * ((x + M - r) % M)) := by
      rw [← pow_add, ← mul_add, rootOfUnity_pow_mod hM (ξ * x),
        rootOfUnity_pow_mod hM (ξ * (s + (x + M - r) % M))]
      congr 1
      rw [Nat.mul_mod ξ (s + (x + M - r) % M), Nat.mul_mod ξ x]
      congr 1
      have hadd : (s + (x + M - r) % M) % M = (r + (x + M - r)) % M := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mod s, Nat.add_mod r]
        simp [r]
      rw [hadd, show r + (x + M - r) = x + M by omega, Nat.add_mod_right]
    rw [hpow]; ring

lemma norm_dft_cyclicShift {M : ℕ} (hM : 0 < M) (s : ℕ) (f : ℕ → ℝ) (ξ : ℕ) :
    ‖dft M (cyclicShift M s f) ξ‖ = ‖dft M f ξ‖ := by
  rw [dft_cyclicShift hM, norm_mul, norm_rootOfUnity_pow, one_mul]

/-- Cyclic cross-correlation expressed via DFT. -/
lemma cyclicXcorr_eq_dft {M : ℕ} (hM : 0 < M) (f g : ℕ → ℝ) (d : ℕ) :
    cyclicXcorr M f g d =
      (1 / (M : ℝ)) *
        (∑ ξ ∈ Finset.range M,
          dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)).re := by
  have hsumC :
      ∑ ξ ∈ Finset.range M,
        dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d) =
      (M : ℂ) * ((cyclicXcorr M f g d : ℝ) : ℂ) := by
    unfold dft cyclicXcorr
    have hexp : ∀ ξ ∈ Finset.range M,
        (∑ x ∈ Finset.range M, (f x : ℂ) * (rootOfUnity M) ^ (ξ * x)) *
          starRingEnd ℂ (∑ y ∈ Finset.range M, (g y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
          (rootOfUnity M) ^ (ξ * d) =
        ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
          ((f x : ℂ) * (g y : ℂ)) * (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) := by
      intro ξ _
      rw [map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Finset.mem_range] at hy
      rw [map_mul, Complex.conj_ofReal]
      have hpow : (rootOfUnity M) ^ (ξ * x) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * y)) *
          (rootOfUnity M) ^ (ξ * d) =
          (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) := by
        rw [mul_right_comm, ← pow_add, ← mul_add]
        exact rootOfUnity_conj_mul_eq hM ξ (x + d) y hy.le
      calc (f x : ℂ) * (rootOfUnity M) ^ (ξ * x) *
            ((g y : ℂ) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * y))) * (rootOfUnity M) ^ (ξ * d)
          = (f x : ℂ) * (g y : ℂ) *
              ((rootOfUnity M) ^ (ξ * x) * starRingEnd ℂ ((rootOfUnity M) ^ (ξ * y)) *
                (rootOfUnity M) ^ (ξ * d)) := by ring
        _ = ((f x : ℂ) * (g y : ℂ)) * (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) := by
            rw [hpow]
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    have hcomm : ∀ x ∈ Finset.range M,
        ∑ ξ ∈ Finset.range M, ∑ y ∈ Finset.range M,
          ((f x : ℂ) * (g y : ℂ)) * (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) =
        ∑ y ∈ Finset.range M, ((f x : ℂ) * (g y : ℂ)) *
          ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) := by
      intro x _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
    rw [Finset.sum_congr rfl hcomm]
    have hinner : ∀ x ∈ Finset.range M,
        ∑ y ∈ Finset.range M, ((f x : ℂ) * (g y : ℂ)) *
          ∑ ξ ∈ Finset.range M, (rootOfUnity M) ^ (ξ * ((x + d + M - y) % M)) =
        (M : ℂ) * ((f x : ℂ) * (g ((x + d) % M) : ℂ)) := by
      intro x _
      rw [Finset.sum_eq_single ((x + d) % M)]
      · have hmod0 : (x + d + M - (x + d) % M) % M = 0 := by
          have hdm := Nat.div_add_mod (x + d) M
          have hlt := Nat.mod_lt (x + d) hM
          have hsub : x + d + M - (x + d) % M = M * ((x + d) / M) + M := by omega
          rw [hsub, Nat.add_mod_right, Nat.mul_mod_right]
        rw [hmod0, sum_rootOfUnity_ortho hM 0]
        simp [mul_comm]
      · intro y hy hyne
        rw [Finset.mem_range] at hy
        rw [sum_rootOfUnity_ortho hM]
        have hndvd : ¬ M ∣ ((x + d + M - y) % M) := by
          intro hdvd
          have hmod0 : (x + d + M - y) % M = 0 :=
            Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hM)
          have h1 : x + d + M = (x + d + M - y) + y := by omega
          have h2 := congrArg (· % M) h1
          rw [Nat.add_mod_right] at h2
          conv_rhs at h2 => rw [Nat.add_mod, hmod0, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hy]
          exact hyne h2.symm
        simp [hndvd]
      · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.mod_lt _ hM)))
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
    congr 1
    push_cast
    rfl
  rw [hsumC]
  have hre : ((M : ℂ) * ((cyclicXcorr M f g d : ℝ) : ℂ)).re = (M : ℝ) * cyclicXcorr M f g d := by
    simp
  rw [hre]
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp

/-- Triangle-inequality bound for cyclic cross-correlation minus the DC mean term. -/
lemma cyclicXcorr_sub_mean_le {M : ℕ} (hM : 0 < M) (f g : ℕ → ℝ) (d : ℕ) :
    |cyclicXcorr M f g d -
      (∑ x ∈ Finset.range M, f x) * (∑ x ∈ Finset.range M, g x) / (M : ℝ)| ≤
      (1 / (M : ℝ)) * ∑ ξ ∈ Finset.Ico 1 M, ‖dft M f ξ‖ * ‖dft M g ξ‖ := by
  rw [cyclicXcorr_eq_dft hM, ← Finset.sum_range_add_sum_Ico _ hM]
  have h0 :
      (∑ ξ ∈ Finset.range 1,
        dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)).re =
      (∑ x ∈ Finset.range M, f x) * (∑ x ∈ Finset.range M, g x) := by
    simp [dft_zero]
  rw [Complex.add_re, h0, mul_add]
  have hcancel :
      (1 / (M : ℝ)) * ((∑ x ∈ Finset.range M, f x) * (∑ x ∈ Finset.range M, g x)) +
      (1 / (M : ℝ)) * (∑ ξ ∈ Finset.Ico 1 M,
        dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)).re -
      (∑ x ∈ Finset.range M, f x) * (∑ x ∈ Finset.range M, g x) / (M : ℝ) =
      (1 / (M : ℝ)) * (∑ ξ ∈ Finset.Ico 1 M,
        dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)).re := by ring
  rw [hcancel]
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  rw [abs_mul, abs_of_pos (div_pos one_pos hMpos)]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one hMpos.le)
  calc |(∑ ξ ∈ Finset.Ico 1 M,
          dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)).re|
      ≤ ‖∑ ξ ∈ Finset.Ico 1 M,
          dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ ξ ∈ Finset.Ico 1 M,
          ‖dft M f ξ * starRingEnd ℂ (dft M g ξ) * (rootOfUnity M) ^ (ξ * d)‖ :=
        norm_sum_le _ _
    _ = ∑ ξ ∈ Finset.Ico 1 M, ‖dft M f ξ‖ * ‖dft M g ξ‖ := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, norm_rootOfUnity_pow, mul_one]

/-- Exact relation between linear and cyclic autocorrelation: linear = cyclic - wrap-around. -/
lemma linear_autocorr_eq_cyclic_sub_wrap {M d : ℕ} (hd : d < M) (f : ℕ → ℝ) :
    ∑ x ∈ Finset.range (M - d), f x * f (x + d) =
      cyclicXcorr M f f d - ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) := by
  unfold cyclicXcorr
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le M d)]
  have hleft : ∑ x ∈ Finset.range (M - d), f x * f ((x + d) % M) =
      ∑ x ∈ Finset.range (M - d), f x * f (x + d) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    rw [Nat.mod_eq_of_lt (by omega)]
  have hright : ∑ x ∈ Finset.Ico (M - d) M, f x * f ((x + d) % M) =
      ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    have hlt : x + d - M < M := by omega
    have hadd : x + d = (x + d - M) + M := by omega
    conv_lhs => rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  rw [hleft, hright]; ring

/-- For nonnegative functions on `range M`, linear autocorrelation is bounded by cyclic autocorrelation. -/
lemma linear_autocorr_le_cyclic {M d : ℕ} (hd : d < M) {f : ℕ → ℝ}
    (hf : ∀ x, x < M → 0 ≤ f x) :
    ∑ x ∈ Finset.range (M - d), f x * f (x + d) ≤ cyclicXcorr M f f d := by
  rw [linear_autocorr_eq_cyclic_sub_wrap hd]
  have hwrap : 0 ≤ ∑ x ∈ Finset.Ico (M - d) M, f x * f (x + d - M) := by
    refine Finset.sum_nonneg fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    exact mul_nonneg (hf x hx.2) (hf (x + d - M) (by omega))
  linarith

/-- DFT of a pointwise product equals `(1 / M)` times the cyclic convolution of DFTs. -/
lemma dft_pointwise_mul {M : ℕ} (hM : 0 < M) (w f : ℕ → ℝ) (ξ : ℕ) :
    dft M (fun x => w x * f x) ξ =
      (1 / (M : ℂ)) * ∑ η ∈ Finset.range M, dft M w η * dft M f ((ξ + M - η) % M) := by
  unfold dft
  have hexp :
      ∑ η ∈ Finset.range M,
        (∑ x ∈ Finset.range M, (w x : ℂ) * (rootOfUnity M) ^ (η * x)) *
          (∑ y ∈ Finset.range M, (f y : ℂ) * (rootOfUnity M) ^ (((ξ + M - η) % M) * y)) =
      ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
        ((w x : ℂ) * (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
          ∑ η ∈ Finset.range M, (rootOfUnity M) ^ (η * ((x + M - y) % M)) := by
    have h1 : ∀ η ∈ Finset.range M,
        (∑ x ∈ Finset.range M, (w x : ℂ) * (rootOfUnity M) ^ (η * x)) *
          (∑ y ∈ Finset.range M, (f y : ℂ) * (rootOfUnity M) ^ (((ξ + M - η) % M) * y)) =
        ∑ x ∈ Finset.range M, ∑ y ∈ Finset.range M,
          ((w x : ℂ) * (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
            (rootOfUnity M) ^ (η * ((x + M - y) % M)) := by
      intro η hη
      rw [Finset.mem_range] at hη
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Finset.mem_range] at hy
      have hpow : (rootOfUnity M) ^ (η * x) * (rootOfUnity M) ^ (((ξ + M - η) % M) * y) =
          (rootOfUnity M) ^ (ξ * y) * (rootOfUnity M) ^ (η * ((x + M - y) % M)) := by
        rw [← pow_add, ← pow_add, rootOfUnity_pow_mod hM, rootOfUnity_pow_mod hM (ξ * y + _)]
        congr 1
        have hLHS : (η * x + (ξ + M - η) % M * y) % M = (η * x + (ξ + M - η) * y) % M := by
          rw [Nat.add_mod, Nat.mul_mod ((ξ + M - η) % M) y, Nat.mod_mod, ← Nat.mul_mod,
            ← Nat.add_mod]
        have hRHS : (ξ * y + η * ((x + M - y) % M)) % M = (ξ * y + η * (x + M - y)) % M := by
          rw [Nat.add_mod, Nat.mul_mod η ((x + M - y) % M), Nat.mod_mod, ← Nat.mul_mod,
            ← Nat.add_mod]
        rw [hLHS, hRHS]
        have heq_nat : η * x + (ξ + M - η) * y + M * (η * 1) =
            ξ * y + η * (x + M - y) + M * y := by
          zify [show η ≤ ξ + M by omega, show y ≤ x + M by omega]
          ring
        have hmod := congrArg (· % M) heq_nat
        simpa [Nat.add_mul_mod_self_left] using hmod
      calc (w x : ℂ) * (rootOfUnity M) ^ (η * x) *
            ((f y : ℂ) * (rootOfUnity M) ^ (((ξ + M - η) % M) * y))
          = (w x : ℂ) * (f y : ℂ) *
              ((rootOfUnity M) ^ (η * x) * (rootOfUnity M) ^ (((ξ + M - η) % M) * y)) := by ring
        _ = (w x : ℂ) * (f y : ℂ) *
              ((rootOfUnity M) ^ (ξ * y) * (rootOfUnity M) ^ (η * ((x + M - y) % M))) := by
            rw [hpow]
        _ = ((w x : ℂ) * (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
              (rootOfUnity M) ^ (η * ((x + M - y) % M)) := by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => (Finset.mul_sum ..).symm
  rw [hexp]
  have hinner : ∀ x ∈ Finset.range M,
      ∑ y ∈ Finset.range M,
        ((w x : ℂ) * (f y : ℂ) * (rootOfUnity M) ^ (ξ * y)) *
          ∑ η ∈ Finset.range M, (rootOfUnity M) ^ (η * ((x + M - y) % M)) =
      (M : ℂ) * (((w x * f x : ℝ) : ℂ) * (rootOfUnity M) ^ (ξ * x)) := by
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Finset.sum_eq_single x]
    · rw [show x + M - x = M by omega, Nat.mod_self, sum_rootOfUnity_ortho hM 0]
      simp; ring
    · intro y hy hyx
      rw [Finset.mem_range] at hy
      rw [sum_rootOfUnity_ortho hM]
      have hndvd : ¬ M ∣ ((x + M - y) % M) := by
        intro hdvd
        have hmod0 : (x + M - y) % M = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hM)
        rcases Nat.dvd_of_mod_eq_zero hmod0 with ⟨q, hq⟩
        have hq1 : q = 1 := by
          by_contra hqne
          rcases lt_or_gt_of_ne hqne with hlt | hgt
          · have : q = 0 := by omega
            subst this; omega
          · have : 2 ≤ q := by omega
            have : 2 * M ≤ M * q := by nlinarith
            omega
        subst hq1; omega
      simp [hndvd]
    · intro hx'; exact False.elim (hx' (Finset.mem_range.mpr hx))
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  field_simp

/-! ### Part 4: Jordan Lower Bound, Box DFT Decay, and Analytic Sum Bounds -/

/-- Jordan-type lower bound on the chord length `‖ω^ξ - 1‖` for `1 ≤ ξ < M`:
`4 * min(ξ, M - ξ) / M ≤ ‖(rootOfUnity M) ^ ξ - 1‖`. -/
lemma norm_rootOfUnity_sub_one_ge {M ξ : ℕ} (hM : 0 < M) (hξ1 : 1 ≤ ξ) (hξM : ξ < M) :
    4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ) ≤ ‖(rootOfUnity M) ^ ξ - 1‖ := by
  set k : ℕ := min ξ (M - ξ)
  have hk_norm : ‖(rootOfUnity M) ^ ξ - 1‖ = ‖(rootOfUnity M) ^ k - 1‖ := by
    by_cases hle : ξ ≤ M - ξ
    · have hk : k = ξ := min_eq_left hle
      rw [hk]
    · have hk : k = M - ξ := min_eq_right (by omega)
      rw [hk]
      have hconj : (rootOfUnity M) ^ (M - ξ) - 1 = starRingEnd ℂ ((rootOfUnity M) ^ ξ - 1) := by
        rw [map_sub, map_one, ← mul_one (M - ξ), rootOfUnity_pow_sub_eq_star hM hξM.le 1, mul_one]
      rw [hconj, Complex.norm_conj]
  rw [hk_norm]
  have hk_le : 2 * k ≤ M := by dsimp only [k]; omega
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (M : ℝ)
  have hωk : (rootOfUnity M) ^ k = Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold rootOfUnity
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp only [θ]
    push_cast; ring
  rw [hωk, Complex.exp_mul_I]
  have hnorm_eq : ‖Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I - 1‖ =
      2 * Real.sin (θ / 2) := by
    have hre : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I - 1).re =
        Real.cos θ - 1 := by
      simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have him : (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I - 1).im =
        Real.sin θ := by
      simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hsq : ‖Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I - 1‖ ^ 2 =
        (2 * Real.sin (θ / 2)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
      have hcos2 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
        have h := Real.cos_two_mul' (θ / 2)
        have hsc := Real.sin_sq_add_cos_sq (θ / 2)
        rw [show 2 * (θ / 2) = θ by ring] at h
        linarith
      have hsc2 := Real.sin_sq_add_cos_sq θ
      nlinarith
    have hθ_nn : 0 ≤ θ / 2 := by dsimp only [θ]; positivity
    have hθ_le : θ / 2 ≤ Real.pi / 2 := by
      dsimp only [θ]
      have h2kR : (2 : ℝ) * (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk_le
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
      have h1 : 2 * Real.pi * (k : ℝ) / (M : ℝ) ≤ Real.pi := by
        rw [div_le_iff₀ hMpos]
        nlinarith [Real.pi_pos]
      linarith
    have hsin_nn : 0 ≤ 2 * Real.sin (θ / 2) :=
      mul_nonneg (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi hθ_nn (by linarith [Real.pi_pos]))
    nlinarith [norm_nonneg (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I - 1)]
  rw [hnorm_eq]
  have hθ_nn : 0 ≤ θ / 2 := by dsimp only [θ]; positivity
  have hθ_le : θ / 2 ≤ Real.pi / 2 := by
    dsimp only [θ]
    have h2kR : (2 : ℝ) * (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk_le
    have h1 : 2 * Real.pi * (k : ℝ) / (M : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hMpos]; nlinarith [Real.pi_pos]
    linarith
  have hjordan := Real.mul_le_sin hθ_nn hθ_le
  have hsimp : 2 * (2 / Real.pi * (θ / 2)) = 4 * (k : ℝ) / (M : ℝ) := by
    dsimp only [θ]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  linarith

/-- Box indicator DFT bounds: for `1 ≤ K ≤ M` and `1 ≤ ξ < M`,
`‖dft M (box K) ξ‖ ≤ K` and `‖dft M (box K) ξ‖ ≤ M / (2 * min(ξ, M - ξ))`. -/
lemma norm_dft_box_le {M K ξ : ℕ} (hM : 0 < M) (hKM : K ≤ M) (hξ1 : 1 ≤ ξ) (hξM : ξ < M) :
    ‖dft M (fun x => if x < K then (1 : ℝ) else 0) ξ‖ ≤ (K : ℝ) ∧
    ‖dft M (fun x => if x < K then (1 : ℝ) else 0) ξ‖ ≤
      (M : ℝ) / (2 * ((min ξ (M - ξ) : ℕ) : ℝ)) := by
  have hsum : dft M (fun x => if x < K then (1 : ℝ) else 0) ξ =
      ∑ x ∈ Finset.range K, ((rootOfUnity M) ^ ξ) ^ x := by
    unfold dft
    rw [← Finset.sum_subset (Finset.range_mono hKM)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      simp [hx, pow_mul]
    · intro x _ hx
      rw [Finset.mem_range] at hx
      simp [hx]
  rw [hsum]
  constructor
  · calc ‖∑ x ∈ Finset.range K, ((rootOfUnity M) ^ ξ) ^ x‖
        ≤ ∑ x ∈ Finset.range K, ‖((rootOfUnity M) ^ ξ) ^ x‖ := norm_sum_le _ _
      _ = ∑ x ∈ Finset.range K, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_pow, norm_rootOfUnity_pow, one_pow]
      _ = (K : ℝ) := by simp
  · have hne : (rootOfUnity M) ^ ξ ≠ 1 := by
      intro h1
      have hdvd := (rootOfUnity_pow_eq_one_iff_dvd hM ξ).mp h1
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [geom_sum_eq hne, norm_div]
    have hnum : ‖((rootOfUnity M) ^ ξ) ^ K - 1‖ ≤ 2 := by
      calc ‖((rootOfUnity M) ^ ξ) ^ K - 1‖
          ≤ ‖((rootOfUnity M) ^ ξ) ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, norm_rootOfUnity_pow, one_pow, norm_one]; norm_num
    have hden_ge := norm_rootOfUnity_sub_one_ge hM hξ1 hξM
    have hk_pos : (0 : ℝ) < ((min ξ (M - ξ) : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < min ξ (M - ξ) by omega)
    have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hlb_pos : (0 : ℝ) < 4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ) := by positivity
    have hdiv_le : ‖((rootOfUnity M) ^ ξ) ^ K - 1‖ / ‖(rootOfUnity M) ^ ξ - 1‖ ≤
        2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) := by
      calc ‖((rootOfUnity M) ^ ξ) ^ K - 1‖ / ‖(rootOfUnity M) ^ ξ - 1‖
          ≤ 2 / ‖(rootOfUnity M) ^ ξ - 1‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ ≤ 2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) :=
            div_le_div_of_nonneg_left (by norm_num) hlb_pos hden_ge
    have hsimp : 2 / (4 * ((min ξ (M - ξ) : ℕ) : ℝ) / (M : ℝ)) =
        (M : ℝ) / (2 * ((min ξ (M - ξ) : ℕ) : ℝ)) := by
      field_simp; ring
    linarith

/-- Elementary quadratic tail bound: for `1 ≤ K`, `∑_{k=K}^{N-1} 1 / k^2 ≤ 2 / K`. -/
lemma sum_inv_sq_Ico_le {K N : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Ico K N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / (K : ℝ) := by
  by_cases hKN : N ≤ K
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    positivity
  push Not at hKN
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  -- Split off `k = K` and telescope `1 / k^2 ≤ 1 / (k - 1) - 1 / k` for `k ≥ K + 1`
  have hsplit : Finset.Ico K N = insert K (Finset.Ico (K + 1) N) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have htail : ∑ k ∈ Finset.Ico (K + 1) N, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
    have htele : ∀ n : ℕ, K < n →
        ∑ k ∈ Finset.Ico (K + 1) n, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
        1 / (K : ℝ) - 1 / ((n - 1 : ℕ) : ℝ) := by
      intro n
      induction n with
      | zero => intro h; omega
      | succ m ih =>
        intro hm1
        by_cases hm : m ≤ K
        · have : m = K := by omega
          subst this
          simp
        · push Not at hm
          rw [Finset.sum_Ico_succ_top (by omega), ih (by omega)]
          have h1 : m + 1 - 1 = m := by omega
          rw [h1]
          ring
    have hteleN := htele N hKN
    have hle : ∑ k ∈ Finset.Ico (K + 1) N, (1 : ℝ) / (k : ℝ) ^ 2 ≤
        ∑ k ∈ Finset.Ico (K + 1) N, (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
        linarith
      rw [hkm1, div_sub_div _ _ hkm1_pos.ne' (by linarith)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hN1_nn : (0 : ℝ) ≤ 1 / ((N - 1 : ℕ) : ℝ) := by positivity
    linarith
  have hKsq : (1 : ℝ) / (K : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hKpos]
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith
  have htwo : 1 / (K : ℝ) + 1 / (K : ℝ) = 2 / (K : ℝ) := by ring
  linarith

/-- Elementary geometric tail bound: for `0 ≤ ρ < 1`, `∑_{1 ≤ k < N} ρ^k ≤ ρ / (1 - ρ)`. -/
lemma sum_geom_Ico_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (N : ℕ) :
    ∑ k ∈ Finset.Ico 1 N, ρ ^ k ≤ ρ / (1 - ρ) := by
  by_cases hN : N ≤ 1
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact div_nonneg hρ0 (by linarith)
  push Not at hN
  have hshift : ∑ k ∈ Finset.Ico 1 N, ρ ^ k = ρ * ∑ j ∈ Finset.range (N - 1), ρ ^ j := by
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
  rw [hshift, geom_sum_eq (ne_of_lt hρ1)]
  have h1m : 0 < 1 - ρ := by linarith
  have hpow_nn : 0 ≤ ρ ^ (N - 1) := pow_nonneg hρ0 _
  have hgeom_le : (ρ ^ (N - 1) - 1) / (ρ - 1) ≤ 1 / (1 - ρ) := by
    have hne1 : ρ - 1 ≠ 0 := by linarith
    have hne2 : 1 - ρ ≠ 0 := by linarith
    have heq : (ρ ^ (N - 1) - 1) / (ρ - 1) = (1 - ρ ^ (N - 1)) / (1 - ρ) := by
      field_simp [hne1, hne2]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by linarith) h1m.le
  calc ρ * ((ρ ^ (N - 1) - 1) / (ρ - 1))
      ≤ ρ * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left hgeom_le hρ0
    _ = ρ / (1 - ρ) := by ring

/-- Bernoulli-type inequality: `1 - ρ^k ≤ k * (1 - ρ)` for `0 ≤ ρ ≤ 1`. -/
lemma one_sub_pow_le_mul {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (k : ℕ) :
    1 - ρ ^ k ≤ (k : ℝ) * (1 - ρ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    have hpow_le : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρ1
    nlinarith

/-- Exponential inequality: `1 - exp(-t) ≤ t` for all `t : ℝ`. -/
lemma one_sub_exp_neg_le (t : ℝ) : 1 - Real.exp (-t) ≤ t := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- Parseval identity on `Finset.range M`:
`∑_{ξ < M} ‖dft M f ξ‖^2 = M * ∑_{x < M} (f x)^2`. -/
lemma dft_parseval {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) :
    ∑ ξ ∈ Finset.range M, ‖dft M f ξ‖ ^ 2 = (M : ℝ) * ∑ x ∈ Finset.range M, (f x) ^ 2 := by
  have h0 := cyclicXcorr_eq_dft hM f f 0
  have hlhs : cyclicXcorr M f f 0 = ∑ x ∈ Finset.range M, (f x) ^ 2 := by
    unfold cyclicXcorr
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    rw [add_zero, Nat.mod_eq_of_lt hx, sq]
  have hrhs : (∑ ξ ∈ Finset.range M,
      dft M f ξ * starRingEnd ℂ (dft M f ξ) * (rootOfUnity M) ^ (ξ * 0)).re =
      ∑ ξ ∈ Finset.range M, ‖dft M f ξ‖ ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [mul_zero, pow_zero, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hlhs, hrhs] at h0
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have := congrArg (fun t => (M : ℝ) * t) h0
  field_simp at this
  linarith

/-- Reflection `x ↦ f (M - 1 - x)` preserves DFT magnitudes:
`‖dft M (fun x => if x < M then f (M - 1 - x) else 0) ξ‖ = ‖dft M f ξ‖`. -/
lemma norm_dft_reflect {M : ℕ} (hM : 0 < M) (f : ℕ → ℝ) (ξ : ℕ) :
    ‖dft M (fun x => if x < M then f (M - 1 - x) else 0) ξ‖ = ‖dft M f ξ‖ := by
  have hrel : dft M (fun x => if x < M then f (M - 1 - x) else 0) ξ =
      starRingEnd ℂ ((rootOfUnity M) ^ ξ) * starRingEnd ℂ (dft M f ξ) := by
    unfold dft
    rw [map_sum, Finset.mul_sum]
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
      simp only [hx, ↓reduceIte, map_mul, Complex.conj_ofReal]
      have hpow : (rootOfUnity M) ^ (ξ * x) =
          starRingEnd ℂ ((rootOfUnity M) ^ ξ) *
            starRingEnd ℂ ((rootOfUnity M) ^ (ξ * (M - 1 - x))) := by
        rw [← map_mul, ← pow_add, ← mul_one_add,
          show 1 + (M - 1 - x) = M - x by omega,
          mul_comm ξ (M - x), mul_comm ξ x]
        rw [rootOfUnity_pow_sub_eq_star hM hx.le ξ, starRingEnd_self_apply]
      rw [hpow]; ring
  rw [hrel, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_rootOfUnity_pow, one_mul]

end Erdos030
