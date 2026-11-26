import Cutoff
import Peetre

namespace Canonne

open scoped BigOperators
noncomputable section

/-- A head of mass \(1-t\) followed by \(m\) equal atoms of total mass \(t\). -/
private def headTail (t : ℝ) (m i : ℕ) : ℝ :=
  if i = 0 then 1 - t else if i ≤ m then t / (m : ℝ) else 0

private theorem headTail_tail {t : ℝ} {m i : ℕ} (hi : i ≠ 0) (hm : i ≤ m) :
    headTail t m i = t / (m : ℝ) := by
  simp [headTail, hi, hm]

private theorem headTail_zero {t : ℝ} {m i : ℕ} (hi : m < i) :
    headTail t m i = 0 := by
  simp [headTail, show i ≠ 0 by omega, Nat.not_le.mpr hi]

private theorem headTail_prefix (t : ℝ) {m j : ℕ} (hj : j ≤ m) :
    (∑ i ∈ Finset.range (j + 1), headTail t m i) = (1 - t) + (j : ℝ) * (t / (m : ℝ)) := by
  rw [Finset.sum_range_succ']
  have htail :
      (∑ i ∈ Finset.range j, headTail t m (i + 1)) = (j : ℝ) * (t / (m : ℝ)) := by
    calc
      _ = ∑ _i ∈ Finset.range j, t / (m : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have := Finset.mem_range.mp hi
        exact headTail_tail (by omega) (by omega)
      _ = _ := by simp
  rw [htail]
  simp only [headTail, ite_true]
  ring

private theorem headTail_law {t : ℝ} {m : ℕ} (hm : 0 < m) (ht : 0 ≤ t)
    (hsort : t / (m : ℝ) ≤ 1 - t) : Law (headTail t m) := by
  have tailPos : 0 ≤ t / (m : ℝ) := by positivity
  have headPos := tailPos.trans hsort
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold headTail
    split_ifs <;> (first | assumption | exact le_refl _)
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      simp only [headTail, ite_true]
      split_ifs <;> linarith
    · have hj : j ≠ 0 := by omega
      simp only [headTail, hi, hj, ite_false]
      split_ifs <;> linarith
  · have hsum : HasSum (headTail t m) (∑ i ∈ Finset.range (m+1), headTail t m i) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range (m+1)) (fun i hi =>
        headTail_zero (by have := Finset.mem_range.not.mp hi; omega))
    rw [headTail_prefix t (le_refl m)] at hsum
    have htotal : (1-t) + (m:ℝ) * (t / (m:ℝ)) = 1 := by
      field_simp
      ring
    rwa [htotal] at hsum

private theorem cube_flat_cutIndex {t e : ℝ} {k : ℕ}
    (hp : Law (headTail t (k^3))) (he : 0 < e) (hk : 1 ≤ k) (ht : 0 < t)
    (hmass : 1 - e = (1 - t) + (k:ℝ)^2 * (t / (k:ℝ)^3)) :
    cutIndex hp he = k ^ 2 := by
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by decide)
  have hprefix := headTail_prefix t hk23
  rw [Nat.cast_pow, Nat.cast_pow, ← hmass] at hprefix
  have hle := cutIndex_le_of_capture hp he hprefix.ge
  apply le_antisymm hle
  by_contra! hlt
  have hcap := cutIndex_capture hp he
  rw [headTail_prefix t (hle.trans hk23), Nat.cast_pow] at hcap
  have hltR : ((cutIndex hp he : ℕ) : ℝ) < (k:ℝ)^2 := by exact_mod_cast hlt
  have pos : 0 < t / (k:ℝ)^3 := by positivity
  have hbad := mul_lt_mul_of_pos_right hltR pos
  linarith

private theorem cube_flat_phiAt {t : ℝ} {k : ℕ} (hk : 1 ≤ k) (ht : 0 ≤ t) :
    phiAt (headTail t (k^3)) (k^2) = t := by
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk (by decide)
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by omega)
  have hsum : powerSum (headTail t (k^3)) (k^2) =
      (k:ℝ)^2 * (t / (k:ℝ)^3) ^ (2/3 : ℝ) := by
    unfold powerSum
    calc
      _ = ∑ _i ∈ Finset.range (k^2), (t / (k:ℝ)^3) ^ (2/3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i + 1 ≤ k^3 := Nat.succ_le_of_lt ((Finset.mem_range.mp hi).trans_le hk23)
        rw [headTail_tail (by omega) hi']
        rw [Nat.cast_pow]
      _ = _ := by simp
  have htail : 0 ≤ t / (k:ℝ)^3 := by positivity
  unfold phiAt
  rw [hsum, Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg htail _)]
  rw [← Real.rpow_mul htail, ← Real.rpow_natCast_mul hkR.le]
  norm_num only [show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one,
    Nat.cast_ofNat, show (2 : ℝ) * (3 / 2 : ℝ) = 3 by norm_num, Real.rpow_ofNat]
  field_simp

private theorem headTail_capture {t : ℝ} {m : ℕ} (z : ℕ → ℝ) :
    (∑' i, headTail t m i * z i) =
      (1 - t) * z 0 + (t / (m:ℝ)) * (∑ i ∈ Finset.range m, z (i+1)) := by
  have hsupp (i : ℕ) (hi : i ∉ Finset.range (m+1)) : headTail t m i * z i = 0 := by
    rw [headTail_zero (by have := Finset.mem_range.not.mp hi; omega), zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [headTail_tail (by omega) (Finset.mem_range.mp hi)]

private theorem cube_flat_energy {t e : ℝ} {k : ℕ} {z : ℕ → ℝ}
    (hk : 0 < k) (ht : 0 < t) (hh : 0 ≤ 1-t)
    (hmass : 1 - e = (1-t) + (k:ℝ)^2 * (t / (k:ℝ)^3))
    (hz : Feasible (headTail t (k^3)) e z) :
    Real.sqrt (k : ℝ) ≤ ell2 z := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let s := ∑ i ∈ Finset.range (k^3), z (i+1)
  have hcap := hz.capture
  rw [headTail_capture, Nat.cast_pow] at hcap
  change 1-e ≤ (1-t)*z 0 + (t / (k:ℝ)^3)*s at hcap
  have hhead := mul_le_of_le_one_right hh (hz.le_one 0)
  have hS : (k:ℝ)^2 ≤ s := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < t / (k:ℝ)^3)).mp
    rw [mul_comm s]
    linarith
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (k^3))
    (fun i => z (i + 1)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_pow] at hC
  change s^2 ≤ (∑ i ∈ Finset.range (k^3), z (i+1)^2) * (k:ℝ)^3 at hC
  have hsum : (∑ i ∈ Finset.range (k^3), z (i+1)^2) ≤ ∑' i, z i^2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k^3+1), z i^2 := by
        rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ _ := hz.energy.sum_le_tsum _ (fun i _ => sq_nonneg (z i))
  have hsquare : (k:ℝ)^4 ≤ s^2 := by
    rw [show (k:ℝ)^4 = ((k:ℝ)^2)^2 by ring]
    exact pow_le_pow_left₀ (sq_nonneg _) hS 2
  have hfull : (k:ℝ) * (k:ℝ)^3 ≤ (∑' i, z i^2) * (k:ℝ)^3 := by
    calc
      _ = (k:ℝ)^4 := by ring
      _ ≤ s^2 := hsquare
      _ ≤ _ := hC.trans (mul_le_mul_of_nonneg_right hsum (by positivity))
  exact Real.sqrt_le_sqrt (le_of_mul_le_mul_right hfull (pow_pos hkR 3))

/-- At every fixed positive radius below one, finitely supported laws with
    bounded truncated quasinorm have arbitrarily large inverse Peetre values. -/
theorem same_radius_unbounded {e : ℝ} (he : 0 < e) (he' : e < 1) (A : ℝ) :
    ∃ p : ℕ → ℝ, ∃ hp : Law p, (∃ M : ℕ, ∀ i > M, p i = 0) ∧
      e < phi p e hp he ∧ phi p e hp he < 1 ∧ A < inverseK p e := by
  let g := (1-e)/2
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (max (A^2) (max 1 (1/g)))
  have hA2 : A^2 < (k:ℝ) := (le_max_left _ _).trans_lt hk
  have hk1 : (1:ℝ) < k := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hk
  have hkR : (0:ℝ) < k := by linarith
  have hkN : 0 < k := by exact_mod_cast hkR
  have hkInv : 1 / g < (k:ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hk
  have hsmall : 1 / (k:ℝ) < g := by
    apply (div_lt_iff₀ hkR).2
    have hh := (div_lt_iff₀ hg).1 hkInv
    rwa [mul_comm] at hh
  let t := e / (1 - 1 / (k:ℝ))
  have hden : 0 < 1 - 1 / (k:ℝ) := by
    exact sub_pos.mpr ((div_lt_iff₀ hkR).2 (by simpa using hk1))
  have ht : 0 < t := div_pos he hden
  have ht1 : t < 1 := by
    change e / (1 - 1 / (k:ℝ)) < 1
    apply (div_lt_iff₀ hden).2
    dsimp [g] at hsmall
    linarith
  have hrel : t - t * (1 / (k:ℝ)) = e := by
    calc
      _ = t * (1 - 1 / (k:ℝ)) := by ring
      _ = e := div_mul_cancel₀ _ hden.ne'
  have hte : e < t := by
    have hh : 0 < t * (1 / (k:ℝ)) := by positivity
    linarith
  have hhead : g < 1 - t := by
    have hprod := mul_le_of_le_one_left (by positivity : 0 ≤ 1 / (k:ℝ)) ht1.le
    dsimp [g] at *
    linarith
  have hsort : t / ((k^3 : ℕ) : ℝ) ≤ 1 - t := by
    rw [Nat.cast_pow]
    calc
      _ ≤ 1 / (k:ℝ)^3 := div_le_div_of_nonneg_right ht1.le (by positivity)
      _ ≤ 1 / (k:ℝ) := by
        apply one_div_le_one_div_of_le hkR
        simpa only [pow_one] using (pow_le_pow_right₀ hk1.le (by decide : 1 ≤ 3))
      _ ≤ 1 - t := (hsmall.trans hhead).le
  have hp : Law (headTail t (k^3)) := headTail_law (pow_pos hkN 3) ht.le hsort
  have hmass : 1 - e = (1 - t) + (k:ℝ)^2 * (t / (k:ℝ)^3) := by
    have heq : (k:ℝ)^2 * (t / (k:ℝ)^3) = t * (1 / (k:ℝ)) := by field_simp
    rw [heq]
    linarith
  have hcut : cutIndex hp he = k^2 := cube_flat_cutIndex hp he hkN ht hmass
  have hphi : phi (headTail t (k^3)) e hp he = t := by
    rw [phi, hcut, cube_flat_phiAt hkN ht.le]
  obtain ⟨z, hz, hnorm, _⟩ := inverse_attained hp he he'
  have hlow := cube_flat_energy hkN ht (sub_nonneg.mpr ht1.le) hmass hz
  have hA : A < Real.sqrt (k:ℝ) := by
    by_cases hA0 : 0 ≤ A
    · apply (sq_lt_sq₀ hA0 (Real.sqrt_nonneg _)).mp
      rwa [Real.sq_sqrt hkR.le]
    · exact (lt_of_not_ge hA0).trans_le (Real.sqrt_nonneg _)
  refine ⟨headTail t (k^3), hp, ⟨k^3, fun i hi => headTail_zero hi⟩, ?_, ?_, hA.trans_le ?_⟩
  · rwa [hphi]
  · rwa [hphi]
  · rwa [← hnorm]

end

end Canonne
