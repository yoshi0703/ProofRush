import Peetre

namespace Canonne
open scoped BigOperators
noncomputable section

/-- One half at the head, followed by m equal tail atoms. -/
def halfFlat (m : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 / 2 else if i ≤ m then 1 / (2 * (m : ℝ)) else 0

lemma halfFlat_tail {m i : ℕ} (hi : 1 ≤ i) (him : i ≤ m) :
    halfFlat m i = 1 / (2 * (m : ℝ)) := by
  simp [halfFlat, Nat.ne_of_gt hi, him]

lemma halfFlat_prefix (m k : ℕ) (_hm : 0 < m) (hk : k ≤ m) :
    (∑ i ∈ Finset.range (k + 1), halfFlat m i) = 1 / 2 + (k : ℝ) / (2 * (m : ℝ)) := by
  rw [Finset.sum_range_succ']
  have htail : (∑ i ∈ Finset.range k, halfFlat m (i + 1)) =
      (k : ℝ) * (1 / (2 * (m : ℝ))) := by
    calc
      _ = ∑ _i ∈ Finset.range k, (1 / (2 * (m : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact halfFlat_tail (by omega) (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  rw [htail]
  simp [halfFlat]
  ring

lemma halfFlat_law {m : ℕ} (hm : 0 < m) : Law (halfFlat m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hhalf : 1 / (2 * (m : ℝ)) ≤ 1 / 2 := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith
  have htail : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  constructor
  · intro i
    simp only [halfFlat]
    split_ifs <;> positivity
  · intro i j hij
    by_cases hi : i = 0
    · subst i
      simp only [halfFlat, ite_true]
      split_ifs <;> linarith
    · have hj : j ≠ 0 := by omega
      simp only [halfFlat, hi, hj, ite_false]
      split_ifs <;> linarith
  · have hsum : HasSum (halfFlat m) (∑ i ∈ Finset.range (m + 1), halfFlat m i) := hasSum_sum_of_ne_finset_zero (s := Finset.range (m + 1))
      (f := halfFlat m) (by intro i hi; simp only [Finset.mem_range] at hi; simp [halfFlat, show i ≠ 0 by omega, show ¬ i ≤ m by omega])
    have heq : (∑ i ∈ Finset.range (m + 1), halfFlat m i) = 1 := by
      rw [halfFlat_prefix m m hm (le_refl _)]
      field_simp
      ring
    simpa [heq] using hsum

lemma halfFlat_cut {m : ℕ} (hm : 2 ≤ m) :
    Cut (halfFlat m) (1 / (4 * (m : ℝ))) m := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  constructor
  · rw [halfFlat_prefix m m hmpos (le_refl _)]
    have hmul : 0 < 4 * (m : ℝ) := by positivity
    have hfrac : 0 < 1 / (4 * (m : ℝ)) := by positivity
    field_simp
    nlinarith
  · right
    have hpred : (m - 1) + 1 = m := by omega
    have hpre := halfFlat_prefix m (m - 1) hmpos (by omega)
    rw [hpred] at hpre
    rw [hpre]
    have hpredR : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hpredR]
    have hmul : 0 < 4 * (m : ℝ) := by positivity
    field_simp
    nlinarith

lemma halfFlat_phi {m : ℕ} (hm : 0 < m) :
    phiAt (halfFlat m) m = Real.sqrt (m : ℝ) / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htail : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  have hsum : powerSum (halfFlat m) m = (m : ℝ) * (1 / (2 * (m : ℝ))) ^ (2 / 3 : ℝ) := by
    unfold powerSum
    calc
      _ = ∑ _i ∈ Finset.range m, (1 / (2 * (m : ℝ))) ^ (2 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [halfFlat_tail (by omega) (by have := Finset.mem_range.mp hi; omega)]
      _ = _ := by simp
  unfold phiAt
  rw [hsum, Real.mul_rpow (le_of_lt hmR) (Real.rpow_nonneg htail _)]
  rw [← Real.rpow_mul htail]
  norm_num only [show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  have hpower : (m : ℝ) ^ (3 / 2 : ℝ) = (m : ℝ) * Real.sqrt (m : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hmR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpower]
  field_simp

lemma halfFlat_feasible_tail {m : ℕ} (hm : 0 < m) {z : ℕ → ℝ}
    (hz : Feasible (halfFlat m) (1 / 4) z) :
    (m : ℝ) / 2 ≤ ∑ i ∈ Finset.range m, z (i + 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : HasSum (fun i => halfFlat m i * z i)
      (∑ i ∈ Finset.range (m + 1), halfFlat m i * z i) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range (m + 1)) (by
      intro i hi
      have hnot : ¬ i < m + 1 := by simpa using hi
      simp [halfFlat, show i ≠ 0 by omega, show ¬ i ≤ m by omega])
  have htail : (∑ i ∈ Finset.range m, halfFlat m (i + 1) * z (i + 1)) =
      (1 / (2 * (m : ℝ))) * (∑ i ∈ Finset.range m, z (i + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [halfFlat_tail (by omega) (by have := Finset.mem_range.mp hi; omega)]
  have hc := hz.capture
  rw [hsum.tsum_eq, Finset.sum_range_succ', htail] at hc
  simp only [halfFlat, ite_true] at hc
  have hz0 := hz.le_one 0
  have hmul : 0 < 4 * (m : ℝ) := by positivity
  field_simp at hc
  nlinarith

lemma halfFlat_feasible_energy {m : ℕ} (hm : 0 < m) {z : ℕ → ℝ}
    (hz : Feasible (halfFlat m) (1 / 4) z) :
    Real.sqrt (m : ℝ) / 2 ≤ ell2 z := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htail := halfFlat_feasible_tail hm hz
  have hC := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun i => z (i + 1)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hC
  have hE : (∑ i ∈ Finset.range m, z (i + 1) ^ 2) ≤ ∑' i, z i ^ 2 := by
    have hsumm : Summable (fun i => z (i + 1) ^ 2) := hz.energy.comp_injective (by intro x y h; exact Nat.add_right_cancel h)
    have hle := hsumm.sum_le_tsum (Finset.range m) (by intros; exact sq_nonneg _)
    have hshift : (∑' i, z (i + 1) ^ 2) ≤ ∑' i, z i ^ 2 := by
      have h0 := hz.energy.tsum_eq_zero_add
      nlinarith [sq_nonneg (z 0)]
    exact le_trans hle hshift
  have hE0 : 0 ≤ ∑' i, z i ^ 2 := tsum_nonneg (fun i => sq_nonneg _)
  have hsq : (Real.sqrt (m : ℝ)) ^ 2 = m := Real.sq_sqrt (le_of_lt hmR)
  have hsqE : (Real.sqrt (∑' i, z i ^ 2)) ^ 2 = ∑' i, z i ^ 2 := Real.sq_sqrt hE0
  have hrt := Real.sqrt_nonneg (m : ℝ)
  have hrtE := Real.sqrt_nonneg (∑' i, z i ^ 2)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range m, z (i + 1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact hz.nonneg _
  have hsqL : ((m : ℝ) / 2) ^ 2 ≤ (∑ i ∈ Finset.range m, z (i + 1)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hE (le_of_lt hmR)
  have hfactor : (m : ℝ) * ((m : ℝ) / 4) ≤ (m : ℝ) * (∑' i, z i ^ 2) := by nlinarith
  have hlower : (m : ℝ) / 4 ≤ ∑' i, z i ^ 2 := le_of_mul_le_mul_left hfactor hmR
  unfold ell2
  nlinarith

lemma halfFlat_inverse_lower {m : ℕ} (hm : 0 < m) :
    Real.sqrt (m : ℝ) / 2 ≤ inverseK (halfFlat m) (1 / 4) := by
  obtain ⟨z, hz, heq, _⟩ := inverse_attained (halfFlat_law hm) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  rw [← heq]
  exact halfFlat_feasible_energy hm hz

/-- Every proposed upper coefficient obeys this necessary finite-m inequality. -/
theorem halfFlat_coefficient_constraint {m : ℕ} (hm : 2 ≤ m) (c : ℝ)
    (hupper : inverseK (halfFlat m) (1 / 4) ≤
      Real.sqrt (1 + (c * phiAt (halfFlat m) m /
        ((1 / 4 : ℝ) - 1 / (4 * (m : ℝ)))) ^ 2)) :
    (m : ℝ) / 4 ≤ 1 + (c * (Real.sqrt (m : ℝ) / 2) /
      ((1 / 4 : ℝ) - 1 / (4 * (m : ℝ)))) ^ 2 := by
  have hmpos : 0 < m := by omega
  have hlow := halfFlat_inverse_lower hmpos
  rw [halfFlat_phi hmpos] at hupper
  have h1 : 0 ≤ Real.sqrt (m : ℝ) / 2 := by positivity
  have h2 : 0 ≤ 1 + (c * (Real.sqrt (m : ℝ) / 2) /
      ((1 / 4 : ℝ) - 1 / (4 * (m : ℝ)))) ^ 2 := by positivity
  have hsq := Real.sq_sqrt h2
  have hmR : 0 ≤ (m : ℝ) := by positivity
  have hsm := Real.sq_sqrt hmR
  nlinarith

/-- A normalized coefficient constraint, suitable for passage to the limit. -/
theorem halfFlat_coefficient_normalized {m : ℕ} (hm : 2 ≤ m) (c : ℝ)
    (hupper : inverseK (halfFlat m) (1 / 4) ≤
      Real.sqrt (1 + (c * phiAt (halfFlat m) m /
        ((1 / 4 : ℝ) - 1 / (4 * (m : ℝ)))) ^ 2)) :
    (((m : ℝ) - 1) / (4 * (m : ℝ))) ^ 2 * (1 - 4 / (m : ℝ)) ≤ c ^ 2 := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hdiff : (1 / 4 : ℝ) - 1 / (4 * (m : ℝ)) = ((m : ℝ) - 1) / (4 * (m : ℝ)) := by field_simp
  have hgap : ((m : ℝ) - 1) / (4 * (m : ℝ)) ≠ 0 := by positivity
  have hbase := halfFlat_coefficient_constraint hm c hupper
  rw [hdiff] at hbase
  have hroot := Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity)
  field_simp at hbase ⊢
  rw [hroot] at hbase
  nlinarith

/-- No nonnegative coefficient smaller than one quarter can work uniformly
for all sorted laws and all admissible cutoff levels. -/
theorem universal_coefficient_lower (c : ℝ) (hc : 0 ≤ c)
    (hupper : ∀ (p : ℕ → ℝ) (u η : ℝ) (k : ℕ),
      Law p → Cut p η k → 0 < η → η < u → u < 1 →
      inverseK p u ≤ Real.sqrt (1 + (c * phiAt p k / (u - η)) ^ 2)) :
    1 / 4 ≤ c := by
  have hinv : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto
      (fun m : ℕ => ((1 - (1 : ℝ) / (m : ℝ)) / 4) ^ 2 *
        (1 - 4 * ((1 : ℝ) / (m : ℝ)))) Filter.atTop (nhds (1 / 16 : ℝ)) := by
    convert (((tendsto_const_nhds.sub hinv).div_const 4).pow 2).mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)) using 1; norm_num
  have hevent : ∀ᶠ m : ℕ in Filter.atTop,
      ((1 - (1 : ℝ) / (m : ℝ)) / 4) ^ 2 *
        (1 - 4 * ((1 : ℝ) / (m : ℝ))) ≤ c ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with m hm
    have hmpos : 0 < m := by omega
    have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    have heta0 : (0 : ℝ) < 1 / (4 * (m : ℝ)) := by positivity
    have hetalt : (1 : ℝ) / (4 * (m : ℝ)) < 1 / 4 := by
      apply (div_lt_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
    have hu := hupper (halfFlat m) (1 / 4) (1 / (4 * (m : ℝ))) m
      (halfFlat_law hmpos) (halfFlat_cut hm) heta0 hetalt (by norm_num)
    have hb := halfFlat_coefficient_normalized hm c hu
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    convert hb using 1; field_simp
  have hlimbound : (1 / 16 : ℝ) ≤ c ^ 2 := le_of_tendsto hlim hevent
  nlinarith

end
end Canonne
