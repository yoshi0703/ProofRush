import Peetre

namespace Canonne
open scoped BigOperators
noncomputable section

/-- Uniform probability on the first m natural indices, with zero padding. -/
def uniformLaw (m i : ℕ) : ℝ := if i < m then 1 / (m : ℝ) else 0

theorem uniformLaw_law {m : ℕ} (hm : 0 < m) : Law (uniformLaw m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · intro i
    simp only [uniformLaw]
    split_ifs <;> positivity
  · intro i j hij
    simp only [uniformLaw]
    split_ifs <;> first | positivity | linarith
  · have hsum : HasSum (uniformLaw m) (∑ i ∈ Finset.range m, uniformLaw m i) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range m) (by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [uniformLaw, hi])
    have heq : (∑ i ∈ Finset.range m, uniformLaw m i) = 1 := by
      calc
        _ = ∑ _i ∈ Finset.range m, (1 / (m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [uniformLaw, Finset.mem_range.mp hi]
        _ = 1 := by simp [ne_of_gt hmR]
    simpa [heq] using hsum

/-- Radius smaller than one atom keeps every atom, including the final one. -/
theorem uniformLaw_cut {m : ℕ} (hm : 2 ≤ m) :
    Cut (uniformLaw m) (1 / (2 * (m : ℝ))) (m - 1) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (m - 1) + 1 = m := by omega
  have hfull : (∑ i ∈ Finset.range m, uniformLaw m i) = 1 := by
    calc
      _ = ∑ _i ∈ Finset.range m, (1 / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [uniformLaw, Finset.mem_range.mp hi]
      _ = 1 := by simp [ne_of_gt hmR]
  have hlast : uniformLaw m (m - 1) = 1 / (m : ℝ) := by
    simp [uniformLaw, show m - 1 < m by omega]
  have hprev : (∑ i ∈ Finset.range (m - 1), uniformLaw m i) = 1 - 1 / (m : ℝ) := by
    have h := Finset.sum_range_succ (uniformLaw m) (m - 1)
    rw [hm1, hfull, hlast] at h
    linarith
  constructor
  · rw [hm1, hfull]
    have : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
    linarith
  · right
    rw [hprev]
    have hden : (0 : ℝ) < m := hmR
    field_simp
    nlinarith

def uniformIndicator (m i : ℕ) : ℝ := if i < m then 1 else 0

theorem uniformLaw_inverse_upper {m : ℕ} (hm : 2 ≤ m) :
    inverseK (uniformLaw m) (1 / (2 * (m : ℝ))) ≤ Real.sqrt (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hzs : HasSum (fun i => uniformIndicator m i ^ 2) (m : ℝ) := by
    have h : HasSum (fun i => uniformIndicator m i ^ 2)
        (∑ i ∈ Finset.range m, uniformIndicator m i ^ 2) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range m) (by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp [uniformIndicator, hi])
    have hs : (∑ i ∈ Finset.range m, uniformIndicator m i ^ 2) = (m : ℝ) := by
      calc
        _ = ∑ _i ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [uniformIndicator, Finset.mem_range.mp hi]
        _ = _ := by simp
    simpa [hs] using h
  have hcapture : (∑' i, uniformLaw m i * uniformIndicator m i) = 1 := by
    have h : (fun i => uniformLaw m i * uniformIndicator m i) = uniformLaw m := by
      funext i
      simp only [uniformLaw, uniformIndicator]
      split_ifs <;> ring
    rw [h, (uniformLaw_law hmpos).total.tsum_eq]
  have hf : Feasible (uniformLaw m) (1 / (2 * (m : ℝ))) (uniformIndicator m) := by
    constructor
    · intro i
      simp only [uniformIndicator]
      split_ifs <;> norm_num
    · intro i
      simp only [uniformIndicator]
      split_ifs <;> norm_num
    · exact hzs.summable
    · rw [hcapture]
      have : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
      linarith
  have hle := inverseK_le_ell2 (uniformLaw_law hmpos) hf
  unfold ell2 at hle
  rw [hzs.tsum_eq] at hle
  exact hle

theorem uniformLaw_phi {m : ℕ} (hm : 2 ≤ m) :
    phiAt (uniformLaw m) (m - 1) = ((m : ℝ) - 1) ^ (3 / 2 : ℝ) / (m : ℝ) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have htail : 0 ≤ 1 / (m : ℝ) := by positivity
  have hpred : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsum : powerSum (uniformLaw m) (m - 1) =
      ((m : ℝ) - 1) * (1 / (m : ℝ)) ^ (2 / 3 : ℝ) := by
    unfold powerSum
    calc
      _ = ∑ _i ∈ Finset.range (m - 1), (1 / (m : ℝ)) ^ (2 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [uniformLaw, show i + 1 < m by have := Finset.mem_range.mp hi; omega]
      _ = _ := by simp [hpred]
  unfold phiAt
  rw [hsum, Real.mul_rpow (by linarith) (Real.rpow_nonneg htail _)]
  rw [← Real.rpow_mul htail]
  norm_num only [show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  ring

theorem uniformLaw_phi_squared {m : ℕ} (hm : 2 ≤ m) :
    (phiAt (uniformLaw m) (m - 1)) ^ 2 = ((m : ℝ) - 1) ^ 3 / (m : ℝ) ^ 2 := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  rw [uniformLaw_phi hm, div_pow]
  rw [← Real.rpow_mul_natCast (show 0 ≤ (m : ℝ) - 1 by linarith)]
  norm_num

/-- Every universal lower coefficient satisfies this normalized finite bound. -/
theorem uniform_coefficient_constraint {m : ℕ} (hm : 2 ≤ m) (c : ℝ) (hc : 0 ≤ c)
    (hlower : c * phiAt (uniformLaw m) (m - 1) ≤ inverseK (uniformLaw m) (1 / (2 * (m : ℝ)))) :
    c ^ 2 * (1 - 1 / (m : ℝ)) ^ 3 ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hbound := le_trans hlower (uniformLaw_inverse_upper hm)
  have hmR1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hphi0 : 0 ≤ phiAt (uniformLaw m) (m - 1) := by
    rw [uniformLaw_phi hm]
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (le_of_lt hmR)
  have hprod : 0 ≤ c * phiAt (uniformLaw m) (m - 1) := mul_nonneg hc hphi0
  have hsquare : (c * phiAt (uniformLaw m) (m - 1)) ^ 2 ≤ (Real.sqrt (m : ℝ)) ^ 2 := by nlinarith
  rw [mul_pow, uniformLaw_phi_squared hm, Real.sq_sqrt (le_of_lt hmR)] at hsquare
  field_simp at hsquare ⊢
  nlinarith

/-- The coefficient one in the universal lower inequality is optimal. -/
theorem universal_lower_coefficient_optimal (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ (p : ℕ → ℝ) (u : ℝ) (k : ℕ), Law p → Cut p u k →
      0 < u → u < 1 → c * phiAt p k ≤ inverseK p u) :
    c ≤ 1 := by
  have hinv : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto (fun m : ℕ => c ^ 2 * (1 - 1 / (m : ℝ)) ^ 3)
      Filter.atTop (nhds (c ^ 2)) := by
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.sub hinv).pow 3) using 1; norm_num
  have hevent : ∀ᶠ m : ℕ in Filter.atTop, c ^ 2 * (1 - 1 / (m : ℝ)) ^ 3 ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 2] with m hm
    have hmpos : 0 < m := by omega
    have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    have hu0 : (0 : ℝ) < 1 / (2 * (m : ℝ)) := by positivity
    have hu1 : (1 : ℝ) / (2 * (m : ℝ)) < 1 := by
      apply (div_lt_iff₀ (by positivity)).2
      linarith
    have h := hlower (uniformLaw m) (1 / (2 * (m : ℝ))) (m - 1)
      (uniformLaw_law hmpos) (uniformLaw_cut hm) hu0 hu1
    exact uniform_coefficient_constraint hm c hc h
  have hc2 : c ^ 2 ≤ 1 := le_of_tendsto hlim hevent
  nlinarith

end
end Canonne
