import Model

namespace Canonne
open scoped BigOperators
noncomputable section

/-- Mass transport across a cutoff: increasing the weight per unit mass on
later coordinates preserves a deficit-versus-surplus inequality. -/
theorem cutoff_transfer {α : Type*} [DecidableEq α] (s t : Finset α)
    (w a z : α → ℝ) (c : ℝ)
    (hc : 0 < c)
    (hw : ∀ i, 0 ≤ w i) (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (hs : ∀ i ∈ s, c ≤ a i) (ht : ∀ i ∈ t, a i ≤ c)
    (h : (∑ i ∈ s, a i * w i * (1 - z i)) ≤ ∑ i ∈ t, a i * w i * z i) :
    (∑ i ∈ s, w i * (1 - z i)) ≤ ∑ i ∈ t, w i * z i := by
  have hs' : c * (∑ i ∈ s, w i * (1 - z i)) ≤
      ∑ i ∈ s, a i * w i * (1 - z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpos : 0 ≤ w i * (1 - z i) := mul_nonneg (hw i) (sub_nonneg.mpr (hz1 i))
    nlinarith [mul_nonneg (sub_nonneg.mpr (hs i hi)) hpos]
  have ht' : (∑ i ∈ t, a i * w i * z i) ≤
      c * (∑ i ∈ t, w i * z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hpos : 0 ≤ w i * z i := mul_nonneg (hw i) (hz0 i)
    nlinarith [mul_nonneg (sub_nonneg.mpr (ht i hi)) hpos]
  nlinarith

/-- The two exponents used in the analytic Hölder step are conjugate. -/
theorem lower_holder_exponents : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- Cubic mass is controlled by quadratic mass for a unit-bounded vector. -/
theorem cube_le_square {x : ℝ} (h1 : x ≤ 1) : x ^ 3 ≤ x ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h1)]

/-- Raising a two-thirds power to the conjugate exponent recovers the input. -/
theorem two_thirds_conjugate {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x := by
  rw [← Real.rpow_mul hx]
  norm_num

/-- Finite Hölder bound for weighted retained mass. -/
theorem finite_holder_bound (s : Finset ℕ) (p z : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, 0 ≤ z i) :
    (∑ i ∈ s, p i ^ (2 / 3 : ℝ) * z i) ≤
      (∑ i ∈ s, p i) ^ (2 / 3 : ℝ) * (∑ i ∈ s, z i ^ 3) ^ (1 / 3 : ℝ) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (f := fun i => p i ^ (2 / 3 : ℝ)) (g := z) lower_holder_exponents
    (by intro i hi; exact Real.rpow_nonneg (hp i) _) (by intro i hi; exact hz i)
  have ha : (∑ i ∈ s, (p i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) = ∑ i ∈ s, p i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact two_thirds_conjugate (hp i)
  have hb : (∑ i ∈ s, z i ^ (3 : ℝ)) = ∑ i ∈ s, z i ^ 3 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.rpow_natCast (z i) 3
  simpa only [ha, hb, show (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) by norm_num] using h

/-- With a probability-mass budget and unit bounds, Hölder reduces to
one third power of the quadratic energy on any finite set. -/
theorem finite_weighted_energy (s : Finset ℕ) (p z : ℕ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (hpsum : (∑ i ∈ s, p i) ≤ 1) :
    (∑ i ∈ s, p i ^ (2 / 3 : ℝ) * z i) ≤
      (∑ i ∈ s, z i ^ 2) ^ (1 / 3 : ℝ) := by
  have hmass : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg (by intros; apply hp)
  have hpow : (∑ i ∈ s, p i) ^ (2 / 3 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow hmass hpsum (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have henergy : (∑ i ∈ s, z i ^ 3) ≤ ∑ i ∈ s, z i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact cube_le_square (hz1 i)
  have hcube : 0 ≤ ∑ i ∈ s, z i ^ 3 := Finset.sum_nonneg (by intro i hi; exact pow_nonneg (hz i) 3)
  have henergy' := Real.rpow_le_rpow hcube henergy (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hnonneg : 0 ≤ (∑ i ∈ s, z i ^ 3) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hcube _
  calc
    _ ≤ (∑ i ∈ s, p i) ^ (2 / 3 : ℝ) * (∑ i ∈ s, z i ^ 3) ^ (1 / 3 : ℝ) := finite_holder_bound s p z hp hz
    _ ≤ 1 * (∑ i ∈ s, z i ^ 3) ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_right hpow hnonneg
    _ ≤ _ := by simpa using henergy'

/-- Strict cutoff mass is already captured by a sufficiently long finite prefix. -/
theorem finite_capture_prefix {p z : ℕ → ℝ} {u : ℝ} {k : ℕ}
    (hp : Law p) (hc : Cut p u k) (hz : Feasible p u z) (hk : 0 < k) :
    ∃ n, k ≤ n ∧ (∑ i ∈ Finset.range k, p i) < ∑ i ∈ Finset.range n, p i * z i := by
  have hpz : Summable (fun i => p i * z i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hp.nonneg i) (hz.nonneg i))
      (fun i => by nlinarith [mul_nonneg (hp.nonneg i) (sub_nonneg.mpr (hz.le_one i))]) hp.total.summable
  have hlt : (∑ i ∈ Finset.range k, p i) < ∑' i, p i * z i := by
    have hcut : (∑ i ∈ Finset.range k, p i) < 1 - u := by
      rcases hc.2 with hzero | hlt
      · omega
      · exact hlt
    linarith [hz.capture]
  have hevent : ∀ᶠ n in Filter.atTop,
      (∑ i ∈ Finset.range k, p i) < ∑ i ∈ Finset.range n, p i * z i :=
    hpz.hasSum.tendsto_sum_nat.eventually (lt_mem_nhds hlt)
  obtain ⟨n, hn, hncap⟩ := (Filter.Eventually.and (Filter.eventually_ge_atTop k) hevent).exists
  exact ⟨n, hn, hncap⟩

/-- The finite captured mass covers every deficit before the cutoff. -/
theorem finite_cutoff_deficit {p z : ℕ → ℝ} {k n : ℕ}
    (hn : k ≤ n)
    (hcap : (∑ i ∈ Finset.range k, p i) ≤ ∑ i ∈ Finset.range n, p i * z i) :
    (∑ i ∈ Finset.range k, p i * (1 - z i)) ≤ ∑ i ∈ Finset.Ico k n, p i * z i := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun i => p i * z i) hn
  have hdef : (∑ i ∈ Finset.range k, p i * (1 - z i)) =
      (∑ i ∈ Finset.range k, p i) - ∑ i ∈ Finset.range k, p i * z i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdef]
  linarith

/-- The fractional powers used in the cutoff comparison multiply back to p. -/
theorem power_split {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
  rw [← Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num)]
  norm_num

/-- Under finite capture, retained powers are dominated by weighted powers. -/
theorem finite_power_capture {p z : ℕ → ℝ} {u : ℝ} {k n : ℕ}
    (hp : Law p) (hz : Feasible p u z) (hk : 0 < p k) (hn : k ≤ n)
    (hcap : (∑ i ∈ Finset.range k, p i) ≤ ∑ i ∈ Finset.range n, p i * z i) :
    (∑ i ∈ Finset.range k, p i ^ (2 / 3 : ℝ)) ≤
      ∑ i ∈ Finset.range n, p i ^ (2 / 3 : ℝ) * z i := by
  let w : ℕ → ℝ := fun i => p i ^ (2 / 3 : ℝ)
  let a : ℕ → ℝ := fun i => p i ^ (1 / 3 : ℝ)
  have hc : 0 < a k := Real.rpow_pos_of_pos hk _
  have hs : ∀ i ∈ Finset.range k, a k ≤ a i := by
    intro i hi
    apply Real.rpow_le_rpow (hp.nonneg k)
    · exact hp.sorted (Nat.le_of_lt (Finset.mem_range.mp hi))
    · norm_num
  have ht : ∀ i ∈ Finset.Ico k n, a i ≤ a k := by
    intro i hi
    apply Real.rpow_le_rpow (hp.nonneg i)
    · exact hp.sorted (Finset.mem_Ico.mp hi).1
    · norm_num
  have hsplit : ∀ i, a i * w i = p i := fun i => power_split (hp.nonneg i)
  have hd := finite_cutoff_deficit hn hcap
  have hd' : (∑ i ∈ Finset.range k, a i * w i * (1 - z i)) ≤
      ∑ i ∈ Finset.Ico k n, a i * w i * z i := by
    simpa only [hsplit] using hd
  have hw : ∀ i, 0 ≤ w i := fun i => Real.rpow_nonneg (hp.nonneg i) _
  have htrans := cutoff_transfer (Finset.range k) (Finset.Ico k n) w a z (a k)
    hc hw hz.nonneg hz.le_one hs ht hd'
  have heq : (∑ i ∈ Finset.range k, w i * (1 - z i)) =
      (∑ i ∈ Finset.range k, w i) - ∑ i ∈ Finset.range k, w i * z i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq] at htrans
  have hsum := Finset.sum_range_add_sum_Ico (fun i => w i * z i) hn
  change (∑ i ∈ Finset.range k, w i) ≤ ∑ i ∈ Finset.range n, w i * z i
  linarith

/-- The Valiant--Valiant retained quasinorm is bounded by every feasible dual energy. -/
theorem phiAt_le_ell2 {p z : ℕ → ℝ} {u : ℝ} {k : ℕ}
    (hp : Law p) (hc : Cut p u k) (hz : Feasible p u z) : phiAt p k ≤ ell2 z := by
  by_cases hk0 : k = 0
  · subst k
    simp [phiAt, powerSum, ell2, Real.sqrt_nonneg]
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hcut : (∑ i ∈ Finset.range k, p i) < 1 - u := by
    rcases hc.2 with hzero | hstrict
    · contradiction
    · exact hstrict
  have hpk : 0 < p k := by
    have hsum := hc.1
    rw [Finset.sum_range_succ] at hsum
    linarith
  obtain ⟨n, hkn, hcap⟩ := finite_capture_prefix hp hc hz hk
  have hc1 := finite_power_capture hp hz hpk hkn (le_of_lt hcap)
  have hpsum : (∑ i ∈ Finset.range n, p i) ≤ 1 := by
    have h := hp.total.summable.sum_le_tsum (Finset.range n) (by intros; apply hp.nonneg)
    simpa [hp.total.tsum_eq] using h
  have henergy := finite_weighted_energy (Finset.range n) p z hp.nonneg hz.nonneg hz.le_one hpsum
  have hE : (∑ i ∈ Finset.range n, z i ^ 2) ≤ ∑' i, z i ^ 2 :=
    hz.energy.sum_le_tsum _ (by intros; exact sq_nonneg _)
  have hE0 : 0 ≤ ∑ i ∈ Finset.range n, z i ^ 2 := Finset.sum_nonneg (by intros; exact sq_nonneg _)
  have hpowE := Real.rpow_le_rpow hE0 hE (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hret : powerSum p k ≤ ∑ i ∈ Finset.range k, p i ^ (2 / 3 : ℝ) := by
    let f : ℕ → ℝ := fun i => p i ^ (2 / 3 : ℝ)
    have heq1 := Finset.sum_range_succ' f k
    have heq2 := Finset.sum_range_succ f k
    have hsorted : f k ≤ f 0 := by
      apply Real.rpow_le_rpow (hp.nonneg k)
      · exact hp.sorted (Nat.zero_le k)
      · norm_num
    change (∑ i ∈ Finset.range k, f (i + 1)) ≤ ∑ i ∈ Finset.range k, f i
    linarith
  have hS : 0 ≤ powerSum p k := by
    unfold powerSum
    apply Finset.sum_nonneg
    intro i hi
    exact Real.rpow_nonneg (hp.nonneg _) _
  have hfinal : powerSum p k ≤ (∑' i, z i ^ 2) ^ (1 / 3 : ℝ) := by
    exact le_trans hret (le_trans hc1 (le_trans henergy hpowE))
  have hraise := Real.rpow_le_rpow hS hfinal (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hEpos : 0 ≤ ∑' i, z i ^ 2 := tsum_nonneg (fun i => sq_nonneg _)
  unfold phiAt ell2
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hEpos] at hraise
  norm_num at hraise ⊢
  exact hraise

end
end Canonne
