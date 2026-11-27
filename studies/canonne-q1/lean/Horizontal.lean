import HeadSmoothing

namespace CanonneQuantile

open scoped BigOperators
noncomputable section

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]

def cost (s : ι → ℝ) (cuts : Finset (Finset ι)) (hc : cuts.Nonempty) (v n : ℝ) : ℝ :=
  Real.sqrt v / Real.sqrt n + 1/n + headProfile s cuts hc n

def slack (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (d n : ℝ) (hn : 0 ≤ n) : ℝ :=
  d + (root q hq n hn)^2

theorem slack_monotone (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (d : ℝ) {n m : ℝ}
    (hn : 0 ≤ n) (hnm : n ≤ m) : slack q hq d n hn ≤ slack q hq d m (hn.trans hnm) :=
  add_le_add_right (pow_le_pow_left₀ (root_spec q hq hn).1 (root_mono q hq hn hnm) 2) _

theorem cost_monotone (s : ι → ℝ) (cuts : Finset (Finset ι)) (hc : cuts.Nonempty)
    (v : ℝ) {n m : ℝ} (hn : 0 < n) (hnm : n ≤ m) : cost s cuts hc v m ≤ cost s cuts hc v n := by
  refine add_le_add (add_le_add (div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
    (Real.sqrt_pos.mpr hn) (Real.sqrt_le_sqrt hnm))
    (div_le_div_of_nonneg_left zero_le_one hn hnm)) ?_
  apply Finset.le_inf'
  intro j hj
  refine (Finset.inf'_le (fun k => cutCost s k m) hj).trans ?_
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (pow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _)
    (sq_pos_of_pos hn) (pow_le_pow_left₀ hn.le hnm 2)

theorem cost_dilate (s : ι → ℝ) (cuts : Finset (Finset ι)) (full : Finset.univ ∈ cuts)
    (v : ℝ) {b n t : ℝ} (hb : 0 < b) (hn : 0 < n) (ht : 1 ≤ t) (hs : ∀ i, b ≤ s i) :
    cost s cuts ⟨_,full⟩ v (t^2*n) ≤ 2*(cost s cuts ⟨_,full⟩ v n + 1/(b^3*n^2))/t := by
  have ht' : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hh := head_profile_dilate s hb hn ht' hs cuts full
  unfold cost
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht'.le]
  have hf : 1/(t^2*n) ≤ (1/n)/t := by
    rw [div_div]
    apply div_le_div_of_nonneg_left zero_le_one (mul_pos hn ht')
    have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg ht'.le hn.le)
    nlinarith
  have he : Real.sqrt v / (t * Real.sqrt n) = (Real.sqrt v / Real.sqrt n)/t := by ring
  rw [he]
  apply (le_div_iff₀ ht').mpr
  have hf' := (le_div_iff₀ ht').mp hf
  have hh' := (le_div_iff₀ ht').mp hh
  have ht0 := div_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg n)
  have hr := div_nonneg (by norm_num : (0:ℝ) ≤ 1) hn.le
  have he' : ((Real.sqrt v/Real.sqrt n)/t)*t = Real.sqrt v/Real.sqrt n :=
    div_mul_cancel₀ _ ht'.ne'
  linarith

theorem unsaturated_at_weak_crossing (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i)
    {a d n M γ G : ℝ} (hn : 0 < n) (_ha : 0 < a) (hd : 0 ≤ d)
    (hda : d ≤ a) (hatoms : ∀ i, q i ≤ a) (hM : 1 ≤ M) (hG : 0 < G)
    (hscale : G ≤ n*slack q hq d n hn.le)
    (hsmall : n^2*a*slack q hq d n hn.le < γ) (hg : 2*γ ≤ G^2) (hcap : M^4*γ ≤ 1) :
    M^2 * slack q hq d n hn.le / 2 ≤ slack q hq d (M*n) (mul_nonneg (by linarith) hn.le) := by
  let y := root q hq n hn.le
  let Y := slack q hq d n hn.le
  have hy : 0 ≤ y := (root_spec q hq hn.le).1
  have hY : 0 ≤ Y := add_nonneg hd (sq_nonneg _)
  change n^2*a*Y < γ at hsmall
  change G ≤ n*Y at hscale
  have hhalf : Y ≤ 2*y^2 := by
    by_contra! h
    have hdY : Y ≤ 2*d := by dsimp [Y,slack,y] at *; linarith
    have h1 := pow_le_pow_left₀ hG.le hscale 2
    have h2 := mul_le_mul_of_nonneg_left (hdY.trans (by linarith : 2*d ≤ 2*a))
      (mul_nonneg (sq_nonneg n) hY)
    nlinarith
  have light (i : τ) : M^2*n*y*Real.sqrt (q i) ≤ 1 := by
    have hsq := Real.sq_sqrt (hq i)
    have h1 : y^2 ≤ Y := by dsimp [Y,slack,y]; linarith
    have h2 := mul_le_mul h1 (hatoms i) (hq i) hY
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by positivity : 0 ≤ M^4) (sq_nonneg n))
    have h4 := mul_le_mul_of_nonneg_left hsmall.le (by positivity : 0 ≤ M^4)
    have h5 : (M^2*n*y*Real.sqrt (q i))^2 = M^4*n^2*(y^2*q i) := by
      calc
        _ = M^4*n^2*(y^2*(Real.sqrt (q i))^2) := by ring
        _ = _ := by rw [hsq]
    nlinarith [sq_nonneg (M^2*n*y*Real.sqrt (q i)-1)]
  have heq := root_unsaturated_dilation q hq hn.le hM light
  change M^2*Y/2 ≤ d + _^2
  rw [heq]
  change M^2*Y/2 ≤ d+(M*y)^2
  nlinarith [mul_le_mul_of_nonneg_left hhalf (sq_nonneg M)]

/-- At the same specified radius, a fixed horizontal dilation closes a
constant difference between upper and lower tests. The cutoff family may
be any collection of head prefixes containing the whole head. The two
multipliers and all displayed constants are independent of the atom counts. -/
theorem horizontal_crossing (s : ι → ℝ) (cuts : Finset (Finset ι)) (full : Finset.univ ∈ cuts)
    (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v : ℝ) {b d n K c M t γ G : ℝ}
    (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hda : d ≤ b^3) (hd : 0 ≤ d)
    (hatoms : ∀ i, q i ≤ b^3) (hn : 0 < n) (hc : 0 < c) (hM : 1 ≤ M) (ht : 1 ≤ t)
    (hγ : 0 < γ) (hG : 0 < G) (hGγ : 2*γ ≤ G^2) (hcap : M^4*γ ≤ 1)
    (hfast : 2*K ≤ c*M^2) (hslow : 2*(K+1/γ) ≤ c*t)
    (hscale : G ≤ n*slack q hq d n hn.le)
    (hweak : cost s cuts ⟨_,full⟩ v n ≤ K*slack q hq d n hn.le) :
    ∃ m : ℝ, n ≤ m ∧ m ≤ max M (t^2)*n ∧
      ∃ hm : 0 ≤ m, cost s cuts ⟨_,full⟩ v m ≤ c*slack q hq d m hm := by
  let Y := slack q hq d n hn.le
  have hY : 0 ≤ Y := add_nonneg hd (sq_nonneg _)
  have hM0 : 0 ≤ M := by linarith
  have ht0 : 0 < t := by linarith
  have htsq : 1 ≤ t^2 := by nlinarith [sq_nonneg (t-1)]
  have hsn : n ≤ t^2*n := le_mul_of_one_le_left hn.le htsq
  by_cases hbig : γ ≤ n^2*b^3*Y
  · refine ⟨t^2*n, hsn, mul_le_mul_of_nonneg_right (le_max_right _ _) hn.le, hn.le.trans hsn, ?_⟩
    have hprod : 0 < b^3*n^2 := by positivity
    have herr : 1/(b^3*n^2) ≤ Y/γ := by
      apply (div_le_div_iff₀ hprod hγ).mpr
      linarith
    have hstep := cost_dilate s cuts full v hb hn ht hs
    refine hstep.trans (le_trans ?_ (mul_le_mul_of_nonneg_left
      (slack_monotone q hq d hn.le hsn) hc.le))
    apply (div_le_iff₀ ht0).mpr
    have hconst := mul_le_mul_of_nonneg_right hslow hY
    change cost s cuts _ v n ≤ K*Y at hweak
    change 2*(cost s cuts _ v n + 1/(b^3*n^2)) ≤ c*Y*t
    simp only [div_eq_mul_inv, one_mul] at herr ⊢
    simp only [one_div] at hconst
    linarith only [herr, hweak, hconst]
  · have hm : n ≤ M*n := le_mul_of_one_le_left hn.le hM
    refine ⟨M*n, hm, mul_le_mul_of_nonneg_right (le_max_left _ _) hn.le, hn.le.trans hm, ?_⟩
    have hx := unsaturated_at_weak_crossing q hq hn (pow_pos hb 3) hd hda hatoms hM hG
      hscale (lt_of_not_ge hbig) hGγ hcap
    refine (cost_monotone s cuts _ v hn hm).trans (hweak.trans ?_)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hx hc.le)
    change K*Y ≤ c*(M^2*Y/2)
    nlinarith [mul_le_mul_of_nonneg_right hfast hY]

/-- A universal horizontal factor works for every pair of finite alphabets
and every collection of allowed head cuts. Its inputs are only the two
comparison constants. -/
def dilation (K c : ℝ) : ℝ :=
  let M := 1 + 2*K/c
  let γ := min ((1/K)^2/2) (1/M^4)
  let t := 1 + 2*(K+1/γ)/c
  max M (t^2)

theorem same_radius_dilation (s : ι → ℝ) (cuts : Finset (Finset ι)) (full : Finset.univ ∈ cuts)
    (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v : ℝ) {b d n K c : ℝ}
    (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hda : d ≤ b^3) (hd : 0 ≤ d)
    (hatoms : ∀ i, q i ≤ b^3) (hn : 0 < n) (hK : 0 < K) (hc : 0 < c)
    (hweak : cost s cuts ⟨_,full⟩ v n ≤ K*slack q hq d n hn.le) :
    ∃ m : ℝ, n ≤ m ∧ m ≤ dilation K c*n ∧
      ∃ hm : 0 ≤ m, cost s cuts ⟨_,full⟩ v m ≤ c*slack q hq d m hm := by
  let M := 1 + 2*K/c
  let G := 1/K
  let γ := min (G^2/2) (1/M^4)
  let t := 1 + 2*(K+1/γ)/c
  have hG : 0 < G := by dsimp [G]; positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith [show 0 ≤ 2*K/c by positivity]
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hγ : 0 < γ := lt_min (by positivity) (by positivity)
  have ht : 1 ≤ t := by dsimp [t]; linarith [show 0 ≤ 2*(K+1/γ)/c by positivity]
  have hGγ : 2*γ ≤ G^2 := by linarith [min_le_left (G^2/2) (1/M^4)]
  have hcap : M^4*γ ≤ 1 := by
    have h := (le_div_iff₀ (pow_pos hM0 4)).mp (min_le_right (G^2/2) (1/M^4))
    change γ * M^4 ≤ 1 at h
    linarith
  have hfast : 2*K ≤ c*M^2 := by
    have hmc : M*c = c + 2*K := by dsimp [M]; field_simp
    have h1 := mul_le_mul_of_nonneg_left hM hM0.le
    nlinarith [mul_le_mul_of_nonneg_right h1 hc.le]
  have hslow : 2*(K+1/γ) ≤ c*t := by
    have htc : t*c = c + 2*(K+1/γ) := by dsimp [t]; field_simp
    linarith
  have hhead : 0 ≤ headProfile s cuts ⟨_,full⟩ n := by
    apply Finset.le_inf'
    intro j _
    exact add_nonneg (bulk_nonneg _ _) (Finset.sum_nonneg fun i _ => pow_nonneg (hb.le.trans (hs i)) _)
  have hscaled : G ≤ n*slack q hq d n hn.le := by
    have hfloor : 1/n ≤ cost s cuts ⟨_,full⟩ v n := by
      unfold cost
      linarith [div_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg n)]
    have hraw := (div_le_iff₀ hn).mp (hfloor.trans hweak)
    exact (div_le_iff₀ hK).mpr (by linarith)
  exact horizontal_crossing s cuts full q hq v hb hs hda hd hatoms hn hc hM ht hγ hG hGγ hcap
    hfast hslow hscaled hweak

end
end CanonneQuantile
