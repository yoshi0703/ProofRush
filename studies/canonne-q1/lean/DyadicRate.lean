import Horizontal

namespace CanonneQuantile

open scoped BigOperators
noncomputable section

/-- The next binary sample budget loses at most a factor of two. -/
theorem exists_dyadic_at_scale {x : ℝ} (hx : 1 ≤ x) :
    ∃ j : ℕ, x ≤ (2 : ℝ)^j ∧ (2 : ℝ)^j ≤ 2*x := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_gt x
  have h : ∃ j : ℕ, x ≤ (2:ℝ)^j := by
    refine ⟨N,hN.le.trans ?_⟩
    exact_mod_cast (Nat.lt_two_pow_self : N < 2^N).le
  refine ⟨Nat.find h,Nat.find_spec h,?_⟩
  generalize hj : Nat.find h = j
  cases j with
  | zero => simp; linarith
  | succ j =>
    have prev : j < Nat.find h := by omega
    have hp : (2:ℝ)^j < x := lt_of_not_ge (Nat.find_min h prev)
    rw [pow_succ]
    linarith

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]

def crosses (s : ι → ℝ) (cuts : Finset (Finset ι)) (hc : cuts.Nonempty)
    (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v d c : ℝ) (j : ℕ) : Prop :=
  cost s cuts hc v ((2:ℝ)^j) ≤ c*slack q hq d ((2:ℝ)^j) (by positivity)

/-- Evaluates only the displayed arithmetic criteria on the known reference law. -/
def firstDyadic (P : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ j, P j then 2^Nat.find h else 0

theorem firstDyadic_spec (P : ℕ → Prop) (h : ∃ j, P j) :
    ∃ j, P j ∧ firstDyadic P = 2^j ∧ ∀ i, P i → j ≤ i := by
  classical
  exact ⟨Nat.find h,Nat.find_spec h,by simp [firstDyadic,h],fun _ hi => Nat.find_min' h hi⟩

theorem dyadic_crossing_from_weak (s : ι → ℝ) (cuts : Finset (Finset ι))
    (full : Finset.univ ∈ cuts) (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v : ℝ)
    {b d n K c : ℝ} (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hda : d ≤ b^3)
    (hd : 0 ≤ d) (hatoms : ∀ i, q i ≤ b^3) (hn : 1 ≤ n) (hK : 0 < K) (hc : 0 < c)
    (hw : cost s cuts ⟨_,full⟩ v n ≤ K*slack q hq d n (by linarith)) :
    ∃ j, crosses s cuts ⟨_,full⟩ q hq v d c j ∧ (2:ℝ)^j ≤ 2*dilation K c*n := by
  have hn0 : 0 < n := by linarith
  obtain ⟨m,hnm,hmax,hm,hstrong⟩ := same_radius_dilation s cuts full q hq v
    hb hs hda hd hatoms hn0 hK hc hw
  obtain ⟨j,hj,hh⟩ := exists_dyadic_at_scale (hn.trans hnm)
  refine ⟨j,?_,by linarith⟩
  exact (cost_monotone s cuts _ v (hn0.trans_le hnm) hj).trans <|
    hstrong.trans <| mul_le_mul_of_nonneg_left (slack_monotone q hq d hm hj) hc.le

/-- Every scale with the necessary bound controls the first strong crossing by a
universal factor at the very same distance. -/
theorem firstDyadic_le_of_weak (s : ι → ℝ) (cuts : Finset (Finset ι))
    (full : Finset.univ ∈ cuts) (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v : ℝ)
    {b d n K c : ℝ} (hb : 0 < b) (hs : ∀ i, b ≤ s i) (hda : d ≤ b^3)
    (hd : 0 ≤ d) (hatoms : ∀ i, q i ≤ b^3) (hn : 1 ≤ n) (hK : 0 < K) (hc : 0 < c)
    (hw : cost s cuts ⟨_,full⟩ v n ≤ K*slack q hq d n (by linarith)) :
    (firstDyadic (crosses s cuts ⟨_,full⟩ q hq v d c) : ℝ) ≤ 2*dilation K c*n := by
  obtain ⟨i,hi,hsz⟩ := dyadic_crossing_from_weak s cuts full q hq v hb hs hda hd hatoms hn hK hc hw
  obtain ⟨j,_,hj,hmin⟩ := firstDyadic_spec _ ⟨i,hi⟩
  rw [hj,Nat.cast_pow,Nat.cast_ofNat]
  exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (hmin i hi)).trans hsz

theorem dyadic_crossing_exists (s : ι → ℝ) (cuts : Finset (Finset ι))
    (full : Finset.univ ∈ cuts) (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) (v d : ℝ) {c : ℝ}
    (hc : 0 < c) (hy : 0 < slack q hq d 1 (by norm_num)) :
    ∃ j, crosses s cuts ⟨_,full⟩ q hq v d c j := by
  let W := ∑ i, (s i)^2
  let Y := slack q hq d 1 (by norm_num)
  let L := Real.sqrt v + 1 + bulk W 1
  let t := max 1 (L/(c*Y))
  have ht : 1 ≤ t := le_max_left _ _
  have ht0 : 0 < t := by linarith
  have hY : 0 < c*Y := mul_pos hc hy
  have hL : L ≤ t*(c*Y) := (div_le_iff₀ hY).mp (le_max_right _ _)
  have htsq : 1 ≤ t^2 := by nlinarith [sq_nonneg (t-1)]
  obtain ⟨j,hj,_⟩ := exists_dyadic_at_scale htsq
  have hprof : headProfile s cuts ⟨_,full⟩ (t^2) ≤ bulk W 1/t := by
    have hh := Finset.inf'_le (fun k => cutCost s k (t^2)) full
    change headProfile s cuts ⟨_,full⟩ (t^2) ≤ _ at hh
    simp only [cutCost,Finset.compl_univ,Finset.sum_empty,add_zero] at hh
    have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
    simpa only [mul_one] using hh.trans_eq (by simpa only [mul_one] using bulk_dilate hW (by norm_num : (0:ℝ)<1) ht0)
  have hfloor : 1/t^2 ≤ 1/t :=
    div_le_div_of_nonneg_left zero_le_one ht0 (by nlinarith [mul_le_mul_of_nonneg_left ht ht0.le])
  have hcost : cost s cuts ⟨_,full⟩ v (t^2) ≤ L/t := by
    unfold cost
    rw [Real.sqrt_sq ht0.le]
    dsimp [L]
    linarith only [hprof,hfloor,add_div (Real.sqrt v) 1 t,add_div (Real.sqrt v+1) (bulk W 1) t]
  refine ⟨j,(cost_monotone s cuts _ v (sq_pos_of_pos ht0) hj).trans (hcost.trans ?_)⟩
  have hv : L/t ≤ c*Y := (div_le_iff₀ ht0).mpr (by linarith)
  exact hv.trans (mul_le_mul_of_nonneg_left (slack_monotone q hq d (by norm_num) (htsq.trans hj)) hc.le)

theorem positive_initial_slack (q : τ → ℝ) (hq : ∀ i, 0 ≤ q i) {e : ℝ}
    (he : 0 < e) (hw : (∑ i, q i) ≤ e) :
    0 < slack q hq (e-∑ i, q i) 1 (by norm_num) := by
  let W := ∑ i, q i
  let y := root q hq 1 (by norm_num)
  obtain ⟨hy,hfix⟩ := root_spec q hq (by norm_num : (0:ℝ)≤1)
  change 0 < e-W+y^2
  by_cases h : W < e
  · linarith [sq_nonneg y]
  have hWe : W = e := le_antisymm hw (le_of_not_gt h)
  have hi : ∃ i, 0 < q i := by
    by_contra! hnone
    have hz : ∀ i, q i = 0 := fun i => le_antisymm (hnone i) (hq i)
    have : W = 0 := by simp [W,hz]
    linarith
  obtain ⟨i,hi⟩ := hi
  have hyp : 0 < y := by
    refine lt_of_le_of_ne hy ?_
    intro hz
    change 0 = y at hz
    change tail q 1 y = y at hfix
    rw [← hz] at hfix
    have ht : 0 < tail q 1 0 := by
      unfold tail
      apply Finset.sum_pos'
      · intro a _
        positivity [hq a]
      · refine ⟨i,Finset.mem_univ _,?_⟩
        positivity [Real.sqrt_pos.2 hi]
    linarith
  rw [hWe,sub_self,zero_add]
  exact sq_pos_of_pos hyp

end
end CanonneQuantile
