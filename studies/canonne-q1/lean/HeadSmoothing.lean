import TailCrossing
import Mathlib.Data.Finset.Max

namespace CanonneQuantile

open scoped BigOperators
noncomputable section

/-- The retained part of the head proxy in original, unconditional units. -/
def bulk (s n : ℝ) : ℝ := Real.sqrt (Real.sqrt (s^3/n^2))

theorem bulk_nonneg (s n : ℝ) : 0 ≤ bulk s n := Real.sqrt_nonneg _

theorem bulk_fourth {s : ℝ} (hs : 0 ≤ s) (n : ℝ) : (bulk s n)^4 = s^3/n^2 := by
  have hinner : 0 ≤ s^3/n^2 := by positivity
  unfold bulk
  calc
    _ = ((Real.sqrt (Real.sqrt (s^3/n^2)))^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hinner]

theorem bulk_dilate {s n t : ℝ} (hs : 0 ≤ s) (hn : 0 < n) (ht : 0 < t) :
    bulk s (t^2*n) = bulk s n / t := by
  apply (pow_left_inj₀ (bulk_nonneg _ _) (div_nonneg (bulk_nonneg _ _) ht.le)
    (by decide : 4 ≠ 0)).mp
  rw [div_pow, bulk_fourth hs, bulk_fourth hs]
  field_simp

theorem bulk_mono {s v : ℝ} (hs : 0 ≤ s) (hsv : s ≤ v) (n : ℝ) :
    bulk s n ≤ bulk v n := by
  apply Real.sqrt_le_sqrt
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hs hsv 3) (sq_nonneg _)

theorem bulk_twice {s : ℝ} (hs : 0 ≤ s) (n : ℝ) : bulk (2*s) n ≤ 2*bulk s n := by
  apply (pow_le_pow_iff_left₀ (bulk_nonneg _ _) (mul_nonneg (by norm_num) (bulk_nonneg _ _))
    (by decide : 4 ≠ 0)).mp
  rw [mul_pow, bulk_fourth hs, bulk_fourth (by positivity : 0 ≤ 2*s)]
  calc
    (2*s)^3/n^2 = 8*(s^3/n^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem bulk_split {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℝ) :
    bulk (u+v) n ≤ 2*(bulk u n + bulk v n) := by
  rcases le_total u v with h | h
  · calc
      _ ≤ bulk (2*v) n := bulk_mono (add_nonneg hu hv) (by linarith) n
      _ ≤ 2*bulk v n := bulk_twice hv n
      _ ≤ _ := by linarith [bulk_nonneg u n]
  · calc
      _ ≤ bulk (2*u) n := bulk_mono (add_nonneg hu hv) (by linarith) n
      _ ≤ 2*bulk u n := bulk_twice hu n
      _ ≤ _ := by linarith [bulk_nonneg v n]

theorem omitted_bulk {w v b n : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) (hb : 0 < b)
    (hn : 0 < n) (hm : b*w ≤ v) : bulk w n ≤ v + 1/(b^3*n^2) := by
  let E := 1/(b^3*n^2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  apply (pow_le_pow_iff_left₀ (bulk_nonneg _ _) (add_nonneg hv hE) (by decide : 4 ≠ 0)).mp
  rw [bulk_fourth hw]
  have hcube := pow_le_pow_left₀ (mul_nonneg hb.le hw) hm 3
  rw [mul_pow] at hcube
  calc
    _ ≤ v^3 * E := by
      dsimp [E]
      field_simp
      nlinarith
    _ ≤ (v+E)^3 * (v+E) := mul_le_mul (pow_le_pow_left₀ hv (by linarith) 3)
      (by linarith) hE (by positivity)
    _ = _ := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original unconditional head masses are \(s_i^3\). The deleted
largest head label is omitted from the index type. -/
def cutCost (s : ι → ℝ) (keep : Finset ι) (n : ℝ) : ℝ :=
  bulk (∑ i ∈ keep, (s i)^2) n + ∑ i ∈ keepᶜ, (s i)^3

def headProfile (s : ι → ℝ) (cuts : Finset (Finset ι)) (hc : cuts.Nonempty) (n : ℝ) : ℝ :=
  cuts.inf' hc (fun k => cutCost s k n)

theorem actual_omitted_bulk (s : ι → ℝ) {b n : ℝ} (hb : 0 < b) (hn : 0 < n)
    (hs : ∀ i, b ≤ s i) (keep : Finset ι) :
    bulk (∑ i ∈ keepᶜ, (s i)^2) n ≤ (∑ i ∈ keepᶜ, (s i)^3) + 1/(b^3*n^2) := by
  apply omitted_bulk (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => pow_nonneg (hb.le.trans (hs i)) 3) hb hn
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ s i*(s i)^2 := mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)
    _ = _ := by ring

theorem head_profile_dilate (s : ι → ℝ) {b n t : ℝ} (hb : 0 < b) (hn : 0 < n)
    (ht : 0 < t) (hs : ∀ i, b ≤ s i) (cuts : Finset (Finset ι))
    (full : Finset.univ ∈ cuts) :
    headProfile s cuts ⟨_,full⟩ (t^2*n) ≤ 2*(headProfile s cuts ⟨_,full⟩ n + 1/(b^3*n^2))/t := by
  have hc : cuts.Nonempty := ⟨_, full⟩
  obtain ⟨j, hj, hmin⟩ := cuts.exists_min_image (fun k => cutCost s k n) hc
  have hprof : headProfile s cuts hc n = cutCost s j n := by
    apply le_antisymm (Finset.inf'_le _ hj)
    exact Finset.le_inf' _ _ hmin
  have hfull : headProfile s cuts hc (t^2*n) ≤ cutCost s Finset.univ (t^2*n) :=
    Finset.inf'_le _ full
  simp only [cutCost, Finset.compl_univ, Finset.sum_empty, add_zero] at hfull
  rw [hprof, cutCost]
  have hpos (k : Finset ι) : 0 ≤ ∑ i ∈ k, (s i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine hfull.trans ?_
  rw [bulk_dilate (hpos _) hn ht]
  apply div_le_div_of_nonneg_right _ ht.le
  rw [←j.sum_add_sum_compl (fun i => (s i)^2)]
  have hsplit := bulk_split (hpos j) (hpos jᶜ) n
  have hrest := actual_omitted_bulk s hb hn hs j
  linarith

end
end CanonneQuantile
