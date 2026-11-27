import HeadProfile
import HeadSmoothing

open scoped BigOperators

namespace CanonneHeadEnvelope

def cutoffCandidates (d : ℕ) : Finset (Finset (Fin d)) :=
  (Finset.range (d+1)).image (cutoffPrefix d)

theorem cutoffPrefix_full (d : ℕ) : cutoffPrefix d d = Finset.univ := by
  ext i
  simp [cutoffPrefix]

theorem cutoffCandidates_full (d : ℕ) : Finset.univ ∈ cutoffCandidates d :=
  Finset.mem_image.mpr ⟨d, Finset.mem_range.mpr (Nat.lt_succ_self _), cutoffPrefix_full _⟩

theorem cutoffCandidates_nonempty (d : ℕ) : (cutoffCandidates d).Nonempty :=
  ⟨Finset.univ,cutoffCandidates_full d⟩

private theorem quantile_bulk_eq_source {s n : ℝ} (hs : 0 ≤ s) (hn : 0 < n) :
    CanonneQuantile.bulk s n = s^((3 : ℝ)/4) / Real.sqrt n := by
  have hr : 0 ≤ s^((3 : ℝ)/4) / Real.sqrt n := by positivity
  apply (pow_left_inj₀ (CanonneQuantile.bulk_nonneg _ _) hr (by decide : (4 : ℕ) ≠ 0)).mp
  have hpow : (s^((3 : ℝ)/4))^4 = s^3 := by
    rw [← Real.rpow_mul_natCast hs ((3 : ℝ)/4) 4]
    rw [show (3 : ℝ)/4 * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hSQ : (Real.sqrt n)^4 = n^2 := by
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt hn.le]
  rw [CanonneQuantile.bulk_fourth hs, div_pow, hpow, hSQ]

theorem sourceCutoff_eq_quantile {d j : ℕ} {n : ℝ} {q : Fin (d+1) → ℝ}
    (hn : 0 < n) (hq : ∀ i, 0 ≤ q i) :
    sourceCutoff n j q =
      CanonneQuantile.cutCost (fun i : Fin d ↦ (q i.succ)^((1 : ℝ)/3))
        (cutoffPrefix d j) n := by
  have h2 (i : Fin d) : ((q i.succ)^((1 : ℝ)/3))^2 = (q i.succ)^((2 : ℝ)/3) := by
    rw [← Real.rpow_mul_natCast (hq i.succ) ((1 : ℝ)/3) 2]
    norm_num [show (1 : ℝ)/3 * 2 = (2 : ℝ)/3 by ring]
  have h3 (i : Fin d) : ((q i.succ)^((1 : ℝ)/3))^3 = q i.succ := by
    rw [← Real.rpow_mul_natCast (hq i.succ) ((1 : ℝ)/3) 3]
    rw [show (1 : ℝ)/3 * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  unfold sourceCutoff CanonneQuantile.cutCost
  simp_rw [h2, h3]
  rw [quantile_bulk_eq_source (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hq i.succ) _) hn]
  rfl

/-- The source profile and the actual cutoff geometry use exactly the same costs. -/
theorem headProfile_eq_quantile {d : ℕ} {n : ℝ} {q : Fin (d+1) → ℝ}
    (hn : 0 < n) (hq : ∀ i, 0 ≤ q i) :
    headProfile n q =
      CanonneQuantile.headProfile (fun i : Fin d ↦ (q i.succ)^((1 : ℝ)/3))
        (cutoffCandidates d) (cutoffCandidates_nonempty d) n := by
  let S := Finset.range (d+1)
  have hS : S.Nonempty := ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : Finset (Fin d) → ℝ := fun k ↦
    CanonneQuantile.cutCost (fun i ↦ (q i.succ)^((1 : ℝ)/3)) k n
  calc
    _ = S.inf' hS (fun j ↦ sourceCutoff n j q) := rfl
    _ = S.inf' hS (C ∘ cutoffPrefix d) := by
      apply Finset.inf'_congr hS rfl
      intro j _
      exact sourceCutoff_eq_quantile hn hq
    _ = _ := Finset.inf'_comp_eq_image hS C

end CanonneHeadEnvelope
