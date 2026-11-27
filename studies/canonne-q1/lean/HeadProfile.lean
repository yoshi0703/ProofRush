import HeadMinimax
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

namespace CanonneHeadEnvelope

noncomputable def sourceCutoff {d : ℕ} (n : ℝ) (j : ℕ) (q : Fin (d+1) → ℝ) : ℝ :=
  (∑ i ∈ cutoffPrefix d j, (q i.succ)^((2 : ℝ)/3))^((3 : ℝ)/4) / Real.sqrt n +
    ∑ i ∈ (Finset.univ : Finset (Fin d)) \ cutoffPrefix d j, q i.succ

noncomputable def headProfile {d : ℕ} (n : ℝ) (q : Fin (d+1) → ℝ) : ℝ :=
  (Finset.range (d+1)).inf' (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (fun j ↦ sourceCutoff n j q)

def GoodIdentityTest {A : Type*} [Fintype A] (n : ℕ) (q : A → ℝ) (ε : ℝ) : Prop :=
  ∃ f : (Fin n → A) → ℝ,
    (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
    (∑ x, iidMass n q x * f x) ≤ 1/3 ∧
    ∀ p : A → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
      ε < (∑ i, |p i - q i|) / 2 →
      1 - 1/3 ≤ ∑ x, iidMass n p x * f x

private theorem bulk_eq_source {n W : ℝ} (hn : 0 < n) (hW : 0 ≤ W) :
    bulk (1/n^2) W = W^((3 : ℝ)/4) / Real.sqrt n := by
  have hpow : (W^((3 : ℝ)/4))^4 = W^3 := by
    rw [← Real.rpow_mul_natCast hW ((3 : ℝ)/4) 4]
    rw [show (3 : ℝ)/4 * (4 : ℕ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have hSQ : (Real.sqrt n)^4 = n^2 := by
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Real.sq_sqrt hn.le]
  have hR : 0 ≤ W^((3 : ℝ)/4) / Real.sqrt n := by positivity
  have hB : 0 ≤ bulk (1/n^2) W := Real.sqrt_nonneg _
  have hEq : (bulk (1/n^2) W)^4 = (W^((3 : ℝ)/4) / Real.sqrt n)^4 := by
    rw [bulk_pow_four (by positivity) hW, div_pow, hpow, hSQ]
    ring
  apply le_antisymm
  · exact (pow_le_pow_iff_left₀ hB hR (by decide : (4 : ℕ) ≠ 0)).mp hEq.le
  · exact (pow_le_pow_iff_left₀ hR hB (by decide : (4 : ℕ) ≠ 0)).mp hEq.ge

private theorem cube_root_pow {x : ℝ} (hx : 0 ≤ x) :
    (x^((1 : ℝ)/3))^3 = x := by
  rw [← Real.rpow_mul_natCast hx ((1 : ℝ)/3) 3]
  rw [show (1 : ℝ)/3 * (3 : ℕ) = 1 by norm_num, Real.rpow_one]

private theorem cube_root_square {x : ℝ} (hx : 0 ≤ x) :
    (x^((1 : ℝ)/3))^2 = x^((2 : ℝ)/3) := by
  rw [← Real.rpow_mul_natCast hx ((1 : ℝ)/3) 2]
  norm_num [show (1 : ℝ)/3 * 2 = (2 : ℝ)/3 by ring]

theorem headCutoff_eq_source {d n j : ℕ} {q : Fin (d+1) → ℝ}
    (hn : 0 < n) (hq : ∀ i, 0 ≤ q i) :
    headCutoff n d j (fun i ↦ (q i)^((1 : ℝ)/3)) = sourceCutoff n j q := by
  unfold headCutoff cutoffCost sourceCutoff
  simp_rw [cube_root_pow (hq _), cube_root_square (hq _)]
  rw [bulk_eq_source (Nat.cast_pos.mpr hn)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hq i.succ) _)]

theorem head_profile_no_test {n d : ℕ} {q : Fin (d+1) → ℝ} {ε : ℝ}
    (hn : 0 < n) (hq : ∀ i, 0 < q i) (ho : Antitone q) (hm : ∑ i, q i = 1)
    (hfar : 32 * ε < headProfile n q) :
    ¬ GoodIdentityTest n q ε := by
  let a := fun i ↦ (q i)^((1 : ℝ)/3)
  have hc : (fun i ↦ (a i)^3) = q := funext fun i ↦ cube_root_pow (hq i).le
  have hs : 0 < (1 : ℝ)/3 := by norm_num
  have ha : ∀ i, 0 < a i := fun i ↦ Real.rpow_pos_of_pos (hq i) _
  have ho' : Antitone a := fun i j hij ↦ Real.rpow_le_rpow (hq j).le (ho hij) hs.le
  have hnorm : ∑ i, (a i)^3 = 1 := by rw [show (∑ i, (a i)^3) = ∑ i, q i from congrArg _ hc]; exact hm
  have htests := head_cutoff_no_test n d a hn ha ho' hnorm (ε := ε) ?_
  · have htests' : ¬ GoodIdentityTest n (fun i ↦ (a i)^3) ε := htests
    rw [hc] at htests'
    exact htests'
  · intro j hj
    have hj' : j ∈ Finset.range (d+1) := Finset.mem_range.mpr (by omega)
    have hp : headProfile n q ≤ sourceCutoff n j q := Finset.inf'_le _ hj'
    rw [headCutoff_eq_source hn (fun i ↦ (hq i).le)]
    exact hfar.trans_le hp

end CanonneHeadEnvelope
