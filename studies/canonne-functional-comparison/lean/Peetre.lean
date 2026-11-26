import Model
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp

namespace Canonne

open scoped BigOperators
open Filter Finset Set
noncomputable section

private theorem weighted_summable {p z : ℕ → ℝ} (hp : Law p)
    (hz : ∀ i, 0 ≤ z i) (hz' : ∀ i, z i ≤ 1) :
    Summable fun i => p i * z i :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (hp.nonneg i) (hz i))
    (fun i => mul_le_of_le_one_right (hp.nonneg i) (hz' i)) hp.total.summable

theorem costs_nonempty {p : ℕ → ℝ} (hp : Law p) (t : ℝ) :
    (costs p t).Nonempty := by
  refine ⟨(∑' i, |p i|) + t * ell2 (fun _ => 0), p, fun _ => 0, ?_, ?_, ?_, rfl⟩
  · intro i; simp
  · simpa only [abs_of_nonneg (hp.nonneg _)] using hp.total.summable
  · simp

theorem costs_bounded (p : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    BddBelow (costs p t) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨a, b, _, _, _, rfl⟩
  exact add_nonneg (tsum_nonneg fun i => abs_nonneg (a i)) (mul_nonneg ht (Real.sqrt_nonneg _))

/-- Each bounded witness gives a lower bound on the primal cost for every signed split. -/
theorem witness_level {p z : ℕ → ℝ} {u : ℝ} (hp : Law p) (hz : Feasible p u z) :
    1 - u ≤ peetre p (ell2 z) := by
  refine le_csInf (costs_nonempty hp _) ?_
  rintro _ ⟨a, b, hab, ha, hb, rfl⟩
  have hb' : Summable fun i => |b i| ^ (2 : ℝ) := by
    simpa only [Real.rpow_two, sq_abs] using hb
  have hz' : Summable fun i => z i ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hz.energy
  obtain ⟨hm, hCS⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (fun i => abs_nonneg (b i)) hz.nonneg hb' hz'
  have hCS' : (∑' i, |b i| * z i) ≤ ell2 b * ell2 z := by
    simpa only [ell2, Real.sqrt_eq_rpow, Real.rpow_two, sq_abs] using hCS
  have hpoint (i : ℕ) : p i * z i ≤ |a i| + |b i| * z i := by
    rw [← hab i, add_mul]
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (hz.nonneg i)).trans
        (mul_le_of_le_one_right (abs_nonneg _) (hz.le_one i))
    · exact mul_le_mul_of_nonneg_right (le_abs_self _) (hz.nonneg i)
  have h := (weighted_summable hp hz.nonneg hz.le_one).tsum_le_tsum hpoint (ha.add hm)
  rw [ha.tsum_add hm] at h
  have h' := hz.capture.trans h
  linarith

private def clip (p : ℕ → ℝ) (h : ℝ) (i : ℕ) : ℝ := min 1 (h * p i)

private def captured (p : ℕ → ℝ) (h : ℝ) : ℝ := ∑' i, p i * clip p h i

private theorem clip_nonneg {p : ℕ → ℝ} (hp : Law p) {h : ℝ} (hh : 0 ≤ h) (i : ℕ) :
    0 ≤ clip p h i := le_min zero_le_one (mul_nonneg hh (hp.nonneg i))

private theorem clip_le (p : ℕ → ℝ) (h : ℝ) (i : ℕ) : clip p h i ≤ 1 := min_le_left _ _

private theorem exists_clip {p : ℕ → ℝ} (hp : Law p) {u : ℝ} (hu : 0 < u) (hu' : u < 1) :
    ∃ h : ℝ, 0 < h ∧ captured p h = 1 - u := by
  obtain ⟨N, hN⟩ := (hp.total.tendsto_sum_nat.eventually_const_lt (show 1-u < 1 by linarith)).exists
  let H := ∑ i ∈ range N, (p i)⁻¹
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (hp.nonneg i)
  have heq (i : ℕ) (hi : i ∈ range N) : p i * clip p H i = p i := by
    rcases (hp.nonneg i).eq_or_lt with he | he
    · simp [← he]
    · have hsum : (p i)⁻¹ ≤ H :=
        Finset.single_le_sum (f := fun j => (p j)⁻¹) (fun j _ => inv_nonneg.mpr (hp.nonneg j)) hi
      have hprod := mul_le_mul_of_nonneg_right hsum he.le
      rw [inv_mul_cancel₀ he.ne'] at hprod
      simp [clip, min_eq_left hprod]
  have large : 1 - u ≤ captured p H := calc
    1 - u ≤ ∑ i ∈ range N, p i := hN.le
    _ = ∑ i ∈ range N, p i * clip p H i :=
      Finset.sum_congr rfl (fun i hi => (heq i hi).symm)
    _ ≤ captured p H := (weighted_summable hp (clip_nonneg hp hH) (clip_le p H)).sum_le_tsum _
      (fun i _ => mul_nonneg (hp.nonneg i) (clip_nonneg hp hH i))
  have cont : ContinuousOn (captured p) (Icc 0 H) := by
    apply continuousOn_tsum (f := fun (i : ℕ) (x : ℝ) => p i * clip p x i) (u := p)
    · intro i
      change ContinuousOn (fun x : ℝ => p i * min 1 (x * p i)) (Icc 0 H)
      fun_prop
    · exact hp.total.summable
    · intro i h hh
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp.nonneg i) (clip_nonneg hp hh.1 i))]
      exact mul_le_of_le_one_right (hp.nonneg i) (clip_le p h i)
  have atZero : captured p 0 = 0 := by simp [captured, clip]
  obtain ⟨h, hi, eq⟩ := intermediate_value_Icc hH cont (show 1-u ∈ Icc (captured p 0) (captured p H) from
    ⟨by rw [atZero]; linarith, large⟩)
  refine ⟨h, ?_, eq⟩
  rcases hi.1.eq_or_lt with h0 | hpos
  · rw [← h0, atZero] at eq
    linarith
  · exact hpos

theorem inverseK_le_ell2 {p z : ℕ → ℝ} {u : ℝ} (hp : Law p) (hz : Feasible p u z) :
    inverseK p u ≤ ell2 z := by
  exact csInf_le (s := {t : ℝ | 0 ≤ t ∧ 1-u ≤ peetre p t})
    ⟨0, fun _ ht => ht.1⟩ ⟨Real.sqrt_nonneg _, witness_level hp hz⟩

/-- The countable dual minimizer gives exactly the inverse of the signed primal Peetre functional. -/
theorem inverse_attained {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) (hu' : u < 1) :
    ∃ z, Feasible p u z ∧ ell2 z = inverseK p u ∧ peetre p (ell2 z) = 1-u := by
  obtain ⟨h, hh, hcap⟩ := exists_clip hp hu hu'
  let z := clip p h
  have zpos (i : ℕ) : 0 ≤ z i := clip_nonneg hp hh.le i
  have zone (i : ℕ) : z i ≤ 1 := clip_le p h i
  have zsmall (i : ℕ) : z i ≤ h * p i := min_le_right _ _
  have zs : Summable (fun i => z i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i =>
      (show z i ^ 2 ≤ z i by nlinarith [mul_nonneg (zpos i) (sub_nonneg.mpr (zone i))]).trans (zsmall i))
      (hp.total.summable.mul_left h)
  have hf : Feasible p u z := ⟨zpos,zone,zs,hcap.ge⟩
  let c := h⁻¹
  have hc : 0 < c := inv_pos.mpr hh
  let a := fun i => p i - c * z i
  let b := fun i => c * z i
  have scale : c * h = 1 := inv_mul_cancel₀ hh.ne'
  have aPos (i : ℕ) : 0 ≤ a i := by
    have hle := mul_le_mul_of_nonneg_left (zsmall i) hc.le
    rw [← mul_assoc, scale, one_mul] at hle
    exact sub_nonneg.mpr hle
  have asum : Summable a := Summable.of_nonneg_of_le aPos
    (fun i => sub_le_self _ (mul_nonneg hc.le (zpos i))) hp.total.summable
  have aabs : (fun i => |a i|) = a := funext fun i => abs_of_nonneg (aPos i)
  have bpoint (i : ℕ) : b i ^ 2 = c ^ 2 * z i ^ 2 := mul_pow _ _ 2
  have bsum : Summable fun i => b i ^ 2 := by simpa only [bpoint] using zs.mul_left (c ^ 2)
  have bnorm : ell2 b = c * ell2 z := by
    simp only [ell2,bpoint,tsum_mul_left,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le]
  have complement (i : ℕ) : a i * z i = a i := by
    by_cases hsat : 1 ≤ h * p i
    · have : z i = 1 := min_eq_left hsat
      rw [this,mul_one]
    · have : z i = h * p i := min_eq_right (le_of_not_ge hsat)
      have zero : a i = 0 := by
        dsimp only [a]
        rw [this, ← mul_assoc, scale, one_mul, sub_self]
      rw [zero, zero_mul]
  have captureIdentity : 1 - u = (∑' i, a i) + c * (ell2 z) ^ 2 := by
    have term (i : ℕ) : p i * z i = a i + c * z i ^ 2 := by
      calc
        p i * z i = (a i + c * z i) * z i := by dsimp only [a]; ring
        _ = a i + c * z i ^ 2 := by rw [add_mul, complement]; ring
    calc
      1-u = ∑' i, p i * z i := hcap.symm
      _ = ∑' i, (a i + c * z i ^ 2) := tsum_congr term
      _ = (∑' i, a i) + c * ∑' i, z i ^ 2 := by rw [asum.tsum_add (zs.mul_left c), tsum_mul_left]
      _ = _ := by rw [ell2, Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg (z i))]
  have candidate (t : ℝ) (ht : 0 ≤ t) :
      peetre p t ≤ (∑' i, a i) + t * (c * ell2 z) := by
    apply csInf_le (costs_bounded p ht)
    refine ⟨a,b,?_,?_,bsum,?_⟩
    · intro i; dsimp only [a,b]; ring
    · rwa [aabs]
    · rw [aabs,bnorm]
  have nonempty : {t : ℝ | 0 ≤ t ∧ 1-u ≤ peetre p t}.Nonempty :=
    ⟨ell2 z, Real.sqrt_nonneg _, witness_level hp hf⟩
  refine ⟨z,hf,le_antisymm (le_csInf nonempty ?_) (inverseK_le_ell2 hp hf),?Sub⟩
  · intro t ht
    have hm := ht.2.trans (candidate t ht.1)
    rw [captureIdentity] at hm
    by_contra! hlt
    have hpz := mul_pos hc (ht.1.trans_lt hlt)
    nlinarith [mul_pos (sub_pos.mpr hlt) hpz]
  case Sub =>
    apply le_antisymm _ (witness_level hp hf)
    rw [captureIdentity]
    exact (candidate (ell2 z) (Real.sqrt_nonneg _)).trans_eq (by ring)

end
end Canonne
