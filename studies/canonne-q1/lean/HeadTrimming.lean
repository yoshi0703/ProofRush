import NearOneTesting
import HeadPower
import HeadSmoothing

namespace CanonneIIDHead

open CanonneNearOneTesting CanonneDiffuse CanonneHeadTransfer CanonneQuantile
open scoped BigOperators
noncomputable section

theorem bulk_sq_scale {W n : ℝ} (hW : 0 ≤ W) (hn : 0 < n) :
    (bulk W n)^2 = W*(Real.sqrt W/n) := by
  apply (pow_left_inj₀ (sq_nonneg _) (mul_nonneg hW (div_nonneg (Real.sqrt_nonneg _) hn.le))
    (by decide : 2 ≠ 0)).mp
  calc
    _ = (bulk W n)^4 := by ring
    _ = W^3/n^2 := bulk_fourth hW n
    _ = _ := by rw [mul_pow,div_pow,Real.sq_sqrt hW]; ring

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exists_trimmed_prefix_test (q : A → ℝ) (hq : IsLaw q)
    (R : Finset A) (s : A → ℝ) (hs : ∀ i ∈ R, 0 < s i) (hqR : ∀ i ∈ R, q i = (s i)^3)
    (n : ℕ) (hn : 0 < n) :
    let B := bulk (∑ i ∈ R, (s i)^2) n
    ∃ K ⊆ R, mass q (R \ K) ≤ B ∧
      ∃ f : (Fin (n+n) → A) → ℝ, (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
        rejection (pilotLaw q) f ≤ 1/100 ∧
        ∀ p : A → ℝ, IsLaw p → 10000*B < ∑ i ∈ K, |p i-q i| →
          99/100 ≤ rejection (pilotLaw p) f := by
  classical
  let W := ∑ i ∈ R, (s i)^2
  let B := bulk W n
  let v := Real.sqrt W / (n:ℝ)
  change ∃ K ⊆ R, mass q (R \ K) ≤ B ∧ _
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := bulk_nonneg _ _
  have point (i) (hi : i ∈ R) : (s i)^2 ≤ W :=
    Finset.single_le_sum (fun j _ => sq_nonneg (s j)) hi
  by_cases hW : W = 0
  · have hR : R = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have z := point i hi
      rw [hW] at z
      exact (not_lt_of_ge z) (sq_pos_of_pos (hs i hi))
    refine ⟨∅,Finset.empty_subset _, ?_, fun _ => 0, fun _ => ⟨le_rfl,zero_le_one⟩, ?_, ?_⟩
    · simpa [hR,mass] using hB
    · simp [rejection]
    · intro p hp hf
      simp only [Finset.sum_empty] at hf
      exfalso
      linarith
  have hWp := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hv : 0 < v := div_pos (Real.sqrt_pos.2 hWp) hnR
  have hnV : (n:ℝ)*v = Real.sqrt W := by dsimp [v]; field_simp
  have hWv : ((n:ℝ)*v)^2 = W := by rw [hnV,Real.sq_sqrt hW0]
  have hBs : B^2 = W*v := bulk_sq_scale hW0 hnR
  let K := R.filter fun i => 1 ≤ (n:ℝ)^2*v*(s i)^2
  have hKR : K ⊆ R := Finset.filter_subset _ _
  have hkpos i (h : i ∈ K) := hs i (hKR h)
  have hsmall i (hi : i ∈ R \ K) : W*s i ≤ B := by
    obtain ⟨hir,hik⟩ := Finset.mem_sdiff.mp hi
    have hh : (n:ℝ)^2*v*(s i)^2 < 1 := by
      by_contra! h
      exact hik (Finset.mem_filter.mpr ⟨hir,h⟩)
    apply le_of_sq_le_sq _ hB
    calc
      (W*s i)^2 = W*((n:ℝ)*v)^2*(s i)^2 := by rw [hWv]; ring
      _ = (W*v)*((n:ℝ)^2*v*(s i)^2) := by ring
      _ ≤ (W*v)*1 := mul_le_mul_of_nonneg_left hh.le (mul_nonneg hW0 hv.le)
      _ = B^2 := by rw [mul_one,hBs]
  have hmass : mass q (R \ K) ≤ B := by
    apply (le_of_mul_le_mul_left _ hWp : _)
    calc
      W * mass q (R \ K) = ∑ i ∈ R \ K, W*q i := by rw [mass,Finset.mul_sum]
      _ ≤ ∑ i ∈ R \ K, B*(s i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hqR i (Finset.mem_sdiff.mp hi).1]
        nlinarith only [mul_le_mul_of_nonneg_right (hsmall i hi) (sq_nonneg (s i))]
      _ = B*(∑ i ∈ R \ K, (s i)^2) := (Finset.mul_sum ..).symm
      _ ≤ B*W := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => sq_nonneg (s i))) hB
      _ = _ := mul_comm _ _
  let u (i : A) := if i ∈ K then ((s i)^2)⁻¹ else 0
  have hu i : 0 ≤ u i := by dsimp [u]; split <;> positivity
  have hcap i : u i ≤ (n:ℝ)^2*v := by
    by_cases hi : i ∈ K
    · simp only [u,ite_eq_left hi]
      rw [inv_eq_one_div,div_le_iff₀ (sq_pos_of_pos (hkpos i hi))]
      exact (Finset.mem_filter.mp hi).2
    · simp [u,hi,show 0 ≤ (n:ℝ)^2*v by positivity]
  have huq i (hi : i ∈ K) : u i*q i = s i := by
    rw [hqR i (hKR hi)]
    simp only [u,ite_eq_left hi]
    field_simp [(hkpos i hi).ne']
  have hnull i : u i*q i ≤ (n:ℝ)*v := by
    by_cases hi : i ∈ K
    · rw [huq _ hi,hnV]
      exact le_of_sq_le_sq ((point _ (hKR hi)).trans_eq (Real.sq_sqrt hW0).symm) (Real.sqrt_nonneg _)
    · simp [u,hi,hnV]
  have hweight : (∑ i, (u i)^2*(q i)^2) ≤ ((n:ℝ)*v)^2 := by
    rw [hWv]
    calc
      _ = ∑ i, if i ∈ K then (s i)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ K
        · rw [ite_eq_left hi,← mul_pow,huq i hi]
        · simp [u,hi]
      _ = ∑ i ∈ K, (s i)^2 := by simp
      _ ≤ W := Finset.sum_le_sum_of_subset_of_nonneg hKR (fun i _ _ => sq_nonneg (s i))
  let E := rejects (n:=n) q u v
  let f (z : Fin (n+n) → A) : ℝ := if E z then 1 else 0
  have hf z : 0 ≤ f z ∧ f z ≤ 1 := by by_cases h : E z <;> simp [f,h]
  have hfE (p : A → ℝ) : rejection (pilotLaw p) f = eventMass (pilotLaw p) E := by
    rw [eventMass_eq_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : E z <;> simp [f,h]
  refine ⟨K,hKR,hmass,f,hf,?_,?_⟩
  · rw [hfE]
    exact score_null_error hq u hn hv hweight
  intro p hp hdist
  have hV0 : 0 ≤ shapeSignal u p q := Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (sq_nonneg _)
  let g (i : A) := |p i-q i| / s i
  have hV : (∑ i ∈ K, (g i)^2) = shapeSignal u p q := by
    unfold shapeSignal
    calc
      _ = ∑ i, if i ∈ K then (g i)^2 else 0 := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ K
        · simp only [ite_eq_left hi,g,div_pow,sq_abs,u]
          ring
        · simp [hi,u]
  have hS : (∑ i ∈ K, s i*g i) = ∑ i ∈ K, |p i-q i| := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [g]
    field_simp [(hkpos i hi).ne']
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq K s g
  rw [hS,hV] at hcs
  have hdist2 := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ) ≤ 10000) hB) hdist.le 2
  have hK : (∑ i ∈ K, (s i)^2) ≤ W :=
    Finset.sum_le_sum_of_subset_of_nonneg hKR (fun i _ _ => sq_nonneg (s i))
  have hpower : 100000000*v ≤ shapeSignal u p q := by
    apply (le_of_mul_le_mul_left _ hWp : _)
    have hh := hdist2.trans (hcs.trans (mul_le_mul_of_nonneg_right hK hV0))
    rw [mul_pow,hBs] at hh
    nlinarith only [hh]
  have hmiss := score_alt_error hp hu hn hv hweight hcap hnull hpower
  have hsum : eventMass (pilotLaw p) E + eventMass (pilotLaw p) (fun z => ¬ E z) = 1 := by
    rw [eventMass_eq_sum,eventMass_eq_sum,← Finset.sum_add_distrib,← (pilotLaw_isLaw (I:=Fin (n+n)) hp).total]
    apply Finset.sum_congr rfl
    intro z _
    by_cases h : E z <;> simp [h]
  rw [hfE]
  change eventMass (pilotLaw p) (fun z => ¬ E z) ≤ 1/100 at hmiss
  linarith

end
end CanonneIIDHead
