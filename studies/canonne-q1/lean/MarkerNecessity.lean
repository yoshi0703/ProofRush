import RegularCut
import MarkerTilt

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- The binomial marker term is necessary for a successful full test.
The scalar tail bounds are the same ones used in the regular-cut transfer.
If the tail has zero mass the left side is zero. -/
theorem marker_mass_necessary_of_regular_cut
    {n : ℕ} (hn : 0 < n) {q : H ⊕ T → ℝ} (hq : IsLaw q)
    {e x τ ρ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hρ : ρ ≤ 1/64)
    (hfloor : 1 ≤ (n : ℝ) * (1 - ∑ t : T, q (Sum.inr t)))
    (hew : (∑ t : T, q (Sum.inr t)) ≤ e)
    (hfrozen : (∑ t ∈ Finset.univ.filter (fun t : T => τ ≤ q (Sum.inr t)),
      q (Sum.inr t)) ≤ ρ*x)
    (hlight : (n : ℝ) * Real.sqrt x *
      (∑ t ∈ Finset.univ.filter (fun t : T => q (Sum.inr t) < τ),
        q (Sum.inr t) * Real.sqrt (q (Sum.inr t))) ≤ ρ*x)
    (hgeom : 2*τ ≤ x/32)
    (htest : ∃ f, GoodTest q e n f) :
    let w := ∑ t : T, q (Sum.inr t)
    Real.sqrt (w * (1-w) / (n : ℝ)) ≤ 8 * (e-w+x) := by
  classical
  let w := ∑ t : T, q (Sum.inr t)
  let A := 1-w
  have hw0 : 0 ≤ w := Finset.sum_nonneg fun t _ => hq.nonneg _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  change Real.sqrt (w * A / (n : ℝ)) ≤ 8 * (e-w+x)
  change 1 ≤ (n : ℝ) * A at hfloor
  change w ≤ e at hew
  by_cases hzero : w = 0
  · rw [hzero, zero_mul, zero_div, Real.sqrt_zero]
    linarith
  have hw : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hzero)
  have hA : 0 < A := by
    by_contra hbad
    have hneg := mul_nonpos_of_nonneg_of_nonpos hnpos.le (le_of_not_gt hbad)
    linarith
  have hw1 : w < 1 := sub_pos.mp hA
  let d := Real.sqrt (w * A / (n : ℝ)) / 8
  have hd : 0 ≤ d := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hroot_le : Real.sqrt (w*A/(n : ℝ)) ≤ A := by
    have hsq := Real.sq_sqrt (div_nonneg (mul_nonneg hw.le hA.le) hnpos.le)
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hA.le).mp
    rw [hsq]
    apply (div_le_iff₀ hnpos).mpr
    have hcmp : w ≤ (n : ℝ) * A := hw1.le.trans hfloor
    nlinarith [mul_le_mul_of_nonneg_left hcmp hA.le]
  have hdA : d ≤ A := by
    unfold d
    linarith
  let qred := collapsed q
  have hred : IsLaw qred := collapsed_isLaw hq
  let marker : Finset (H ⊕ Unit) := {Sum.inr ()}
  have hmarker : (∑ a ∈ marker, qred a) = w := by
    simp [marker, qred, collapsed, w]
  let reducedAlt := CanonneMarker.shifted qred marker w d
  have hrest : 0 ≤ 1-w-d := by exact sub_nonneg.mpr hdA
  have hplus : 0 ≤ w+d := add_nonneg hw.le hd
  have hReducedAlt : IsLaw reducedAlt := by
    have h := CanonneMarker.shifted_law qred hred.nonneg hred.total marker hmarker hw hw1 hplus hrest
    exact ⟨h.1, h.2⟩
  have hscale : (n : ℝ) * (d^2 / (w * (1-w))) ≤ 1/64 := by
    have hsq := Real.sq_sqrt (div_nonneg (mul_nonneg hw.le hA.le) hnpos.le)
    change (n : ℝ) * ((Real.sqrt (w*A/(n : ℝ)) / 8)^2 / (w*A)) ≤ _
    rw [div_pow, hsq]
    have heq : (n : ℝ) * ((w*A / (n : ℝ)) / (8:ℝ)^2 / (w*A)) = 1/64 := by
      field_simp [hnpos.ne', hw.ne', hA.ne']
      ring
    rw [heq]
  have hTV : totalVariation (pilotLaw (I := Fin n) reducedAlt) (pilotLaw qred) ≤ 1/12 :=
    CanonneMarker.marker_tv_at_scale qred hred.nonneg hred.total marker hmarker hw hw1 hplus hrest n hscale
  have hheadMass : (∑ h : H, q (Sum.inl h)) = A := by
    have h := hq.total
    rw [Fintype.sum_sum_type] at h
    change (∑ h : H, q (Sum.inl h)) + w = 1 at h
    linarith
  have hdeficit : trueHeadDeficit q reducedAlt = d := by
    have hpoint (h : H) : q (Sum.inl h) - reducedAlt (Sum.inl h) = q (Sum.inl h) * (d/A) := by
      simp only [reducedAlt, CanonneMarker.shifted, marker, Finset.mem_singleton, reduceCtorEq,
        ite_false, qred, collapsed, Sum.elim_inl]
      change q (Sum.inl h) - q (Sum.inl h)*((A-d)/A) = _
      field_simp [hA.ne']
      ring
    unfold trueHeadDeficit
    simp only [hpoint]
    have hnonneg (h : H) : 0 ≤ q (Sum.inl h) * (d/A) :=
      mul_nonneg (hq.nonneg _) (div_nonneg hd hA.le)
    simp only [max_eq_left (hnonneg _)]
    rw [← Finset.sum_mul, hheadMass, mul_div_cancel₀ _ hA.ne']
  by_contra hbad
  have hneeded : e-w+x < d := by
    have h := lt_of_not_ge hbad
    unfold d
    linarith
  let weights : Unit → ℝ := fun _ => 1
  let alts : Unit → H ⊕ Unit → ℝ := fun _ => reducedAlt
  have hweights : IsLaw weights := ⟨fun _ => by norm_num [weights], by simp [weights]⟩
  have hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ 1/8 := by
    have hsingle : mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)) = pilotLaw reducedAlt := by
      funext y
      simp [mixLaw, weights, alts]
    rw [hsingle]
    exact hTV.trans (by norm_num)
  exact no_good_test_of_regular_cut hn hq hw hx hτ hρ hfrozen hlight hgeom
    hweights (fun _ => hReducedAlt) (fun _ _ => hdeficit.symm ▸ hneeded) hprior htest

end
end CanonneRegularTransfer
