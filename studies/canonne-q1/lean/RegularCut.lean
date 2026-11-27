import RegularRounded

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot CanonneNearOneTesting
open scoped BigOperators
noncomputable section

/-- Take only indices of occupied dyadic bins for any specified finite
set of light labels. Ties at the original cutoff can be kept outside. -/
theorem exists_occupied_dyadic_bins {A : Type*} [Fintype A] (q : A → ℝ)
    (light : A → Prop) {top : ℝ} (htop : 0 < top)
    (hl : ∀ a, light a → 0 < q a ∧ q a ≤ top) :
    ∃ S : Finset ℕ, ∃ bin : A → Option S,
      (∀ a, light a ↔ bin a ≠ none) ∧
      (∀ j, ∃ a, bin a = some j) ∧
      (∀ a j, bin a = some j → q a ≤ top * (1/2 : ℝ)^j.val ∧
        top * (1/2 : ℝ)^j.val ≤ 2*q a) ∧
      (∑ j : S, top * (1/2 : ℝ)^j.val) ≤ 2*top := by
  classical
  let L := {a // light a}
  let d (a : L) : ℕ := Classical.choose (exists_dyadic_bin (hl a a.2).1 htop (hl a a.2).2)
  have hd (a : L) : q a ≤ top * (1/2 : ℝ)^(d a) ∧ top * (1/2 : ℝ)^(d a) ≤ 2*q a :=
    Classical.choose_spec (exists_dyadic_bin (hl a a.2).1 htop (hl a a.2).2)
  let S := Finset.univ.image d
  let bin (a : A) : Option S :=
    if h : light a then some ⟨d ⟨a,h⟩, Finset.mem_image.mpr ⟨⟨a,h⟩, Finset.mem_univ _, rfl⟩⟩
    else none
  have assigned (a : L) :
      bin a = some ⟨d a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩ := by
    unfold bin
    rw [dite_eq_left a.2]
  have heq a : light a ↔ bin a ≠ none := by
    by_cases ha : light a <;> simp [bin, ha]
  refine ⟨S, bin, heq, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp j.2
    refine ⟨a, (assigned a).trans ?_⟩
    congr 1
    exact Subtype.ext ha
  · intro a j hj
    have ha : light a := (heq a).2 (by simp [hj])
    have hj' := (assigned ⟨a, ha⟩).symm.trans hj
    have ht := hd ⟨a, ha⟩
    rw [show d ⟨a, ha⟩ = j.val from congrArg Subtype.val (Option.some.inj hj')] at ht
    exact ht
  · rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach S (fun j => top * (1/2 : ℝ)^j)).trans_le (dyadic_top_sum htop.le S)

section Decomposition

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

def residualOf (q : A → ℝ) (bin : A → Option B) (a : A) : ℝ :=
  if bin a = none then q a else 0

theorem sum_occupied_and_residual (q : A → ℝ) (bin : A → Option B) :
    (∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) + (∑ a, residualOf q bin a) =
      ∑ a, q a := by
  unfold CanonneNearOne.normalizedBinMass residualOf
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  cases ha : bin a <;> simp

/-- Split a reference law into its active conditional bins and a fresh
residual part. If the residual is empty, its coefficient is zero. -/
theorem exists_fresh_residual_ref {q : A → ℝ} (hq : IsLaw q)
    (bin : A → Option B) (hb : ∀ j, 0 < CanonneNearOne.normalizedBinMass q 1 bin j) :
    ∃ fresh : A → ℝ, IsLaw fresh ∧
      (∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) ≤ 1 ∧
      q = bandedLabel (CanonneNearOne.normalizedBinMass q 1 bin) fresh (binConditional q bin) ∧
      ∀ a, (1 - ∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) * fresh a = residualOf q bin a := by
  let res := residualOf q bin
  let s := ∑ a, res a
  have hres (a : A) : 0 ≤ res a := by
    unfold res residualOf
    split <;> first | exact le_rfl | exact hq.nonneg _
  have hs : 0 ≤ s := Finset.sum_nonneg (fun a _ => hres a)
  have hsplit := sum_occupied_and_residual q bin
  rw [hq.total] at hsplit
  change (∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) + s = 1 at hsplit
  have hs' : 1 - (∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) = s := by linarith
  let fresh : A → ℝ := if 0 < s then fun a => res a / s else q
  have hFresh : IsLaw fresh := by
    unfold fresh
    split
    · rename_i hp
      refine ⟨fun a => div_nonneg (hres a) hp.le, ?_⟩
      rw [← Finset.sum_div]
      change s/s = 1
      exact div_self hp.ne'
    · exact hq
  have hscaled (a : A) :
      (1 - ∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) * fresh a = res a := by
    rw [hs']
    unfold fresh
    split
    · rename_i hp
      exact mul_div_cancel₀ _ hp.ne'
    · rename_i hno
      have hz : s = 0 := hs.antisymm' (le_of_not_gt hno)
      have hle : res a ≤ s :=
        Finset.single_le_sum (fun a _ => hres a) (Finset.mem_univ a)
      rw [hz, zero_mul]
      exact (le_antisymm (hle.trans hz.le) (hres a)).symm
  refine ⟨fresh, hFresh, by linarith, ?_, hscaled⟩
  funext a
  unfold bandedLabel
  rw [hscaled]
  have hpoint (j : B) :
      CanonneNearOne.normalizedBinMass q 1 bin j * binConditional q bin j a =
        if bin a = some j then q a else 0 := by
    unfold binConditional
    split
    · exact mul_div_cancel₀ _ (hb j).ne'
    · simp
  simp only [hpoint]
  cases ha : bin a <;> simp [res, residualOf, ha]

end Decomposition

section Cut

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- A regular-branch lower bound from the actual finite cutoff. Its three
scalar hypotheses are supplied by the tail-moment calculation. The
bin assignment, fresh residual, shared list experiment and tests are
constructed internally. -/
theorem no_good_test_of_regular_cut
    {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (hw : 0 < ∑ t : T, q (Sum.inr t))
    {e x τ ρ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hρ : ρ ≤ 1/64)
    (hfrozen : (∑ t ∈ Finset.univ.filter (fun t : T => τ ≤ q (Sum.inr t)),
      q (Sum.inr t)) ≤ ρ*x)
    (hlight : (n : ℝ) * Real.sqrt x *
      (∑ t ∈ Finset.univ.filter (fun t : T => q (Sum.inr t) < τ),
        q (Sum.inr t) * Real.sqrt (q (Sum.inr t))) ≤ ρ*x)
    (hgeom : 2*τ ≤ x/32)
    {weights : I → ℝ} (hweights : IsLaw weights)
    {alts : I → H ⊕ Unit → ℝ} (halts : ∀ i, IsLaw (alts i))
    (hdef : ∀ i, 0 < weights i →
      e - (∑ t : T, q (Sum.inr t)) + x < trueHeadDeficit q (alts i))
    (hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ 1/8) :
    ¬ ∃ f, GoodTest q e n f := by
  classical
  let light (t : T) := 0 < q (Sum.inr t) ∧ q (Sum.inr t) < τ
  obtain ⟨S, binT, hassign, hoccupied, hbounds, hsumTops⟩ :=
    exists_occupied_dyadic_bins (fun t : T => q (Sum.inr t)) light hτ
      (fun t h => ⟨h.1, h.2.le⟩)
  let u (j : S) := τ * (1/2 : ℝ)^j.val
  let bin : H ⊕ T → Option S := Sum.elim (fun _ => none) binT
  let b := CanonneNearOne.normalizedBinMass q 1 bin
  have hb (j : S) : 0 < b j := by
    obtain ⟨t, ht⟩ := hoccupied j
    have hqpos : 0 < q (Sum.inr t) := ((hassign t).2 (by simp [ht])).1
    unfold b CanonneNearOne.normalizedBinMass
    simp only [div_one]
    refine hqpos.trans_le ?_
    simpa only [bin, Sum.elim_inr, ht, ite_true] using
      (Finset.single_le_sum
        (f := fun a : H ⊕ T => if bin a = some j then q a else 0)
        (fun a _ => by split <;> first | exact hq.nonneg a | exact le_rfl)
        (Finset.mem_univ (Sum.inr t)))
  obtain ⟨fresh, hFresh, hsum, href, hscaled⟩ := exists_fresh_residual_ref hq bin hb
  let r := binConditional q bin
  have hr (j : S) : IsLaw (r j) := binConditional_isLaw hq bin j (hb j)
  have hrtop (j : S) (a : H ⊕ T) (hp : 0 < r j a) : q a ≤ u j := by
    have ha : bin a = some j := by
      by_contra hn
      simp [r, binConditional, hn] at hp
    cases a with
    | inl h => simp [bin] at ha
    | inr t => exact (hbounds t j ha).1
  let frozen := Finset.univ.filter (fun t : T => τ ≤ q (Sum.inr t))
  have hfrozenSupport (t : T) (ht : t ∉ frozen) :
      (1 - ∑ j, b j) * fresh (Sum.inr t) = 0 := by
    change (1 - ∑ j, CanonneNearOne.normalizedBinMass q 1 bin j) * fresh (Sum.inr t) = 0
    rw [hscaled]
    have ht' : q (Sum.inr t) < τ := lt_of_not_ge fun h => ht
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    by_cases hpos : 0 < q (Sum.inr t)
    · have hh := (hassign t).1 ⟨hpos, ht'⟩
      simp [residualOf, bin, hh]
    · have he : q (Sum.inr t) = 0 := le_antisymm (le_of_not_gt hpos) (hq.nonneg _)
      simp [residualOf, he]
  have hrawMoment :
      (∑ j, b j * Real.sqrt (u j)) ≤
        2 * (∑ t ∈ Finset.univ.filter (fun t : T => q (Sum.inr t) < τ),
          q (Sum.inr t) * Real.sqrt (q (Sum.inr t))) := by
    unfold b CanonneNearOne.normalizedBinMass
    simp only [div_one, Finset.sum_mul]
    rw [Finset.sum_comm, Fintype.sum_sum_type]
    simp only [bin, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, ite_false,
      zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro t _
    have hcase : binT t = none ∨ ∃ j, binT t = some j := by cases binT t <;> simp
    rcases hcase with ht | ⟨j, ht⟩
    · simp only [ht, reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero]
      split
      · exact mul_nonneg (by norm_num) (mul_nonneg (hq.nonneg _) (Real.sqrt_nonneg _))
      · norm_num
    · have hlt := ((hassign t).2 (by simp [ht])).2
      have hlo := (hbounds t j ht).2
      have hs : Real.sqrt (u j) ≤ 2*Real.sqrt (q (Sum.inr t)) := by
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
        rw [Real.sq_sqrt (by unfold u; positivity), mul_pow, Real.sq_sqrt (hq.nonneg _)]
        change u j ≤ (2 : ℝ)^2 * q (Sum.inr t)
        linarith [show u j ≤ 2*q (Sum.inr t) from hlo, hq.nonneg (Sum.inr t)]
      simp only [ht, Option.some.injEq, ite_eq_left hlt]
      rw [Finset.sum_eq_single j]
      · simp only [ite_true]
        nlinarith only [mul_le_mul_of_nonneg_left hs (hq.nonneg (Sum.inr t))]
      · intro j' _ hne
        simp [Ne.symm hne]
      · simp
  have hlightFull : (n : ℝ) * Real.sqrt x * (∑ j, b j * Real.sqrt (u j)) ≤ 2*ρ*x := by
    have hmul := mul_le_mul_of_nonneg_left hrawMoment
      (show 0 ≤ (n : ℝ) * Real.sqrt x by positivity)
    nlinarith only [hlight, hmul]
  exact no_good_test_of_regular_rounded_marker hn hq hFresh hw hb
    (fun j => by unfold u; positivity) hsum hr href
    (fun j h => by simp [r, binConditional, bin]) hrtop frozen hfrozenSupport
    hx hρ hfrozen hlightFull (hsumTops.trans hgeom) hweights halts hdef hprior

end Cut

end
end CanonneRegularTransfer
