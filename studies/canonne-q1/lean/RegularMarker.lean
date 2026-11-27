import RegularPilot

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- Pool only the tail into a marker. Every head label remains distinct. -/
def collapsed (q : H ⊕ T → ℝ) : H ⊕ Unit → ℝ :=
  Sum.elim (fun h => q (Sum.inl h)) (fun _ => ∑ t : T, q (Sum.inr t))

omit [DecidableEq H] [DecidableEq T] in
theorem collapsed_isLaw {q : H ⊕ T → ℝ} (hq : IsLaw q) : IsLaw (collapsed q) := by
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | inl h => exact hq.nonneg _
    | inr _ => exact Finset.sum_nonneg fun t _ => hq.nonneg _
  · simpa [collapsed, Fintype.sum_sum_type] using hq.total

/-- Keep each head label literally; only marker labels use the supplied tail law. -/
def markerChannel (tail : T → ℝ) : H ⊕ Unit → H ⊕ T → ℝ
  | Sum.inl h => pointLaw (Sum.inl h)
  | Sum.inr _ => Sum.elim (fun _ => 0) tail

theorem markerChannel_isLaw {tail : T → ℝ} (htail : IsLaw tail) (a : H ⊕ Unit) :
    IsLaw (markerChannel tail a) := by
  cases a with
  | inl h => exact pointLaw_isLaw (Sum.inl h)
  | inr _ =>
    refine ⟨?_, ?_⟩
    · intro out
      cases out with
      | inl _ => exact le_rfl
      | inr t => exact htail.nonneg t
    · simp [markerChannel, Fintype.sum_sum_type, htail.total]

omit [Fintype T] in
theorem marker_fill_head (p : H ⊕ Unit → ℝ) (tail : T → ℝ) (h : H) :
    mixLaw p (markerChannel tail) (Sum.inl h) = p (Sum.inl h) := by
  simp [mixLaw, markerChannel, pointLaw, Fintype.sum_sum_type]

omit [Fintype T] in
theorem marker_fill_tail (p : H ⊕ Unit → ℝ) (tail : T → ℝ) (t : T) :
    mixLaw p (markerChannel tail) (Sum.inr t) = p (Sum.inr ()) * tail t := by
  simp [mixLaw, markerChannel, pointLaw, Fintype.sum_sum_type]

def trueHeadDeficit (q : H ⊕ T → ℝ) (p : H ⊕ Unit → ℝ) : ℝ :=
  ∑ h : H, max (q (Sum.inl h) - p (Sum.inl h)) 0

theorem strict_far_from_marker_fill {q : H ⊕ T → ℝ} (hq : IsLaw q)
    {p : H ⊕ Unit → ℝ} (hp : IsLaw p) {tail : T → ℝ} (htail : IsLaw tail)
    {e x : ℝ} (hdef : e - (∑ t : T, q (Sum.inr t)) + x < trueHeadDeficit q p)
    (hoverlap : ∑ t : T, min (mixLaw p (markerChannel tail) (Sum.inr t)) (q (Sum.inr t)) ≤ x) :
    e < totalVariation (mixLaw p (markerChannel tail)) q := by
  classical
  let B := Finset.univ.image (Sum.inr : T → H ⊕ T)
  have hb :
      Bᶜ = Finset.univ.image (Sum.inl : H → H ⊕ T) := by
    ext a
    cases a <;> simp [B]
  have hpfull := mixLaw_isLaw hp (markerChannel tail) (markerChannel_isLaw htail)
  rw [totalVariation_eq_suffix_mass_add_deficit_sub_overlap hpfull hq B, hb]
  have hmass : mass q B = ∑ t : T, q (Sum.inr t) := by
    unfold mass B
    rw [Finset.sum_image Sum.inr_injective.injOn]
  have hov : overlap (mixLaw p (markerChannel tail)) q B =
      ∑ t : T, min (mixLaw p (markerChannel tail) (Sum.inr t)) (q (Sum.inr t)) := by
    unfold overlap B
    rw [Finset.sum_image Sum.inr_injective.injOn]
  have hd : deficit (mixLaw p (markerChannel tail)) q
      (Finset.univ.image (Sum.inl : H → H ⊕ T)) = trueHeadDeficit q p := by
    unfold deficit trueHeadDeficit
    rw [Finset.sum_image Sum.inl_injective.injOn]
    simp only [marker_fill_head]
  rw [hmass, hov, hd]
  linarith

section RegularFill

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Normalize the marked part of a filled law. The fallback at an
impossible tape keeps the channel stochastic on its whole domain. -/
def normalizeMarker (q η : H ⊕ T → ℝ) : T → ℝ :=
  if (∑ t : T, η (Sum.inr t)) = ∑ t : T, q (Sum.inr t) then
    fun t => η (Sum.inr t) / ∑ j : T, q (Sum.inr j)
  else fun t => q (Sum.inr t) / ∑ j : T, q (Sum.inr j)

omit [DecidableEq H] [DecidableEq T] in
theorem normalizeMarker_isLaw {q η : H ⊕ T → ℝ} (hq : IsLaw q) (hη : IsLaw η)
    (hw : 0 < ∑ t : T, q (Sum.inr t)) : IsLaw (normalizeMarker q η) := by
  unfold normalizeMarker
  split
  · rename_i he
    refine ⟨fun t => div_nonneg (hη.nonneg _) hw.le, ?_⟩
    rw [← Finset.sum_div, he, div_self hw.ne']
  · refine ⟨fun t => div_nonneg (hq.nonneg _) hw.le, ?_⟩
    rw [← Finset.sum_div, div_self hw.ne']

theorem qred_fills_to_η {q η : H ⊕ T → ℝ} (hq : IsLaw q) (hη : IsLaw η)
    (hw : 0 < ∑ t : T, q (Sum.inr t)) (hhead : ∀ h, η (Sum.inl h) = q (Sum.inl h)) :
    mixLaw (collapsed q) (markerChannel (normalizeMarker q η)) = η := by
  have htotal := hη.total
  have hqtotal := hq.total
  rw [Fintype.sum_sum_type] at htotal hqtotal
  simp only [hhead] at htotal
  have htail : (∑ t : T, η (Sum.inr t)) = ∑ t : T, q (Sum.inr t) := by linarith
  funext a
  cases a with
  | inl h => simpa only [marker_fill_head, collapsed, Sum.elim_inl] using (hhead h).symm
  | inr t =>
    simp only [marker_fill_tail, collapsed, Sum.elim_inr, normalizeMarker, ite_eq_left htail]
    exact mul_div_cancel₀ _ hw.ne'

/-- A colored fill eligible for the regular lower bound. The zero-mass
condition for the fresh residual is imposed only outside its prescribed
frozen support, so it also covers the case of no frozen tail labels. -/
theorem no_good_test_of_regular_colored_marker
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] {n : ℕ}
    {q fresh : H ⊕ T → ℝ} (hq : IsLaw q) (hfresh : IsLaw fresh)
    (hw : 0 < ∑ t : T, q (Sum.inr t))
    {b u : B → ℝ} {k : B → ℕ} {r : B → H ⊕ T → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hk : ∀ j, 0 < k j) (hbsum : ∑ j, b j ≤ 1)
    (hr : ∀ j, IsLaw (r j))
    (href : q = bandedLabel b fresh r)
    (hrhead : ∀ j h, r j (Sum.inl h) = 0)
    (hrtop : ∀ j a, 0 < r j a → q a ≤ u j)
    (frozen : Finset T)
    (hfrozen : ∀ t ∉ frozen, (1 - ∑ j, b j) * fresh (Sum.inr t) = 0)
    {e x priorround : ℝ}
    (hbudget : (∑ t ∈ frozen, q (Sum.inr t)) + (∑ j, (k j : ℝ) * u j) ≤ x)
    {weights : I → ℝ} (hweights : IsLaw weights)
    {alts : I → H ⊕ Unit → ℝ} (halts : ∀ i, IsLaw (alts i))
    (hdef : ∀ i, 0 < weights i →
      e - (∑ t : T, q (Sum.inr t)) + x < trueHeadDeficit q (alts i))
    (hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ priorround)
    (hgap : (n.choose 2 : ℝ) * (∑ j, (b j)^2/k j) + priorround < 1/3) :
    ¬ ∃ f, GoodTest q e n f := by
  classical
  let key := coloredLatent k b
  have hkey : IsLaw key := coloredLatent_isLaw hk hb hbsum
  let pilotLawAt : Slot k → H ⊕ T → ℝ := fun j => r j.1
  let tape := independentLaw pilotLawAt
  have htape : IsLaw tape := independentLaw_isLaw (fun j => hr j.1)
  let η := freshSlotLabel key fresh
  have hη (z : Slot k → H ⊕ T) : IsLaw (η z) :=
    mixLaw_isLaw hkey _ (fun a => by cases a <;> first | exact hfresh | exact pointLaw_isLaw _)
  let K (z : Slot k → H ⊕ T) : (H ⊕ Unit) → H ⊕ T → ℝ :=
    markerChannel (normalizeMarker q (η z))
  have hK (z : Slot k → H ⊕ T) (a : H ⊕ Unit) : IsLaw (K z a) :=
    markerChannel_isLaw (normalizeMarker_isLaw hq (hη z) hw) a
  have htapeSlot (z : Slot k → H ⊕ T) (hz : 0 < tape z) (j : Slot k) : 0 < r j.1 (z j) := by
    by_contra hnot
    have hzero : r j.1 (z j) = 0 := le_antisymm (le_of_not_gt hnot) ((hr j.1).nonneg _)
    have : tape z = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hzero
    linarith
  have hhead (z : Slot k → H ⊕ T) (hz : 0 < tape z) (h : H) :
      η z (Sum.inl h) = q (Sum.inl h) := by
    have hnopot (j : Slot k) : z j ≠ Sum.inl h := by
      intro hj
      have hzj := htapeSlot z hz j
      rw [hj, hrhead] at hzj
      linarith
    have hqhead : q (Sum.inl h) = (1 - ∑ j, b j) * fresh (Sum.inl h) := by
      rw [href]
      simp [bandedLabel, hrhead]
    simp [η, freshSlotLabel_apply, key, coloredLatent, pointLaw, hnopot, hqhead]
  have hNullPred :
      mixLaw tape (fun z => pilotLaw (I := Fin n) (mixLaw (collapsed q) (K z))) =
      sharedSample (n := n) key fresh pilotLawAt := by
    rw [sharedSample_eq_mixture_with_fresh key hfresh pilotLawAt]
    funext y
    unfold mixLaw
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : 0 < tape z
    · have he := qred_fills_to_η hq (hη z) hw (hhead z hz)
      change tape z * pilotLaw (mixLaw (collapsed q) (markerChannel (normalizeMarker q (η z)))) y =
        tape z * pilotLaw (η z) y
      rw [he]
    · have hzero := (htape.nonneg z).antisymm' (le_of_not_gt hz)
      change tape z * _ = tape z * _
      simp [hzero]
  have hNullTV :
      totalVariation (mixLaw tape (fun z => pilotLaw (I := Fin n) (mixLaw (collapsed q) (K z))))
        (pilotLaw q) ≤ (n.choose 2 : ℝ) * ∑ j, (b j)^2/k j := by
    rw [hNullPred]
    have hc := colored_iid_tv (n := n) hk hb hbsum hfresh hr
    rwa [← href] at hc
  refine no_good_test_of_common_channel hq (collapsed_isLaw hq) hweights halts htape hK
    hgap hNullTV hprior ?_
  intro i z hi hz
  have hsumtail : (∑ t : T, η z (Sum.inr t)) = ∑ t : T, q (Sum.inr t) := by
    have hs := (hη z).total
    have hqsum := hq.total
    rw [Fintype.sum_sum_type] at hs hqsum
    simp only [hhead z hz] at hs
    linarith
  apply strict_far_from_marker_fill hq (halts i) (normalizeMarker_isLaw hq (hη z) hw) (hdef i hi)
  let used := Finset.univ.image z
  have hused :
      CanonneNearOne.mass q used ≤ ∑ j, (k j : ℝ) * u j :=
    CanonneNearOne.support_mass_le_slot_cost ⟨hq.nonneg, hq.total⟩ z
      (fun j => hrtop j.1 (z j) (htapeSlot z hz j))
  have hpoint (t : T) : min (mixLaw (alts i) (K z) (Sum.inr t)) (q (Sum.inr t)) ≤
      (if t ∈ frozen then q (Sum.inr t) else 0) +
      (if Sum.inr t ∈ used then q (Sum.inr t) else 0) := by
    by_cases hf : t ∈ frozen
    · rw [ite_eq_left hf]
      have hn : 0 ≤ (if Sum.inr t ∈ used then q (Sum.inr t) else 0) := by
        split <;> first | exact le_rfl | exact hq.nonneg _
      linarith [min_le_right (mixLaw (alts i) (K z) (Sum.inr t)) (q (Sum.inr t))]
    · rw [ite_eq_right hf, zero_add]
      by_cases hu : Sum.inr t ∈ used
      · rw [ite_eq_left hu]
        exact min_le_right _ _
      · have hneq (j : Slot k) : z j ≠ Sum.inr t := fun he =>
          hu (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he⟩)
        have hzero : η z (Sum.inr t) = 0 := by
          simp [η, freshSlotLabel_apply, key, coloredLatent, pointLaw, hneq, hfrozen t hf]
        simp [hu, K, marker_fill_tail, normalizeMarker, hsumtail, hzero, hq.nonneg _]
  have hbudgetUsed :
      (∑ t : T, if Sum.inr t ∈ used then q (Sum.inr t) else 0) ≤
      CanonneNearOne.mass q used := by
    rw [← Finset.sum_filter]
    let f : T → H ⊕ T := Sum.inr
    have hsub : (Finset.univ.filter (fun t : T => f t ∈ used)).image f ⊆ used := by
      intro a ha
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp ht).2
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hq.nonneg a)
    rw [Finset.sum_image Sum.inr_injective.injOn] at hle
    exact hle
  change (∑ t : T, min (mixLaw (alts i) (K z) (Sum.inr t)) (q (Sum.inr t))) ≤ x
  have hFilter : (Finset.univ.filter (fun t : T => t ∈ frozen)) = frozen := by ext; simp
  have hsumFrozen : (∑ t : T, if t ∈ frozen then q (Sum.inr t) else 0) =
      ∑ t ∈ frozen, q (Sum.inr t) := by rw [← Finset.sum_filter, hFilter]
  calc
    _ ≤ ∑ t : T, ((if t ∈ frozen then q (Sum.inr t) else 0) +
          (if Sum.inr t ∈ used then q (Sum.inr t) else 0)) :=
      Finset.sum_le_sum (fun t _ => hpoint t)
    _ ≤ (∑ t ∈ frozen, q (Sum.inr t)) + ∑ j, (k j : ℝ) * u j := by
      rw [Finset.sum_add_distrib, hsumFrozen]
      exact add_le_add_right (hbudgetUsed.trans hused) _
    _ ≤ _ := hbudget

end RegularFill

end
end CanonneRegularTransfer
