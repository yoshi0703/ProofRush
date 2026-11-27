import NearOneBins

namespace CanonneNearOneTesting

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A]

/-- Tensorization of half-L1 TV for actual ordered IID laws. The common
pointwise mass gives a minorizing product law before normalization. -/
theorem ordered_product_tv_le (n : ℕ) {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    totalVariation (pilotLaw (I := Fin n) p) (pilotLaw q) ≤
      (n : ℝ) * totalVariation p q := by
  let o := ∑ a, min (p a) (q a)
  have hmin (a : A) : 0 ≤ min (p a) (q a) := le_min (hp.nonneg a) (hq.nonneg a)
  have ho : 0 ≤ o := Finset.sum_nonneg (fun a _ => hmin a)
  have hoverlap (z : Fin n → A) :
      (∏ i, min (p (z i)) (q (z i))) ≤ min (pilotLaw p z) (pilotLaw q z) := by
    apply le_min
    · exact Finset.prod_le_prod₀ (fun i _ => hmin (z i)) (fun _ _ => min_le_left _ _)
    · exact Finset.prod_le_prod₀ (fun i _ => hmin (z i)) (fun _ _ => min_le_right _ _)
  have hsum : o^n ≤ ∑ z : Fin n → A, min (pilotLaw p z) (pilotLaw q z) := by
    calc
      _ = ∏ _i : Fin n, ∑ a, min (p a) (q a) := by simp [o]
      _ = ∑ z : Fin n → A, ∏ i, min (p (z i)) (q (z i)) :=
        Fintype.prod_sum (fun (_ : Fin n) a => min (p a) (q a))
      _ ≤ _ := Finset.sum_le_sum (fun z _ => hoverlap z)
  change CanonneNearOne.totalVariation (pilotLaw (I := Fin n) p) (pilotLaw q) ≤
    (n : ℝ) * CanonneNearOne.totalVariation p q
  have hp' := pilotLaw_isLaw (I := Fin n) hp
  have hq' := pilotLaw_isLaw (I := Fin n) hq
  rw [CanonneNearOne.totalVariation_eq_one_sub_overlap
    (show CanonneNearOne.IsLaw _ from ⟨hp'.nonneg, hp'.total⟩)
    (show CanonneNearOne.IsLaw _ from ⟨hq'.nonneg, hq'.total⟩),
    CanonneNearOne.totalVariation_eq_one_sub_overlap
      (show CanonneNearOne.IsLaw _ from ⟨hp.nonneg, hp.total⟩)
      (show CanonneNearOne.IsLaw _ from ⟨hq.nonneg, hq.total⟩)]
  change 1 - _ ≤ (n : ℝ) * (1-o)
  have hBern := one_add_mul_sub_le_pow (show -1 ≤ o by linarith) n
  linarith

def interpolate (q p : A → ℝ) (t : ℝ) (a : A) : ℝ := (1-t)*q a + t*p a

theorem interpolate_isLaw {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsLaw (interpolate q p t) := by
  refine ⟨fun a => add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hq.nonneg a))
    (mul_nonneg ht (hp.nonneg a)), ?_⟩
  unfold interpolate
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq.total, hp.total]
  ring

theorem interpolated_tv {p q : A → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    totalVariation (interpolate q p t) q = t * totalVariation p q := by
  have hpoint (a : A) : interpolate q p t a - q a = t*(p a - q a) := by
    unfold interpolate
    ring
  simp only [totalVariation, hpoint, abs_mul, abs_of_nonneg ht, ← Finset.mul_sum]
  ring

theorem no_zero_sample_good_test {q : A → ℝ} {e : ℝ}
    (hnonempty : ∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q) :
    ¬ ∃ f, GoodTest q e 0 f := by
  obtain ⟨p, hp, hfar⟩ := hnonempty
  intro ⟨f, _, hnull, halt⟩
  have hsame : pilotLaw (I := Fin 0) p = pilotLaw q := by
    funext z
    simp [pilotLaw]
  have hupper := halt p hp hfar
  rw [hsame] at hupper
  linarith

/-- The universal 1/(3e) baseline at the exact strict radius. When a
test exists, interpolation may choose a strictly far law arbitrarily
close to the testing radius. -/
theorem good_test_radius_budget {q : A → ℝ} (hq : IsLaw q) {e : ℝ} (he : 0 ≤ e)
    (hnonempty : ∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q)
    {n : ℕ} (htest : ∃ f, GoodTest q e n f) :
    (1 : ℝ)/3 ≤ (n : ℝ)*e := by
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := Nat.eq_zero_of_not_pos h
    exact no_zero_sample_good_test hnonempty (hz ▸ htest)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨p, hp, hfar⟩ := hnonempty
  let d := totalVariation p q
  have hd : 0 < d := he.trans_lt hfar
  by_contra hb
  have htight : e < 1/(3*(n : ℝ)) := by
    apply (lt_div_iff₀ (show 0 < 3*(n : ℝ) by positivity)).mpr
    nlinarith only [lt_of_not_ge hb]
  let s := (e+min d (1/(3*(n : ℝ))))/2
  have hs : e < s := by
    have h := lt_min hfar htight
    change e < d at hfar
    change e < min d (1/(3*(n : ℝ))) at h
    unfold s
    linarith
  have hsd : s ≤ d := by
    have h := min_le_left d (1/(3*(n : ℝ)))
    unfold s
    linarith [show e < d from hfar]
  have hsB : s < 1/(3*(n : ℝ)) := by
    have h := min_le_right d (1/(3*(n : ℝ)))
    unfold s
    linarith
  let t := s/d
  have ht : 0 ≤ t := div_nonneg (he.trans hs.le) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr hsd
  let p' := interpolate q p t
  have hp' : IsLaw p' := interpolate_isLaw hp hq ht ht1
  have heq : totalVariation p' q = s := by
    rw [interpolated_tv ht]
    change s / d * d = s
    exact div_mul_cancel₀ _ hd.ne'
  obtain ⟨f, hf, hnull, halt⟩ := htest
  have h1 := rejection_sub_le_tv (pilotLaw_isLaw (I := Fin n) hp') (pilotLaw_isLaw hq) hf
  rw [tv_comm] at h1
  have h2 := ordered_product_tv_le n hp' hq
  rw [heq] at h2
  have h3 := halt p' hp' (heq.symm ▸ hs)
  have h4 : (n : ℝ)*s < 1/3 := by
    have hh := (lt_div_iff₀ (show 0 < 3*(n : ℝ) by positivity)).mp hsB
    nlinarith only [hh]
  linarith


theorem good_test_samples_ge_inverse_radius {q : A → ℝ} (hq : IsLaw q) {e : ℝ} (he : 0 < e)
    (hnonempty : ∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q)
    {n : ℕ} (htest : ∃ f, GoodTest q e n f) :
    1/(3*e) ≤ (n:ℝ) := by
  apply (div_le_iff₀ (show 0 < 3*e by positivity)).mpr
  nlinarith only [good_test_radius_budget hq he.le hnonempty htest]

section MoreRecords

variable [DecidableEq A]

theorem product_marginal_at_injective_records {m n : ℕ} {q : A → ℝ} (hq : IsLaw q)
    (f : Fin m → Fin n) (hinj : Function.Injective f) :
    coarsen (fun z : Fin n → A => z ∘ f) (pilotLaw q) = pilotLaw q := by
  classical
  funext y
  rw [coarsen_eventMass]
  rw [eventMass_congr _ (show ∀ z : Fin n → A, z ∘ f = y ↔ ∀ i, z (f i) = y i from
    fun z => ⟨fun h i => congrFun h i, funext⟩)]
  exact independent_draws_at_injective_keys
    (r := fun (_ : Fin n) => q) (fun _ => hq) f hinj y

theorem rejection_coarsen {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (φ : X → Y) (p : X → ℝ) (g : Y → ℝ) :
    rejection (coarsen φ p) g = rejection p (g ∘ φ) := by
  classical
  unfold rejection coarsen
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (φ x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- Fixed-budget tests remain valid by discarding the later records. -/
theorem good_test_budget_monotone {q : A → ℝ} (hq : IsLaw q) {e : ℝ} {m n : ℕ}
    (hmn : m ≤ n) (htest : ∃ f, GoodTest q e m f) :
    ∃ f, GoodTest q e n f := by
  obtain ⟨f, hf, hnull, halt⟩ := htest
  let φ (z : Fin n → A) : Fin m → A := z ∘ Fin.castLE hmn
  have heq {p : A → ℝ} (hp : IsLaw p) :
      rejection (pilotLaw (I := Fin n) p) (f ∘ φ) = rejection (pilotLaw (I := Fin m) p) f := by
    rw [← rejection_coarsen]
    rw [product_marginal_at_injective_records hp _ (Fin.castLE_injective hmn)]
  exact ⟨f ∘ φ, fun z => hf (φ z), (heq hq).symm ▸ hnull,
    fun p hp hfar => (heq hp).symm ▸ halt p hp hfar⟩

end MoreRecords

end
end CanonneNearOneTesting
