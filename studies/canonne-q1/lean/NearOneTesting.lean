import NearOne
import AuditTruncated
import Mathlib.Data.Nat.Choose.Bounds

namespace CanonneNearOneTesting

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The rejection probability of a scalar randomized test. Outcomes remain
ordered; no histogram or deterministic-test reduction is assumed. -/
def rejection {X : Type*} [Fintype X] (p f : X → ℝ) : ℝ := ∑ x, p x * f x

/-- A test has separate one-third errors at the exact strict radius. -/
def GoodTest (q : A → ℝ) (e : ℝ) (n : ℕ) (f : (Fin n → A) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
  rejection (pilotLaw q) f ≤ 1 / 3 ∧
  ∀ p : A → ℝ, IsLaw p → e < totalVariation p q →
    2 / 3 ≤ rejection (pilotLaw p) f

theorem rejection_sub_le_tv {X : Type*} [Fintype X] {p q f : X → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    rejection p f - rejection q f ≤ totalVariation q p := by
  rw [totalVariation_eq_deficit hq hp]
  unfold rejection deficit
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul]
  rcases le_total (p x) (q x) with hl | hr
  · rw [max_eq_right (sub_nonpos.mpr hl)]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl) (hf x).1
  · rw [max_eq_left (sub_nonneg.mpr hr)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf x).2 (sub_nonneg.mpr hr)

theorem tv_comm {X : Type*} [Fintype X] (p q : X → ℝ) :
    totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem mixLaw_isLaw {X Y : Type*} [Fintype X] [Fintype Y] {p : X → ℝ}
    (hp : IsLaw p) (f : X → Y → ℝ) (hf : ∀ x, IsLaw (f x)) :
    IsLaw (mixLaw p f) := by
  refine ⟨fun y => Finset.sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) ((hf x).nonneg y), ?_⟩
  unfold mixLaw
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, (hf _).total, mul_one, hp.total]

theorem rejection_mix {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → ℝ) (laws : X → Y → ℝ) (f : Y → ℝ) :
    rejection (mixLaw p laws) f = ∑ x, p x * rejection (laws x) f := by
  unfold rejection mixLaw
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [DecidableEq A] in
/-- Product TV for one-sided pointwise minorization. This applies to the null
after conditioning on all observations avoiding the discarded labels. -/
theorem product_tv_le_minorized {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {R : ℝ} (hR : 0 ≤ R) (hRone : R ≤ 1) (hminor : ∀ a, (1-R) * p a ≤ q a)
    (n : ℕ) :
    totalVariation (pilotLaw (I := Fin n) p) (pilotLaw q) ≤ (n : ℝ) * R := by
  have hp' := pilotLaw_isLaw (I := Fin n) hp
  have hq' := pilotLaw_isLaw (I := Fin n) hq
  have hoverlap : (1-R)^n ≤ ∑ x : Fin n → A, min (pilotLaw p x) (pilotLaw q x) := by
    calc
      _ = ∑ x : Fin n → A, (1-R)^n * pilotLaw p x := by
        rw [← Finset.mul_sum, hp'.total, mul_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x _
        apply le_min
        · apply mul_le_of_le_one_left (hp'.nonneg x)
          exact pow_le_one₀ (sub_nonneg.mpr hRone) (sub_le_self _ hR)
        · unfold pilotLaw
          have hprod : (∏ i : Fin n, (1-R) * p (x i)) ≤ ∏ i : Fin n, q (x i) :=
            Finset.prod_le_prod₀ (fun i _ => mul_nonneg (sub_nonneg.mpr hRone) (hp.nonneg (x i)))
              (fun i _ => hminor (x i))
          simpa [Finset.prod_mul_distrib] using hprod
  change CanonneNearOne.totalVariation (pilotLaw p) (pilotLaw q) ≤ (n : ℝ) * R
  rw [CanonneNearOne.totalVariation_eq_one_sub_overlap
    (show CanonneNearOne.IsLaw _ from ⟨hp'.nonneg, hp'.total⟩)
    (show CanonneNearOne.IsLaw _ from ⟨hq'.nonneg, hq'.total⟩)]
  have hBern := one_add_mul_le_pow (a := -R) (by linarith) n
  rw [← sub_eq_add_neg] at hBern
  nlinarith

section OrderedMixture

variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

/-- Conditional on all shared labels, each ordered observation independently
draws one slot. The fresh variables used by the underlying coupling have
zero selection probability in the all-active construction. -/
def fixedListLabel [NeZero n] (p : Option J → ℝ) (z : (J ⊕ Fin n) → A) : A → ℝ :=
  coarsen (fun x : Option J => x.elim (z (Sum.inr 0)) (fun j => z (Sum.inl j))) p

/-- A direct coefficient proof that every emitted n-sample law is a mixture of
IID laws once the mask assigns total mass one to the active labels. -/
theorem sharedSample_eq_ordered_mixture [NeZero n] {p : Option J → ℝ}
    (p0 : p none = 0) (fresh : A → ℝ) (r : J → A → ℝ) :
    sharedSample (n := n) p fresh r =
      mixLaw (independentLaw (byKey (n := n) fresh r)) (fun z => pilotLaw (fixedListLabel p z)) := by
  classical
  funext y
  unfold sharedSample mixLaw
  simp only [coarsen, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have point (x : Fin n → Option J) :
      (fun i => z (selectKey x i)) = y ↔ ∀ i, z (selectKey x i) = y i :=
    ⟨fun h i => congrFun h i, funext⟩
  have swap (x : Fin n → Option J) :
      pilotLaw p x *
        (if (fun i => z (selectKey x i)) = y then independentLaw (byKey (n := n) fresh r) z else 0) =
      independentLaw (byKey (n := n) fresh r) z *
        (if ∀ i, z (selectKey x i) = y i then pilotLaw p x else 0) := by
    by_cases h : ∀ i, z (selectKey x i) = y i
    · rw [ite_eq_left ((point x).2 h), ite_eq_left h]
      ring
    · rw [ite_eq_right (fun hh => h ((point x).1 hh)), ite_eq_right h]
      ring
  simp_rw [swap, ← Finset.mul_sum]
  apply congrArg (fun v => independentLaw (byKey (n := n) fresh r) z * v)
  rw [← eventMass_eq_sum]
  change eventMass (pilotLaw p) (fun x : Fin n → Option J =>
    ∀ i, z ((x i).elim (Sum.inr i) Sum.inl) = y i) = _
  rw [product_event_coordinates p (fun i x => z (x.elim (Sum.inr i) Sum.inl) = y i)]
  unfold pilotLaw fixedListLabel
  apply Finset.prod_congr rfl
  intro i _
  unfold coarsen
  rw [eventMass_eq_sum, Finset.sum_filter, Fintype.sum_option, Fintype.sum_option]
  simp [p0]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : z (Sum.inl j) = y i <;> simp [h]

omit [DecidableEq J] in
theorem fixedListLabel_isLaw [NeZero n] {p : Option J → ℝ} (hp : IsLaw p)
    (z : (J ⊕ Fin n) → A) : IsLaw (fixedListLabel p z) := coarsen_isLaw _ hp

omit [Fintype A] [DecidableEq J] in
theorem fixedListLabel_vanishes [NeZero n] {p : Option J → ℝ} (p0 : p none = 0)
    (z : (J ⊕ Fin n) → A) (a : A)
    (ha : a ∉ Finset.univ.image (fun j : J => z (Sum.inl j))) :
    fixedListLabel p z a = 0 := by
  unfold fixedListLabel coarsen
  rw [Finset.sum_filter, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, p0, ite_self, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  have hne : z (Sum.inl j) ≠ a := fun h => ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩)
  simp [hne]

end OrderedMixture

section Partition

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Each bin conditions a probability law on its fiber of the assignment. -/
def binConditional (p : A → ℝ) (bin : A → Option B) (j : B) (a : A) : ℝ :=
  if bin a = some j then p a / CanonneNearOne.normalizedBinMass p 1 bin j else 0

omit [DecidableEq A] [Fintype B] in
theorem binConditional_isLaw {p : A → ℝ} (hp : IsLaw p) (bin : A → Option B) (j : B)
    (hb : 0 < CanonneNearOne.normalizedBinMass p 1 bin j) :
    IsLaw (binConditional p bin j) := by
  refine ⟨?_, ?_⟩
  · intro a
    unfold binConditional
    split
    · exact div_nonneg (hp.nonneg a) hb.le
    · exact le_rfl
  · have hfactor (a : A) :
        (if bin a = some j then p a / CanonneNearOne.normalizedBinMass p 1 bin j else 0) =
        (if bin a = some j then p a else 0) *
          (CanonneNearOne.normalizedBinMass p 1 bin j)⁻¹ := by
        by_cases h : bin a = some j <;> simp [h, div_eq_mul_inv]
    simp only [binConditional, hfactor, ← Finset.sum_mul]
    have hmass : (∑ a, if bin a = some j then p a else 0) =
        CanonneNearOne.normalizedBinMass p 1 bin j := by
      simp only [CanonneNearOne.normalizedBinMass, div_one]
    rw [hmass, mul_inv_cancel₀ hb.ne']

omit [DecidableEq A] in
theorem normalized_mass_by_bin {p : A → ℝ} (bin : A → Option B)
    (hcover : ∀ a, bin a = none → p a = 0) :
    (∑ j, CanonneNearOne.normalizedBinMass p 1 bin j) = ∑ a, p a := by
  unfold CanonneNearOne.normalizedBinMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  cases hg : bin a with
  | none => simp [hcover a hg]
  | some j => simp

omit [DecidableEq A] in
theorem all_active_bandedLabel {p : A → ℝ} (hp : IsLaw p) (bin : A → Option B)
    (hcover : ∀ a, bin a = none → p a = 0)
    (hb : ∀ j, 0 < CanonneNearOne.normalizedBinMass p 1 bin j) :
    bandedLabel (CanonneNearOne.normalizedBinMass p 1 bin) p (binConditional p bin) = p := by
  funext a
  simp only [bandedLabel, normalized_mass_by_bin bin hcover, hp.total, sub_self, zero_mul, zero_add]
  have hterm (j : B) :
      CanonneNearOne.normalizedBinMass p 1 bin j * binConditional p bin j a =
        if bin a = some j then p a else 0 := by
    unfold binConditional
    split
    · exact mul_div_cancel₀ _ (hb j).ne'
    · simp
  simp only [hterm]
  cases hg : bin a with
  | none => simp [hcover a hg]
  | some j => simp

/-- The finite statistical lower bound at the exact strict radius, once a
cover by finite active bins has been supplied. There is no testing or
probabilistic assumption on the bins. -/
theorem no_good_test_of_dyadic_bins {q : A → ℝ} (hq : IsLaw q)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : (n : ℝ) * CanonneNearOne.nearOneMoment q δ ≤ 1/64)
    (bin : A → Option B) (u : B → ℝ) (hu : ∀ j, 0 < u j)
    (hcover : ∀ a, 0 < q a → q a ≤ δ / 16 → bin a ≠ none)
    (hnonempty : ∀ j, ∃ a, bin a = some j)
    (hupper : ∀ a j, bin a = some j → q a ≤ u j)
    (hlower : ∀ a j, bin a = some j → u j ≤ 2 * q a)
    (hlight : ∀ a j, bin a = some j → q a ≤ δ / 16)
    (hgeom : ∑ j, u j ≤ δ / 8) :
    ¬ ∃ f, GoodTest q (1 - δ) n f := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let H : Finset A := Finset.univ.filter (fun a => δ / 16 < q a)
  let R := CanonneNearOne.mass q H
  let Q := CanonneNearOne.discard q H
  have hqN : CanonneNearOne.IsLaw q := ⟨hq.nonneg, hq.total⟩
  have hR : 0 ≤ R := Finset.sum_nonneg fun a _ => hq.nonneg a
  have hheavy : R ≤ 4 * CanonneNearOne.nearOneMoment q δ :=
    CanonneNearOne.heavy_mass_le_four_moment hqN hδ
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ : 0 ≤ CanonneNearOne.nearOneMoment q δ := by linarith
  have hJbound : CanonneNearOne.nearOneMoment q δ ≤ 1/64 :=
    (le_mul_of_one_le_left hJ hn').trans hsmall
  have hRsmall : R ≤ 1/16 := by linarith
  have hret : 1/2 ≤ 1-R := by linarith
  have hQN : CanonneNearOne.IsLaw Q :=
    (CanonneNearOne.discard_law_and_exact_tv hqN H (show R < 1 by linarith)).1
  have hQ : IsLaw Q := ⟨hQN.nonneg, hQN.total⟩
  have hQmin (a : A) : (1-R) * Q a ≤ q a := by
    change (1-R) * (if a ∈ H then 0 else q a / (1-R)) ≤ q a
    split
    · simpa only [mul_zero] using hq.nonneg a
    · rw [mul_div_cancel₀ _ (show 1-R ≠ 0 by linarith)]
  have hTVdiscard : totalVariation (pilotLaw (I := Fin n) Q) (pilotLaw q) ≤ 1/16 := by
    refine (product_tv_le_minorized hQ hq hR (by linarith) hQmin n).trans ?_
    nlinarith only [mul_le_mul_of_nonneg_left hheavy (show (0 : ℝ) ≤ n by positivity), hsmall]
  have hQnone (a : A) (ha : bin a = none) : Q a = 0 := by
    by_cases hh : a ∈ H
    · simp [Q, CanonneNearOne.discard, hh]
    · have hsmallq : q a ≤ δ / 16 := by
        exact le_of_not_gt fun hg => hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)
      have hzero : q a = 0 := (hq.nonneg a).antisymm' (le_of_not_gt fun hp => hcover a hp hsmallq ha)
      simp [Q, CanonneNearOne.discard, hh, hzero]
  let b := CanonneNearOne.normalizedBinMass q (1-R) bin
  have hb_eq (j : B) : b j = CanonneNearOne.normalizedBinMass Q 1 bin j := by
    unfold b CanonneNearOne.normalizedBinMass
    apply Finset.sum_congr rfl
    intro a _
    by_cases hh : bin a = some j
    · have ha : a ∉ H := fun ha => (not_lt_of_ge (hlight a j hh)) (Finset.mem_filter.mp ha).2
      simp [hh, Q, CanonneNearOne.discard, ha, R]
    · simp [hh]
  have hb (j : B) : 0 < b j := by
    obtain ⟨a, ha⟩ := hnonempty j
    have hpos : 0 < q a := by linarith [hu j, hlower a j ha]
    have hkeep : 0 < q a / (1-R) := div_pos hpos (by linarith)
    unfold b CanonneNearOne.normalizedBinMass
    refine hkeep.trans_le ?_
    simpa only [ha, ite_true] using
      (Finset.single_le_sum
        (f := fun x => if bin x = some j then q x / (1-R) else 0)
        (fun x _ => by
          split
          · exact div_nonneg (hq.nonneg x) (by linarith)
          · exact le_rfl) (Finset.mem_univ a))
  have hbsum : ∑ j, b j = 1 := by
    simp only [hb_eq, normalized_mass_by_bin bin hQnone, hQ.total]
  let r := binConditional Q bin
  have hr (j : B) : IsLaw (r j) := binConditional_isLaw hQ bin j ((hb_eq j) ▸ hb j)
  let c := (n : ℝ) * Real.sqrt δ
  have hc : 0 < c := mul_pos (by exact_mod_cast hn) (Real.sqrt_pos.2 hδ)
  let k (j : B) : ℕ := CanonneColoredPilot.pilotCount c (b j) (u j)
  have hk (j : B) : 0 < k j := CanonneColoredPilot.pilotCount_pos hc (hb j) (hu j)
  let key := coloredLatent k b
  have hkey : IsLaw key := coloredLatent_isLaw hk (fun j => (hb j).le) hbsum.le
  have hkey0 : key none = 0 := by simp [key, coloredLatent, hbsum]
  have hqBand : bandedLabel b Q r = Q := by
    rw [show b = CanonneNearOne.normalizedBinMass Q 1 bin from funext hb_eq]
    exact all_active_bandedLabel hQ bin hQnone (fun j => (hb_eq j) ▸ hb j)
  let M := ∑ j, b j * Real.sqrt (u j)
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => mul_nonneg (hb j).le (Real.sqrt_nonneg _)
  have hMbound : Real.sqrt δ * M ≤ 4 * δ * CanonneNearOne.nearOneMoment q δ :=
    CanonneNearOne.normalized_light_charge_le hqN hδ hret bin u hu
      (fun a j h => by linarith [hlight a j h]) hlower
  have hcollision : (n.choose 2 : ℝ) * (M / c) ≤ 1/16 := by
    have hcast : (n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by
      exact_mod_cast Nat.choose_le_pow n 2
    have hsqrtpos := Real.sqrt_pos.2 hδ
    have heq : (n : ℝ)^2 * (M / c) =
        (n : ℝ) / δ * (Real.sqrt δ * M) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      change (n : ℝ)^2 * (M / ((n : ℝ) * Real.sqrt δ)) = (n : ℝ) / δ * (Real.sqrt δ * M)
      field_simp
      nlinarith [Real.sq_sqrt hδ.le]
    calc
      _ ≤ (n : ℝ)^2 * (M / c) := mul_le_mul_of_nonneg_right hcast (div_nonneg hM hc.le)
      _ = (n : ℝ) / δ * (Real.sqrt δ * M) := heq
      _ ≤ (n : ℝ) / δ * (4 * δ * CanonneNearOne.nearOneMoment q δ) :=
        mul_le_mul_of_nonneg_left hMbound (by positivity)
      _ = 4 * ((n : ℝ) * CanonneNearOne.nearOneMoment q δ) := by field_simp
      _ ≤ _ := by linarith
  have hTVcollision :
      totalVariation (sharedSample (n := n) key Q (fun j => r j.1)) (pilotLaw Q) ≤ 1/16 := by
    have hh := rounded_colored_iid_tv (n := n) (s := 1) hc (by norm_num) hb hu
      (by simpa only [one_mul] using hbsum.le) hQ hr
    simp only [one_mul, one_pow, one_div] at hh
    rw [hqBand] at hh
    have hall : (n.choose 2 : ℝ) * (c⁻¹ * M) = (n.choose 2 : ℝ) * (M / c) := by ring
    exact hh.trans (hall.le.trans hcollision)
  let P := independentLaw (byKey (n := n) Q (fun j : Slot k => r j.1))
  have hP : IsLaw P :=
    independentLaw_isLaw (fun j : Slot k ⊕ Fin n => by cases j <;> first | exact hr _ | exact hQ)
  have hmix := sharedSample_eq_ordered_mixture (n := n) hkey0 Q (fun j => r j.1)
  intro ⟨f, hf, hnull, halt⟩
  have hbig : 2/3 ≤ rejection (sharedSample (n := n) key Q (fun j => r j.1)) f := by
    rw [hmix, rejection_mix]
    change 2/3 ≤ ∑ z, P z * rejection (pilotLaw (fixedListLabel key z)) f
    calc
      _ = (∑ z, P z) * (2/3) := by rw [hP.total, one_mul]
      _ = ∑ z, P z * (2/3) := Finset.sum_mul _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hzero : P z = 0
        · simp [hzero]
        · have hslot (i : Slot k) : bin (z (Sum.inl i)) = some i.1 := by
            by_contra hbad
            apply hzero
            change (∏ j, byKey (n := n) Q (fun i : Slot k => r i.1) j (z j)) = 0
            apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
            simp [byKey, r, binConditional, hbad]
          have hplanted := fixedListLabel_isLaw hkey z
          have hfar : 1 - δ < totalVariation (fixedListLabel key z) q :=
            CanonneNearOne.strict_far_at_small_near_one_moment
              ⟨hplanted.nonneg, hplanted.total⟩ hqN hδ hn' hsmall
              bin u hu hlight hlower hgeom (fun i => z (Sum.inl i))
              (fun i => hupper _ _ (hslot i)) (fixedListLabel_vanishes hkey0 z)
          exact mul_le_mul_of_nonneg_left (halt _ hplanted hfar) (hP.nonneg z)
  have hclose1 := rejection_sub_le_tv (mixLaw_isLaw hP (fun z => pilotLaw (fixedListLabel key z))
      (fun z => pilotLaw_isLaw (fixedListLabel_isLaw hkey z))) (pilotLaw_isLaw (I := Fin n) hQ) hf
  have hclose2 := rejection_sub_le_tv (pilotLaw_isLaw (I := Fin n) hQ)
    (pilotLaw_isLaw (I := Fin n) hq) hf
  rw [← hmix, tv_comm] at hclose1
  rw [tv_comm] at hclose2
  linarith

end Partition

end
end CanonneNearOneTesting
