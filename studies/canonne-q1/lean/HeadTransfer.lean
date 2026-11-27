import DiffuseTV

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The finite half-L1 norm equals the exact event supremum in the source.
The event \(\{i:p_i>q_i\}\) attains the bound. -/
theorem totalVariation_event_max {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    let A := Finset.univ.filter (fun i => q i < p i)
    totalVariation p q = mass p A - mass q A ∧
      (∀ B : Finset α, mass p B - mass q B ≤ totalVariation p q) := by
  dsimp only
  have hcomm : totalVariation p q = totalVariation q p := by
    unfold totalVariation
    congr 1
    exact Finset.sum_congr rfl fun i _ => abs_sub_comm (p i) (q i)
  rw [hcomm, totalVariation_eq_deficit hq hp]
  constructor
  · unfold mass deficit
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : q i < p i
    · rw [ite_eq_left hi, max_eq_left (sub_nonneg.mpr hi.le)]
    · rw [ite_eq_right hi, max_eq_right (sub_nonpos.mpr (le_of_not_gt hi))]
  · intro B
    unfold mass deficit
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_le_sum (fun i _ => le_max_left (p i - q i) 0)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i _ _ => le_max_right (p i - q i) 0))

/-- Literal half-L1 boundary comparison for any known finite tail and signed offset.
The labels in the complement are each retained individually. -/
theorem strict_crossing_iff {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    (T : Finset α) (d : ℝ) :
    mass q T + d < totalVariation p q ↔ overlap p q T + d < deficit p q Tᶜ := by
  rw [totalVariation_eq_suffix_mass_add_deficit_sub_overlap hp hq T]
  constructor <;> intro h <;> linarith

omit [DecidableEq α] in
/-- A distribution supported on a selected part of the tail can overlap the
null only by at most the null mass of that part. -/
theorem overlap_le_null_support_mass {p q : α → ℝ} (hq : IsLaw q)
    {S T : Finset α} (hST : S ⊆ T) (hsupport : ∀ i ∈ T, i ∉ S → p i = 0) :
    overlap p q T ≤ mass q S := by
  unfold overlap mass
  rw [← Finset.sum_subset hST (fun i hi hn => by
    rw [hsupport i hi hn, min_eq_left (hq.nonneg i)])]
  exact Finset.sum_le_sum fun _ _ => min_le_right _ _

theorem far_of_tail_support {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {S T : Finset α} (hST : S ⊆ T) (hsupport : ∀ i ∈ T, i ∉ S → p i = 0)
    {d : ℝ} (hfar : mass q S + d < deficit p q Tᶜ) :
    mass q T + d < totalVariation p q := by
  apply (strict_crossing_iff hp hq T d).mpr
  have h := overlap_le_null_support_mass hq hST hsupport
  linarith

/-- Population-level dense-tail certificate. (d) can be negative. The threshold
on the warm labels and both observed mass bounds are algebraic inputs. -/
theorem warm_rich_bounds {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {C T : Finset α} (hCT : C ⊆ T) {d u β c θ : ℝ}
    (hfar : mass q T + d < totalVariation p q)
    (hA : deficit p q Tᶜ ≤ u)
    (htail : β ≤ mass p T) (hcold : mass p C ≤ c)
    (hwarm : ∀ i ∈ T \ C, θ ≤ q i) :
    β - c - (u - d) < mass p (warmWithEnoughMass p q (T \ C)) ∧
      θ * ((warmWithEnoughMass p q (T \ C)).card : ℝ) < u - d := by
  have hO : overlap p q T < u - d := by
    have h := (strict_crossing_iff hp hq T d).mp hfar
    linarith
  have hsub : T \ C ⊆ T := Finset.sdiff_subset
  have hmass := mass_warm_sub_overlap_le_mass_warmWithEnoughMass hp hq hsub
  have hsplit : mass p (T \ C) + mass p C = mass p T :=
    Finset.sum_sdiff hCT
  exact ⟨by linarith, (threshold_mul_card_warmWithEnoughMass_le_overlap hp hq hsub hwarm).trans_lt hO⟩

theorem warm_rich_card_lt {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {C T : Finset α} (hCT : C ⊆ T) {d u β c θ : ℝ}
    (hfar : mass q T + d < totalVariation p q)
    (hA : deficit p q Tᶜ ≤ u)
    (htail : β ≤ mass p T) (hcold : mass p C ≤ c)
    (hwarm : ∀ i ∈ T \ C, θ ≤ q i) (hθ : 0 < θ) :
    β - c - (u - d) < mass p (warmWithEnoughMass p q (T \ C)) ∧
      ((warmWithEnoughMass p q (T \ C)).card : ℝ) < (u - d) / θ := by
  have h := warm_rich_bounds hp hq hCT hfar hA htail hcold hwarm
  exact ⟨h.1, (lt_div_iff₀ hθ).mpr (by simpa only [mul_comm] using h.2)⟩

/-- The constants in the upper boundary transfer apply to all finite
alphabets, including zero-mass and unequal-weight head labels. -/
theorem boundary_warm_rich {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {C T : Finset α} (hCT : C ⊆ T) {x m : ℝ} (hm : 0 < m) (hx : x ≤ 1 / 32)
    (hboundary : mass q T = 1 / 4) (hfar : 1 / 4 < totalVariation p q)
    (hA : deficit p q Tᶜ ≤ 7 * x / 4)
    (htail : 1 / 4 - x ≤ mass p T) (hcold : mass p C ≤ 1 / 32)
    (hwarm : ∀ i ∈ T \ C, 1 / (400 * m) ≤ q i) :
    let R := warmWithEnoughMass p q (T \ C)
    1 / 8 < mass p R ∧ (R.card : ℝ) < 700 * m * x := by
  have hfar' : mass q T + (0 : ℝ) < totalVariation p q := by simpa [hboundary] using hfar
  have h := warm_rich_bounds hp hq hCT hfar' hA htail hcold hwarm
  dsimp only
  refine ⟨by linarith [h.1], ?_⟩
  have hpos : 0 < 400 * m := by positivity
  have hcard : ((warmWithEnoughMass p q (T \ C)).card : ℝ) / (400 * m) < 7 * x / 4 := by
    simpa only [sub_zero, one_div, inv_mul_eq_div] using h.2
  have hscaled := (div_lt_iff₀ hpos).mp hcard
  nlinarith

section DisjointAlphabet

variable {H T : Type*} [Fintype H] [Fintype T]

/-- Laws on two disjoint, unrelated labelled finite types. -/
def split (w : ℝ) (h : H → ℝ) (r : T → ℝ) : H ⊕ T → ℝ :=
  Sum.elim (fun i => (1 - w) * h i) (fun i => w * r i)

theorem split_isLaw {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    {h : H → ℝ} {r : T → ℝ} (hh : IsLaw h) (hr : IsLaw r) :
    IsLaw (split w h r) := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | inl a => exact mul_nonneg (sub_nonneg.mpr hw₁) (hh.nonneg a)
    | inr a => exact mul_nonneg hw₀ (hr.nonneg a)
  · simp only [Fintype.sum_sum_type, split, Sum.elim_inl, Sum.elim_inr,
      ← Finset.mul_sum, hh.total, hr.total, mul_one]
    ring

def headDeficit (v w : ℝ) (g h : H → ℝ) : ℝ :=
  ∑ i, max ((1 - w) * h i - (1 - v) * g i) 0

def tailOverlap (v w : ℝ) (s r : T → ℝ) : ℝ :=
  ∑ i, min (v * s i) (w * r i)

theorem split_totalVariation {v w : ℝ} (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1)
    (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    {g h : H → ℝ} {s r : T → ℝ}
    (hg : IsLaw g) (hh : IsLaw h) (hs : IsLaw s) (hr : IsLaw r) :
    totalVariation (split v g s) (split w h r) = w + headDeficit v w g h - tailOverlap v w s r := by
  rw [totalVariation_eq_deficit (split_isLaw hv₀ hv₁ hg hs) (split_isLaw hw₀ hw₁ hh hr)]
  simp only [deficit, Fintype.sum_sum_type, split, Sum.elim_inl, Sum.elim_inr]
  have point (i : T) : max (w * r i - v * s i) 0 = w * r i - min (v * s i) (w * r i) := by
    rcases le_total (v * s i) (w * r i) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), min_eq_left h]
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_right h, sub_self]
  simp only [headDeficit, tailOverlap, point, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hr.total, mul_one]
  ring

theorem equal_weight_head_deficit {w : ℝ} (hw₁ : w ≤ 1)
    {g h : H → ℝ} (hg : IsLaw g) (hh : IsLaw h) :
    headDeficit w w g h = (1 - w) * totalVariation g h := by
  rw [totalVariation_eq_deficit hg hh]
  unfold headDeficit deficit
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (1-w)*h i-(1-w)*g i = (1-w)*(h i-g i) by ring,
    mul_max_of_nonneg _ _ (sub_nonneg.mpr hw₁), mul_zero]

theorem head_deficit_le_conditional_tv {v w : ℝ} (hw₁ : w ≤ 1)
    {g h : H → ℝ} (hg : IsLaw g) (hh : IsLaw h) :
    headDeficit v w g h ≤ max (v - w) 0 + (1 - w) * totalVariation g h := by
  have hw : 0 ≤ 1 - w := sub_nonneg.mpr hw₁
  have point (i : H) :
      max ((1 - w) * h i - (1 - v) * g i) 0 ≤
        max (v - w) 0 * g i + (1 - w) * max (h i - g i) 0 := by
    apply max_le
    · have h₁ := mul_le_mul_of_nonneg_right (le_max_left (v - w) 0) (hg.nonneg i)
      have h₂ := mul_le_mul_of_nonneg_left (le_max_left (h i - g i) 0) hw
      linarith
    · exact add_nonneg (mul_nonneg (le_max_right _ _) (hg.nonneg i))
        (mul_nonneg hw (le_max_right _ _))
  unfold headDeficit
  calc
    _ ≤ ∑ i, (max (v - w) 0 * g i + (1 - w) * max (h i - g i) 0) :=
      Finset.sum_le_sum (fun i _ => point i)
    _ = _ := by
      rw [totalVariation_eq_deficit hg hh]
      simp only [deficit, Finset.sum_add_distrib, ← Finset.mul_sum, hg.total, mul_one]

theorem head_deficit_same_conditional {v w : ℝ} {h : H → ℝ} (hh : IsLaw h) :
    headDeficit v w h h = max (v - w) 0 := by
  unfold headDeficit
  have point (i : H) :
      max ((1 - w) * h i - (1 - v) * h i) 0 = h i * max (v - w) 0 := by
    rw [show (1-w)*h i-(1-v)*h i = h i*(v-w) by ring,
      mul_max_of_nonneg _ _ (hh.nonneg i), mul_zero]
  simp only [point, ← Finset.sum_mul, hh.total, one_mul]

omit [Fintype T] in
theorem tailOverlap_le_mul_support {v w : ℝ} (hw₀ : 0 ≤ w)
    {s r : T → ℝ} (hr₀ : ∀ i, 0 ≤ r i) [Fintype T]
    (S : Finset T) (hsupport : ∀ i ∉ S, s i = 0) :
    tailOverlap v w s r ≤ w * mass r S := by
  unfold tailOverlap mass
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hn => by
    rw [hsupport i hn, mul_zero, min_eq_left (mul_nonneg hw₀ (hr₀ i))]),
    Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => min_le_right _ _

/-- Equal group masses, arbitrary head laws, and a tail with chosen support.
Any positive signed distance advantage survives the lift unchanged. -/
theorem equal_weight_far_of_tail_support {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1)
    {g h : H → ℝ} {s r : T → ℝ} (hg : IsLaw g) (hh : IsLaw h)
    (hs : IsLaw s) (hr : IsLaw r) (S : Finset T)
    (hsupport : ∀ i ∉ S, s i = 0) {d : ℝ}
    (hfar : w * mass r S + d < (1 - w) * totalVariation g h) :
    w + d < totalVariation (split w g s) (split w h r) := by
  rw [split_totalVariation hw₀ hw₁ hw₀ hw₁ hg hh hs hr, equal_weight_head_deficit hw₁ hg hh]
  have hO := tailOverlap_le_mul_support hw₀ hr.nonneg S hsupport (v := w)
  linarith

/-- Direct strict lower transfer from conditional separation and a small support. -/
theorem strict_radius_from_conditional {w : ℝ} (hw₀ : 0 ≤ w) (hw : w < 1)
    {g h : H → ℝ} {s r : T → ℝ} (hg : IsLaw g) (hh : IsLaw h)
    (hs : IsLaw s) (hr : IsLaw r) (S : Finset T) (hsupport : ∀ i ∉ S, s i = 0)
    {x d : ℝ} (hhead : x < totalVariation g h)
    (hbudget : w * mass r S + d ≤ (1 - w) * x) :
    w + d < totalVariation (split w g s) (split w h r) :=
  equal_weight_far_of_tail_support hw₀ hw.le hg hh hs hr S hsupport
    (lt_of_le_of_lt hbudget (mul_lt_mul_of_pos_left hhead (sub_pos.mpr hw)))

theorem quarter_strict_transfer {g h : H → ℝ} {s r : T → ℝ}
    (hg : IsLaw g) (hh : IsLaw h) (hs : IsLaw s) (hr : IsLaw r)
    (S : Finset T) (hsupport : ∀ i ∉ S, s i = 0)
    {x : ℝ} (hhead : x < totalVariation g h) (hmass : mass r S ≤ x) :
    1 / 4 + x / 2 < totalVariation (split (1 / 4) g s) (split (1 / 4) h r) := by
  apply strict_radius_from_conditional (by norm_num) (by norm_num) hg hh hs hr S hsupport hhead
  linarith

/-- The base-cost transfer uses an increased tail weight with unchanged head. -/
theorem strict_radius_from_tail_tilt {v w : ℝ} (hv : v ≤ 1) (hw₀ : 0 ≤ w) (hwv : w ≤ v)
    {h : H → ℝ} {s r : T → ℝ} (hh : IsLaw h) (hs : IsLaw s)
    (hr : IsLaw r) (S : Finset T) (hsupport : ∀ i ∉ S, s i = 0)
    {d : ℝ} (hbudget : w * mass r S + d < v - w) :
    w + d < totalVariation (split v h s) (split w h r) := by
  rw [split_totalVariation (hw₀.trans hwv) hv hw₀ (hwv.trans hv) hh hh hs hr,
    head_deficit_same_conditional hh, max_eq_left (sub_nonneg.mpr hwv)]
  have hO := tailOverlap_le_mul_support hw₀ hr.nonneg S hsupport (v := v)
  linarith

end DisjointAlphabet
end
end CanonneHeadTransfer
