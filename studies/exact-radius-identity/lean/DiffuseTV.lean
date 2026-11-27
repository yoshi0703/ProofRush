import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CanonneDiffuse

open scoped BigOperators
noncomputable section

variable {α γ : Type*} [Fintype α] [Fintype γ]

/-- A finite probability mass function. -/
structure IsLaw (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  total : ∑ a, p a = 1

def mass (p : α → ℝ) (B : Finset α) : ℝ := ∑ a ∈ B, p a

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

def deficit (p q : α → ℝ) (B : Finset α) : ℝ := ∑ a ∈ B, max (q a - p a) 0

def overlap (p q : α → ℝ) (B : Finset α) : ℝ := ∑ a ∈ B, min (p a) (q a)

/-- Half-L1 equals the sum of all signed deficits in the direction from p to q. -/
theorem totalVariation_eq_deficit {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    totalVariation p q = deficit p q Finset.univ := by
  have hpoint (a : α) : |p a - q a| = (p a - q a) + 2 * max (q a - p a) 0 := by
    rcases le_total (p a) (q a) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
      ring
  simp only [totalVariation, deficit, hpoint, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hp.total, hq.total]
  ring

/-- Exact decomposition at a known suffix B, with the other labels kept individually. -/
theorem totalVariation_eq_suffix_mass_add_deficit_sub_overlap [DecidableEq α]
    {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) (B : Finset α) :
    totalVariation p q = mass q B + deficit p q Bᶜ - overlap p q B := by
  have hpoint (a : α) : max (q a - p a) 0 = q a - min (p a) (q a) := by
    rcases le_total (p a) (q a) with h | h
    · rw [max_eq_left (sub_nonneg.mpr h), min_eq_left h]
    · rw [max_eq_right (sub_nonpos.mpr h), min_eq_right h, sub_self]
  have hin : deficit p q B = mass q B - overlap p q B := by
    simp only [deficit, mass, overlap, hpoint, Finset.sum_sub_distrib]
  have hsplit : deficit p q Bᶜ + deficit p q B = deficit p q Finset.univ :=
    Finset.sum_compl_add_sum B _
  rw [totalVariation_eq_deficit hp hq, ← hsplit, hin]
  ring

theorem overlap_nonneg {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) (B : Finset α) :
    0 ≤ overlap p q B :=
  Finset.sum_nonneg fun a _ => le_min (hp.nonneg a) (hq.nonneg a)

variable [DecidableEq γ]

/-- Push a law forward by the category map f. -/
def coarsen (f : α → γ) (p : α → ℝ) (c : γ) : ℝ :=
  ∑ a ∈ Finset.univ.filter (fun a => f a = c), p a

theorem coarsen_isLaw (f : α → γ) {p : α → ℝ} (hp : IsLaw p) :
    IsLaw (coarsen f p) := by
  constructor
  · intro c
    exact Finset.sum_nonneg fun a _ => hp.nonneg a
  · simp only [coarsen, Finset.sum_filter]
    rw [Finset.sum_comm]
    simpa using hp.total

variable [DecidableEq α]

omit [Fintype γ] [DecidableEq α] in
theorem coarsen_at_singleton {f : α → γ} {a : α}
    (hf : ∀ z, f z = f a → z = a) (p : α → ℝ) :
    coarsen f p (f a) = p a := by
  have hfiber : Finset.univ.filter (fun z => f z = f a) = {a} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hf z, congrArg f⟩
  simp [coarsen, hfiber]

/-- Coarse TV controls the complement's deficit whenever the complement remains
    in singleton fibers. The fibers within B can be chosen arbitrarily. -/
theorem complement_deficit_le_coarse_tv {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) (B : Finset α) (f : α → γ)
    (hf : ∀ a ∉ B, ∀ z, f z = f a → z = a) :
    deficit p q Bᶜ ≤ totalVariation (coarsen f p) (coarsen f q) := by
  rw [totalVariation_eq_deficit (coarsen_isLaw f hp) (coarsen_isLaw f hq)]
  have hinj : Set.InjOn f (↑(Bᶜ : Finset α)) := by
    intro a _ b hb h
    exact hf b (Finset.mem_compl.mp hb) a h
  have heq : deficit p q Bᶜ =
      ∑ c ∈ (Bᶜ : Finset α).image f, max (coarsen f q c - coarsen f p c) 0 := by
    rw [Finset.sum_image hinj]
    unfold deficit
    apply Finset.sum_congr rfl
    intro a ha
    rw [coarsen_at_singleton (hf a (Finset.mem_compl.mp ha)) p,
      coarsen_at_singleton (hf a (Finset.mem_compl.mp ha)) q]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => le_max_right (coarsen f q c - coarsen f p c) 0)

/-- Strict crossing of the suffix mass plus d forces overlap below x − d
    if the coarsened laws are within x in total variation. -/
theorem suffix_overlap_lt_of_coarse_tv_le {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) (B : Finset α) (f : α → γ)
    (hf : ∀ a ∉ B, ∀ z, f z = f a → z = a) {x d : ℝ}
    (hcoarse : totalVariation (coarsen f p) (coarsen f q) ≤ x)
    (hfar : mass q B + d < totalVariation p q) :
    overlap p q B < x - d := by
  have hdeficit := (complement_deficit_le_coarse_tv hp hq B f hf).trans hcoarse
  rw [totalVariation_eq_suffix_mass_add_deficit_sub_overlap hp hq B] at hfar
  linarith

/-- Coarse acceptance makes strict crossing impossible at offsets d ≥ x. -/
theorem totalVariation_le_suffix_mass_add_offset {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) (B : Finset α) (f : α → γ)
    (hf : ∀ a ∉ B, ∀ z, f z = f a → z = a) {x d : ℝ}
    (hcoarse : totalVariation (coarsen f p) (coarsen f q) ≤ x) (hxd : x ≤ d) :
    totalVariation p q ≤ mass q B + d := by
  have hdeficit := (complement_deficit_le_coarse_tv hp hq B f hf).trans hcoarse
  have hoverlap := overlap_nonneg hp hq B
  rw [totalVariation_eq_suffix_mass_add_deficit_sub_overlap hp hq B]
  linarith


/-- The warm labels at which p is at least q. -/
def warmWithEnoughMass (p q : α → ℝ) (W : Finset α) : Finset α :=
  W.filter (fun a => q a ≤ p a)

omit [DecidableEq α] in
theorem mass_warm_sub_overlap_le_mass_warmWithEnoughMass {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) {W B : Finset α} (hWB : W ⊆ B) :
    mass p W - overlap p q B ≤ mass p (warmWithEnoughMass p q W) := by
  have hsub : overlap p q W ≤ overlap p q B :=
    Finset.sum_le_sum_of_subset_of_nonneg hWB
      (fun a _ _ => le_min (hp.nonneg a) (hq.nonneg a))
  have hpoint (a : α) :
      p a ≤ (if q a ≤ p a then p a else 0) + min (p a) (q a) := by
    by_cases h : q a ≤ p a
    · simp only [ite_eq_left h, min_eq_right h]
      linarith [hq.nonneg a]
    · simp [ite_eq_right h, min_eq_left (le_of_not_ge h)]
  have hsum := Finset.sum_le_sum (s := W) (fun a _ => hpoint a)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
  change mass p W ≤ mass p (warmWithEnoughMass p q W) + overlap p q W at hsum
  linarith

omit [DecidableEq α] in
theorem threshold_mul_card_warmWithEnoughMass_le_overlap
    {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q) {W B : Finset α} (hWB : W ⊆ B)
    {threshold : ℝ} (hwarm : ∀ a ∈ W, threshold ≤ q a) :
    threshold * ((warmWithEnoughMass p q W).card : ℝ) ≤ overlap p q B := by
  have hpoint (a : α) (ha : a ∈ warmWithEnoughMass p q W) :
      threshold ≤ min (p a) (q a) := by
    have hmem := Finset.mem_filter.mp ha
    rw [min_eq_right hmem.2]
    exact hwarm a hmem.1
  calc
    threshold * ((warmWithEnoughMass p q W).card : ℝ) =
        ∑ _a ∈ warmWithEnoughMass p q W, threshold := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ overlap p q (warmWithEnoughMass p q W) := Finset.sum_le_sum hpoint
    _ ≤ overlap p q B := Finset.sum_le_sum_of_subset_of_nonneg
      (fun _ ha => hWB (Finset.mem_filter.mp ha).1)
      (fun a _ _ => le_min (hp.nonneg a) (hq.nonneg a))

omit [DecidableEq α] in
theorem mass_coarse_fiber_le_of_totalVariation_le {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) (f : α → γ) (c : γ) {x : ℝ}
    (hcoarse : totalVariation (coarsen f p) (coarsen f q) ≤ x) :
    coarsen f q c - x ≤ coarsen f p c := by
  rw [totalVariation_eq_deficit (coarsen_isLaw f hp) (coarsen_isLaw f hq)] at hcoarse
  have hsingleton : deficit (coarsen f p) (coarsen f q) {c} ≤
      deficit (coarsen f p) (coarsen f q) Finset.univ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {c})
      (fun z _ _ => le_max_right (coarsen f q z - coarsen f p z) 0)
  simp only [deficit, Finset.sum_singleton] at hsingleton
  unfold deficit at hcoarse
  linarith [le_max_left (coarsen f q c - coarsen f p c) 0]

/-- If one coarse category is exactly the warm part of a suffix bin, a law
    crossing the radius has a controlled-size set of warm labels carrying mass.
    The rules allow any signed offset d, including a radius below the suffix mass. -/
theorem warm_set_bounds_of_coarse_tv_le {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) {W B : Finset α} (hWB : W ⊆ B)
    (f : α → γ) (c : γ) (hf : ∀ a ∉ B, ∀ z, f z = f a → z = a)
    (hfiber : ∀ a, a ∈ W ↔ f a = c) {x d threshold : ℝ}
    (hwarm : ∀ a ∈ W, threshold ≤ q a)
    (hcoarse : totalVariation (coarsen f p) (coarsen f q) ≤ x)
    (hfar : mass q B + d < totalVariation p q) :
    mass q W - 2 * x + d < mass p (warmWithEnoughMass p q W) ∧
      threshold * ((warmWithEnoughMass p q W).card : ℝ) < x - d := by
  have hoverlap := suffix_overlap_lt_of_coarse_tv_le hp hq B f hf hcoarse hfar
  have hmass := mass_warm_sub_overlap_le_mass_warmWithEnoughMass hp hq hWB
  have hcompare := mass_coarse_fiber_le_of_totalVariation_le hp hq f c hcoarse
  have heq : Finset.univ.filter (fun a => f a = c) = W := by
    ext a
    simp [hfiber a]
  simp only [coarsen, heq] at hcompare
  change mass q W - x ≤ mass p W at hcompare
  exact ⟨by linarith, lt_of_le_of_lt
    (threshold_mul_card_warmWithEnoughMass_le_overlap hp hq hWB hwarm) hoverlap⟩


end

end CanonneDiffuse
