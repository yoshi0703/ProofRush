import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-! A full-support product example: a first guidance jump concentrates on a
shared output event of arbitrarily small target mass. -/
noncomputable section
/- Finite enumeration shares simp lists across cases; a lemma may be redundant
in an individual branch, and some tactic sequences finish earlier. -/
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace CFGRare
open scoped BigOperators Topology
open Filter

abbrev Word := Bool × Bool × Bool

def bitWeight (s : ℝ) (b : Bool) : ℝ := if b then s else 1-s

def target (s : ℝ) (x : Word) : ℝ :=
  bitWeight s x.1 * bitWeight s x.2.1 * bitWeight s x.2.2

def other (s : ℝ) (x : Word) : ℝ :=
  (1-s/4)*(if x = (false,true,false) ∨ x = (false,false,true) then 1/2 else 0) +
  s/4*(if x = (false,false,false) then 0 else 1/7)

def event (j : Fin 3) (b : Bool) (x : Word) : Bool :=
  if j.val = 0 then x.1 == b else if j.val = 1 then x.2.1 == b else x.2.2 == b

def mass (p : Word → ℝ) (j : Fin 3) (b : Bool) : ℝ :=
  ∑ x : Word, if event j b x then p x else 0

/-- Both raw formulas are normalized probability distributions. -/
theorem normalized_classes (s : ℝ) :
    (∑ x : Word, target s x) = 1 ∧ (∑ x : Word, other s x) = 1 := by
  simp [target, other, bitWeight, Fintype.sum_prod_type]
  ring_nf
  simp

theorem class_nonnegative (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (x : Word) :
    0 ≤ target s x ∧ 0 ≤ other s x := by
  have hb (b : Bool) : 0 ≤ bitWeight s b := by
    cases b <;> simp [bitWeight] <;> linarith
  constructor
  · exact mul_nonneg (mul_nonneg (hb x.1) (hb x.2.1)) (hb x.2.2)
  · unfold other
    apply add_nonneg
    · apply mul_nonneg (by linarith)
      split_ifs <;> norm_num
    · apply mul_nonneg (by linarith)
      split_ifs <;> norm_num

lemma raw_marginals (s : ℝ) :
    mass (target s) 0 true = s ∧ mass (other s) 0 true = s/7 ∧
    mass (target s) 1 true = s ∧ mass (other s) 1 true = 1/2+s/56 ∧
    mass (target s) 2 true = s ∧ mass (other s) 2 true = 1/2+s/56 ∧
    mass (target s) 0 false = 1-s ∧ mass (other s) 0 false = 1-s/7 ∧
    mass (target s) 1 false = 1-s ∧ mass (other s) 1 false = 1/2-s/56 ∧
    mass (target s) 2 false = 1-s ∧ mass (other s) 2 false = 1/2-s/56 := by
  simp [mass, event, target, other, bitWeight, Fintype.sum_prod_type]
  <;> ring_nf
  <;> simp

def rootRate (s : ℝ) (j : Fin 3) (b : Bool) (w : ℕ) : ℝ :=
  let u := mass (target s) j b
  let v := mass (other s) j b
  u * (u / ((u+v)/2)) ^ w

def firstMarker (s : ℝ) (w : ℕ) : ℝ :=
  rootRate s 0 true w / ∑ j : Fin 3, ∑ b : Bool, rootRate s j b w

/-- Substantive finite-strength lower bound, for the exact first-jump rate
constructed from the two raw distributions above. -/
theorem rare_finite_witness : firstMarker (1/100) 50 > 99/100 := by
  have hm := raw_marginals (1/100)
  rcases hm with ⟨h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24⟩
  simp only [firstMarker, rootRate, Fin.sum_univ_succ, Fin.sum_univ_zero, Fintype.sum_bool,
    h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24]
  norm_num [h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24]

/-- For all non-marker root outcomes the class-conditional likelihood ratio
is at most 7/3, while the marker likelihood ratio is exactly 7. -/
theorem competing_likelihoods (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    mass (target s) 0 true = 7 * mass (other s) 0 true ∧
    3 * mass (target s) 0 false ≤ 7 * mass (other s) 0 false ∧
    3 * mass (target s) 1 true ≤ 7 * mass (other s) 1 true ∧
    3 * mass (target s) 1 false ≤ 7 * mass (other s) 1 false ∧
    3 * mass (target s) 2 true ≤ 7 * mass (other s) 2 true ∧
    3 * mass (target s) 2 false ≤ 7 * mass (other s) 2 false := by
  rcases raw_marginals s with ⟨h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24⟩
  rw [h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

def overlap (s : ℝ) : ℝ :=
  ∑ x : Word, if x = (false,false,false) then 0 else target s x

theorem overlap_formula (s : ℝ) : overlap s = 1-(1-s)^3 := by
  simp [overlap, target, bitWeight, Fintype.sum_prod_type]
  ring

theorem rare_initial (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ overlap s < ε := by
  let s : ℝ := min (1/2) (ε/4)
  have hs0 : 0 < s := lt_min (by norm_num) (by linarith)
  have hs1 : s ≤ 1/2 := min_le_left _ _
  have hsε : s ≤ ε/4 := min_le_right _ _
  have hprod : 0 ≤ s^2 * (3-s) := mul_nonneg (sq_nonneg s) (by linarith)
  refine ⟨s, hs0, by linarith, ?_⟩
  rw [overlap_formula]
  nlinarith

theorem rare_initial_witness : overlap (1/100) = 29701/1000000 := by
  rw [overlap_formula]
  norm_num

/-- Finite sum of subunit real powers decays for real guidance strengths. -/
theorem finite_exponential_decay (n : ℕ) (a r : ℕ → ℝ)
    (h : ∀ i < n, -1 < r i ∧ r i < 1) :
    Tendsto (fun w : ℝ => ∑ i ∈ Finset.range n, a i * (r i) ^ w) atTop (𝓝 0) := by
  induction n with
  | zero => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0))
  | succ n ih =>
      have hn : ∀ i < n, -1 < r i ∧ r i < 1 := by
        intro i hi
        exact h i (by omega)
      have hp := h n (by omega)
      have ht := (tendsto_rpow_atTop_of_base_lt_one (r n) hp.1 hp.2).const_mul (a n)
      have hsum := (ih hn).add ht
      simpa [Finset.sum_range_succ] using hsum

/-- A normalized first-jump probability converges to one when all competing
posterior-to-marker ratios are below one. -/
theorem normalized_first_jump_limit (n : ℕ) (a r : ℕ → ℝ)
    (h : ∀ i < n, -1 < r i ∧ r i < 1) :
    Tendsto (fun w : ℝ => (1 + ∑ i ∈ Finset.range n, a i * (r i) ^ w)⁻¹)
      atTop (𝓝 1) := by
  have hsum := (finite_exponential_decay n a r h).const_add 1
  have hinv := hsum.inv₀ (by norm_num : (1 + (0:ℝ)) ≠ 0)
  simpa using hinv

/-- Ratio of a competing root posterior to the marker posterior.  Outcomes
are marker=false and then true/false for each of the two other coordinates. -/
def competitorRatio (s : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 4*(1-s)/(7-4*s)
  else if i = 1 ∨ i = 3 then 64*s/(28+57*s)
  else 64*(1-s)/(84-57*s)

def competitorMultiplier (s : ℝ) (i : ℕ) : ℝ :=
  if i = 1 ∨ i = 3 then 1 else (1-s)/s

theorem ratio_bounds (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ i < 5, -1 < competitorRatio s i ∧ competitorRatio s i < 1 := by
  have d0 : 0 < 7-4*s := by linarith
  have d1 : 0 < 28+57*s := by linarith
  have d2 : 0 < 84-57*s := by linarith
  have r0 : 0 ≤ 4*(1-s)/(7-4*s) ∧ 4*(1-s)/(7-4*s) < 1 := by
    constructor
    · apply div_nonneg <;> linarith
    · apply (div_lt_one d0).2; linarith
  have r1 : 0 ≤ 64*s/(28+57*s) ∧ 64*s/(28+57*s) < 1 := by
    constructor
    · apply div_nonneg <;> linarith
    · apply (div_lt_one d1).2; linarith
  have r2 : 0 ≤ 64*(1-s)/(84-57*s) ∧ 64*(1-s)/(84-57*s) < 1 := by
    constructor
    · apply div_nonneg <;> linarith
    · apply (div_lt_one d2).2; linarith
  rcases r0 with ⟨r00,r01⟩
  rcases r1 with ⟨r10,r11⟩
  rcases r2 with ⟨r20,r21⟩
  have hr0 : -1 < 4*(1-s)/(7-4*s) ∧ 4*(1-s)/(7-4*s) < 1 :=
    ⟨lt_of_lt_of_le (by norm_num) r00, r01⟩
  have hr1 : -1 < 64*s/(28+57*s) ∧ 64*s/(28+57*s) < 1 :=
    ⟨lt_of_lt_of_le (by norm_num) r10, r11⟩
  have hr2 : -1 < 64*(1-s)/(84-57*s) ∧ 64*(1-s)/(84-57*s) < 1 :=
    ⟨lt_of_lt_of_le (by norm_num) r20, r21⟩
  intro i hi
  interval_cases i <;> simp [competitorRatio] <;> first | exact hr0 | exact hr1 | exact hr2

theorem ratio_nonnegative (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ i < 5, 0 ≤ competitorRatio s i := by
  have d0 : 0 ≤ 7-4*s := by linarith
  have d1 : 0 ≤ 28+57*s := by linarith
  have d2 : 0 ≤ 84-57*s := by linarith
  have r0 : 0 ≤ 4*(1-s)/(7-4*s) := div_nonneg (by linarith) d0
  have r1 : 0 ≤ 64*s/(28+57*s) := div_nonneg (by linarith) d1
  have r2 : 0 ≤ 64*(1-s)/(84-57*s) := div_nonneg (by linarith) d2
  intro i hi
  interval_cases i <;> simp [competitorRatio] <;> first | exact r0 | exact r1 | exact r2

def rootLikelihood (s : ℝ) (j : Fin 3) (b : Bool) : ℝ :=
  let u := mass (target s) j b
  let v := mass (other s) j b
  u / ((u+v)/2)

theorem root_likelihood_nonnegative (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (j : Fin 3) (b : Bool) : 0 ≤ rootLikelihood s j b := by
  have hu : 0 ≤ mass (target s) j b := by
    unfold mass
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact (class_nonnegative s hs0 hs1 x).1
    · norm_num
  have hv : 0 ≤ mass (other s) j b := by
    unfold mass
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact (class_nonnegative s hs0 hs1 x).2
    · norm_num
  unfold rootLikelihood
  exact div_nonneg hu (by linarith)

theorem marker_likelihood (s : ℝ) (hs0 : 0 < s) : rootLikelihood s 0 true = 7/4 := by
  rcases raw_marginals s with ⟨h01,h02,_,_,_,_,_,_,_,_,_,_⟩
  simp only [rootLikelihood, h01, h02]
  have hd : s+s/7 ≠ 0 := ne_of_gt (by linarith)
  field_simp [ne_of_gt hs0, hd] <;> ring

/-- The explicit ratios in the limit theorem really are the five raw
competitor likelihoods divided by the marker likelihood. -/
theorem raw_ratio_bridge (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    rootLikelihood s 0 false / rootLikelihood s 0 true = competitorRatio s 0 ∧
    rootLikelihood s 1 true / rootLikelihood s 0 true = competitorRatio s 1 ∧
    rootLikelihood s 1 false / rootLikelihood s 0 true = competitorRatio s 2 ∧
    rootLikelihood s 2 true / rootLikelihood s 0 true = competitorRatio s 3 ∧
    rootLikelihood s 2 false / rootLikelihood s 0 true = competitorRatio s 4 := by
  rcases raw_marginals s with ⟨h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24⟩
  have hs : s ≠ 0 := ne_of_gt hs0
  have h0 : 7-4*s ≠ 0 := ne_of_gt (by linarith)
  have h1 : 28+57*s ≠ 0 := ne_of_gt (by linarith)
  have h2 : 84-57*s ≠ 0 := ne_of_gt (by linarith)
  have h3 : 14-8*s ≠ 0 := ne_of_gt (by linarith)
  have h4 : 168-114*s ≠ 0 := ne_of_gt (by linarith)
  have h5 : 56+114*s ≠ 0 := ne_of_gt (by linarith)
  simp [rootLikelihood, competitorRatio,
    h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24]
  ring_nf at h0 h1 h2 h3 h4 h5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp [hs, h0, h1, h2] <;> ring_nf <;> field_simp [h0,h1,h2,h3,h4,h5] <;> ring

/-- Base-rate factors in the same five-outcome order. -/
theorem raw_multiplier_bridge (s : ℝ) (hs0 : 0 < s) :
    mass (target s) 0 false / mass (target s) 0 true = competitorMultiplier s 0 ∧
    mass (target s) 1 true / mass (target s) 0 true = competitorMultiplier s 1 ∧
    mass (target s) 1 false / mass (target s) 0 true = competitorMultiplier s 2 ∧
    mass (target s) 2 true / mass (target s) 0 true = competitorMultiplier s 3 ∧
    mass (target s) 2 false / mass (target s) 0 true = competitorMultiplier s 4 := by
  rcases raw_marginals s with ⟨h01,h02,h11,h12,h21,h22,h03,h04,h13,h14,h23,h24⟩
  simp [competitorMultiplier, h01,h11,h21,h03,h13,h23, ne_of_gt hs0]

/-- The normalized marker probability in posterior-ratio coordinates. -/
def normalizedMarker (s w : ℝ) : ℝ :=
  (1 + ∑ i ∈ Finset.range 5, competitorMultiplier s i * (competitorRatio s i)^w)⁻¹

theorem normalized_marker_limit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (normalizedMarker s) atTop (𝓝 1) := by
  exact normalized_first_jump_limit 5 (competitorMultiplier s) (competitorRatio s)
    (ratio_bounds s hs0 hs1)

/-- Dividing any competing guided rate by the marker rate gives the
base-mass ratio multiplied by the posterior-ratio power. -/
theorem guided_rate_ratio (u u0 r r0 w : ℝ) (_hu0 : 0 < u0)
    (hr : 0 ≤ r) (hr0 : 0 < r0) :
    (u * r^w) / (u0 * r0^w) = (u/u0) * (r/r0)^w := by
  rw [Real.div_rpow hr (le_of_lt hr0)]
  exact mul_div_mul_comm u (r^w) u0 (r0^w)

/-- Exact real-strength guided rate, with the common time factor omitted. -/
def realRootRate (s : ℝ) (j : Fin 3) (b : Bool) (w : ℝ) : ℝ :=
  mass (target s) j b * (rootLikelihood s j b)^w

def realFirstMarker (s w : ℝ) : ℝ :=
  realRootRate s 0 true w / ∑ j : Fin 3, ∑ b : Bool, realRootRate s j b w


lemma normalize_six (a b c d e f : ℝ) (ha : a ≠ 0) :
    a/(b+a+c+d+e+f) = (1+b/a+c/a+d/a+e/a+f/a)⁻¹ := by
  rw [← inv_div]
  congr 1
  field_simp [ha]
  <;> ring

theorem real_rate_ratio (s w : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (j : Fin 3) (b : Bool) :
    realRootRate s j b w / realRootRate s 0 true w =
    (mass (target s) j b / mass (target s) 0 true) *
      (rootLikelihood s j b / rootLikelihood s 0 true)^w := by
  unfold realRootRate
  apply guided_rate_ratio
  · rw [(raw_marginals s).1]; exact hs0
  · exact root_likelihood_nonnegative s (le_of_lt hs0) (le_of_lt hs1) j b
  · rw [marker_likelihood s hs0]; norm_num

theorem real_marker_formula (s w : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    realFirstMarker s w = normalizedMarker s w := by
  rcases raw_ratio_bridge s hs0 hs1 with ⟨r0,r1,r2,r3,r4⟩
  rcases raw_multiplier_bridge s hs0 with ⟨u0,u1,u2,u3,u4⟩
  have e0 := real_rate_ratio s w hs0 hs1 0 false
  have e1 := real_rate_ratio s w hs0 hs1 1 true
  have e2 := real_rate_ratio s w hs0 hs1 1 false
  have e3 := real_rate_ratio s w hs0 hs1 2 true
  have e4 := real_rate_ratio s w hs0 hs1 2 false
  rw [u0,r0] at e0
  rw [u1,r1] at e1
  rw [u2,r2] at e2
  rw [u3,r3] at e3
  rw [u4,r4] at e4
  have ha : realRootRate s 0 true w ≠ 0 := by
    unfold realRootRate
    rw [(raw_marginals s).1, marker_likelihood s hs0]
    exact ne_of_gt (mul_pos hs0 (Real.rpow_pos_of_pos (by norm_num) w))
  unfold realFirstMarker normalizedMarker
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fintype.sum_bool,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  -- At this point the six rates are divided by the marker rate.
  have hn := normalize_six (realRootRate s 0 true w) (realRootRate s 0 false w)
    (realRootRate s 1 true w) (realRootRate s 1 false w)
    (realRootRate s 2 true w) (realRootRate s 2 false w) ha
  rw [e0,e1,e2,e3,e4] at hn
  convert hn using 1 <;> ring

theorem real_first_marker_limit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (realFirstMarker s) atTop (𝓝 1) := by
  apply (normalized_marker_limit s hs0 hs1).congr'
  exact Filter.Eventually.of_forall fun w => (real_marker_formula s w hs0 hs1).symm

/-- Any word reached after the marker reveal is shared between classes. -/
theorem marker_is_shared (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (x : Word) (hx : x.1 = true) : 0 < target s x ∧ 0 < other s x := by
  rcases x with ⟨b,c,d⟩
  cases b <;> cases c <;> cases d <;> simp_all [target, other, bitWeight]

#print axioms normalized_classes
#print axioms class_nonnegative
#print axioms raw_marginals
#print axioms rare_finite_witness
#print axioms rare_initial
#print axioms normalized_first_jump_limit
#print axioms normalized_marker_limit
#print axioms raw_ratio_bridge
#print axioms raw_multiplier_bridge
#print axioms marker_is_shared
#print axioms guided_rate_ratio
#print axioms real_first_marker_limit
end CFGRare
