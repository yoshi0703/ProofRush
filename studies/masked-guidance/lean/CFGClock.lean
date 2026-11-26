import CFGFinite
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The exact jump law of the continuously timed guided reverse process.
The operational clock covers the entire physical interval up to T. Integrating
the exponential race density over the full waiting-time distribution gives
the transition probabilities, with no time discretization. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace CFGClock

def clockRate (T t : ℝ) : ℝ := Real.exp (t - T) / (1 - Real.exp (t - T))

def chart (T u : ℝ) : ℝ :=
  T + Real.log (1 - (1 - Real.exp (-T)) * Real.exp (-u))

def toOperational (T t : ℝ) : ℝ :=
  Real.log ((1 - Real.exp (-T)) / (1 - Real.exp (t - T)))

private theorem clock_base {T : ℝ} (hT : 0 < T) :
    0 < 1 - Real.exp (-T) ∧ 1 - Real.exp (-T) < 1 := by
  constructor
  · exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hT))
  · linarith [Real.exp_pos (-T)]

private theorem clock_argument {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) :
    0 < 1 - (1 - Real.exp (-T)) * Real.exp (-u) := by
  have h := (clock_base hT)
  have hx : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  exact sub_pos.mpr ((mul_le_of_le_one_right h.1.le hx).trans_lt h.2)

theorem chart_zero (T : ℝ) : chart T 0 = 0 := by
  simp [chart]

theorem chart_tendsto (T : ℝ) : Tendsto (chart T) atTop (𝓝 T) := by
  have h : Tendsto (fun u : ℝ => 1 - (1 - Real.exp (-T)) * Real.exp (-u)) atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := 1 - Real.exp (-T))).mul Real.tendsto_exp_neg_atTop_nhds_zero)
  change Tendsto (fun u : ℝ => T + Real.log (1 - (1 - Real.exp (-T)) * Real.exp (-u))) _ _
  simpa only [Function.comp_apply, Real.log_one, add_zero] using (tendsto_const_nhds (x := T)).add
    ((Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp h)

theorem chart_derivative {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) :
    HasDerivAt (chart T) ((1 - Real.exp (-T)) * Real.exp (-u) /
      (1 - (1 - Real.exp (-T)) * Real.exp (-u))) u := by
  let B := 1 - Real.exp (-T)
  have h : HasDerivAt (fun x : ℝ => 1 - B * Real.exp (-x)) (B * Real.exp (-u)) u := by
    convert (hasDerivAt_const u (1 : ℝ)).sub (((hasDerivAt_id u).neg.exp).const_mul B) using 1
    · rfl
    · simp
  exact (h.log (ne_of_gt (clock_argument hT hu))).const_add T

theorem chart_rate_product {T u : ℝ} (hT : 0 < T) (hu : 0 ≤ u) :
    clockRate T (chart T u) * deriv (chart T) u = 1 := by
  have ha := clock_argument hT hu
  have hb := (clock_base hT).1
  have hc := Real.exp_pos (-u)
  rw [(chart_derivative hT hu).deriv]
  simp only [clockRate, chart, add_sub_cancel_left, Real.exp_log ha, sub_sub_cancel]
  field_simp

theorem chart_toOperational {T t : ℝ} (hT : 0 < T) (ht : t < T) :
    chart T (toOperational T t) = t := by
  have h1 := (clock_base hT).1
  have h2 : 0 < 1 - Real.exp (t - T) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold chart toOperational
  rw [Real.exp_neg (Real.log ((1 - Real.exp (-T)) / (1 - Real.exp (t - T)))), Real.exp_log (div_pos h1 h2)]
  have harg : 1 - (1 - Real.exp (-T)) * ((1 - Real.exp (-T)) / (1 - Real.exp (t - T)))⁻¹ =
      Real.exp (t - T) := by field_simp; ring
  rw [harg, Real.log_exp]
  ring

theorem toOperational_nonneg {T t : ℝ} (_hT : 0 < T) (h0 : 0 ≤ t) (ht : t < T) :
    0 ≤ toOperational T t := by
  apply Real.log_nonneg
  have h2 : 0 < 1 - Real.exp (t - T) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  rw [one_le_div h2]
  have he : Real.exp (-T) ≤ Real.exp (t - T) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Forward masking independently retains each visible token with probability
p. The other factors are the visible cylinder mass and the mask probabilities. -/
def forwardMass (p mass : ℝ) (visible hidden : ℕ) : ℝ :=
  mass * p ^ visible * (1-p) ^ hidden

/-- Ratio of the exact forward density at a one-token child and at its parent.
The forward rate back to the parent is one. -/
theorem reverse_score {p parent : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hparent : 0 < parent) (child : ℝ) (k m : ℕ) :
    forwardMass p child (k+1) m / forwardMass p parent k (m+1) =
      (p / (1-p)) * (child / parent) := by
  have hp0 := ne_of_gt hp
  have hq0 := ne_of_gt (sub_pos.mpr hp1)
  unfold forwardMass
  rw [pow_succ, pow_succ]
  field_simp

/-- At unit guidance the physical rates are the square of the conditional
reverse score divided by the mixture score, as in the source equation (9). -/
theorem guided_score_one {T t ma mb : ℝ} (ht : t < T) (ha : 0 < ma)
    (hb : 0 < mb) (ca cb : ℝ) (k m : ℕ) :
    (forwardMass (Real.exp (t-T)) ca (k+1) m /
      forwardMass (Real.exp (t-T)) ma k (m+1))^2 /
    (forwardMass (Real.exp (t-T)) cb (k+1) m /
      forwardMass (Real.exp (t-T)) mb k (m+1)) =
    clockRate T t * ((ca/ma)^2 / (cb/mb)) := by
  have hp := Real.exp_pos (t-T)
  have hq : Real.exp (t-T) < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr ht)
  rw [reverse_score hp hq ha, reverse_score hp hq hb, clockRate]
  have hne : Real.exp (t-T) / (1-Real.exp (t-T)) ≠ 0 := (div_pos hp (sub_pos.mpr hq)).ne'
  by_cases hz : cb = 0
  · simp [hz]
  · field_simp

/-- Removing the common clock from either concrete score preserves their
ratio at every guidance strength. The score-zero convention on an infeasible
target successor agrees with multiplication by its zero conditional rate. -/
theorem guided_score {T t ma mb : ℝ} (ht : t < T) (ha : 0 < ma)
    (hb : 0 < mb) (ca cb w : ℝ) (k m : ℕ) :
    let p := Real.exp (t-T)
    let a := forwardMass p ca (k+1) m / forwardMass p ma k (m+1)
    let b := forwardMass p cb (k+1) m / forwardMass p mb k (m+1)
    a * (a/b)^w = clockRate T t * ((ca/ma) * ((ca/ma)/(cb/mb))^w) := by
  dsimp only
  have hp := Real.exp_pos (t-T)
  have hq : Real.exp (t-T) < 1 := Real.exp_lt_one_iff.mpr (sub_neg.mpr ht)
  rw [reverse_score hp hq ha, reverse_score hp hq hb, clockRate]
  have hn : Real.exp (t-T) / (1-Real.exp (t-T)) ≠ 0 := (div_pos hp (sub_pos.mpr hq)).ne'
  rw [mul_div_mul_left _ _ hn, mul_assoc]

/-- Integrated probability density for a marked exit of rate c in a race
with total rate L under operational time. -/
def raceMass (L c : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), c * Real.exp ((-L) * u)

theorem raceMass_eq {L : ℝ} (hL : 0 < L) (c : ℝ) : raceMass L c = c / L := by
  rw [raceMass, integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hL) 0]
  simp [div_eq_mul_inv]

/-- The exact mass of the shared output, using the integrated holding-time
density at each jump. The horizon counts reveals. A full state is absorbing. -/
def sharedByIntegration {d : ℕ} (jump : CFGFinite.State d → Fin d → Bool → ℚ) :
    ℕ → CFGFinite.State d → ℝ
  | 0, s => if CFGFinite.terminalShared s then 1 else 0
  | n + 1, s =>
    if CFGFinite.Incomplete s then
      ∑ j : Fin d, ∑ b : Bool,
        raceMass (CFGFinite.exitRate jump s : ℝ) (jump s j b : ℝ) *
          sharedByIntegration jump n (CFGFinite.reveal s j b)
    else if CFGFinite.terminalShared s then 1 else 0

open CFGFinite

theorem sharedByIntegration_eq {d : ℕ} (jump : State d → Fin d → Bool → ℚ)
    (hn : ∀ s j b, 0 ≤ jump s j b)
    (hc : ∀ s j b, Reachable s → 0 < jump s j b → Reachable (reveal s j b))
    (hp : ∀ s, Reachable s → Incomplete s → 0 < exitRate jump s)
    (n : ℕ) (s : State d) (hs : Reachable s) :
    sharedByIntegration jump n s = (sharedWithin jump n s : ℝ) := by
  induction n generalizing s with
  | zero =>
    by_cases h : terminalShared s <;> simp [sharedByIntegration, sharedWithin, h]
  | succ n ih =>
    by_cases hi : Incomplete s
    · have hL : 0 < (exitRate jump s : ℝ) := by exact_mod_cast hp s hs hi
      simp only [sharedByIntegration, sharedWithin, ite_eq_left hi]
      push_cast
      simp only [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      rw [raceMass_eq hL]
      by_cases hz : jump s j b = 0
      · simp [hz]
      · have hy := hc s j b hs (lt_of_le_of_ne (hn s j b) (Ne.symm hz))
        rw [ih _ hy, ite_eq_right hz, Rat.cast_mul]
        ring
    · by_cases h : terminalShared s <;> simp [sharedByIntegration, sharedWithin, hi, h]

theorem terminal2_shared : sharedByIntegration rate2 2 (masked 2) = 63 / 80 := by
  rw [sharedByIntegration_eq _ rate2_nonneg rate2_reachable rate2_exit_pos _ _ mask2_reachable,
    sharedWithin2_masked]
  norm_num

theorem terminal3_shared : sharedByIntegration rate3 3 (masked 3) = 171 / 208 := by
  rw [sharedByIntegration_eq _ rate3_nonneg rate3_reachable rate3_exit_pos _ _ mask3_reachable,
    sharedWithin3_masked]
  norm_num

end CFGClock
