import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

/-! Strong-guidance selection and finite-path leakage for normalized rates.
A path's exponential cost is the sum of its nonnegative log posterior gaps.
The endpoint coefficient sums the limiting weights of every minimum-cost path. -/

namespace CFGSelection

open Filter
open scoped BigOperators Topology

noncomputable section

/-- Each edge has positive base weight and a nonnegative gap from the best
available score. At least one edge attains that best score. -/
structure Outgoing (ι : Type*) where
  labels : Finset ι
  base : ι → ℝ
  gap : ι → ℝ
  base_pos : ∀ e ∈ labels, 0 < base e
  gap_nonneg : ∀ e ∈ labels, 0 ≤ gap e
  has_maximizer : ∃ e ∈ labels, gap e = 0

variable {ι : Type*}

def Outgoing.denominator (q : Outgoing ι) (w : ℝ) : ℝ :=
  ∑ e ∈ q.labels, q.base e * Real.exp (-(w * q.gap e))

def Outgoing.maxWeight (q : Outgoing ι) : ℝ :=
  ∑ e ∈ q.labels, if q.gap e = 0 then q.base e else 0

def Outgoing.probability (q : Outgoing ι) (w : ℝ) (e : ι) : ℝ :=
  q.base e * Real.exp (-(w * q.gap e)) / q.denominator w

theorem Outgoing.denominator_pos (q : Outgoing ι) (w : ℝ) : 0 < q.denominator w := by
  obtain ⟨e, he, _⟩ := q.has_maximizer
  exact Finset.sum_pos' (fun j hj => (mul_pos (q.base_pos j hj) (Real.exp_pos _)).le)
    ⟨e, he, mul_pos (q.base_pos e he) (Real.exp_pos _)⟩

theorem Outgoing.maxWeight_pos (q : Outgoing ι) : 0 < q.maxWeight := by
  obtain ⟨e, he, hg⟩ := q.has_maximizer
  refine Finset.sum_pos' (fun j hj => ?_) ⟨e, he, ?_⟩
  · split_ifs
    · exact (q.base_pos j hj).le
    · exact le_rfl
  · simpa only [hg, ite_true] using q.base_pos e he

theorem tendsto_gap_exp (g : ℝ) (hg : 0 ≤ g) :
    Tendsto (fun w : ℝ => Real.exp (-(w * g))) atTop (𝓝 (if g = 0 then 1 else 0)) := by
  rcases hg.eq_or_lt with he | hp
  · simp [← he]
  · rw [ite_eq_right hp.ne']
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_mul_const_atTop_of_pos hp).2 tendsto_id)

theorem Outgoing.denominator_limit (q : Outgoing ι) :
    Tendsto q.denominator atTop (𝓝 q.maxWeight) := by
  unfold Outgoing.denominator Outgoing.maxWeight
  apply tendsto_finsetSum
  intro e he
  have h := (tendsto_gap_exp (q.gap e) (q.gap_nonneg e he)).const_mul (q.base e)
  convert h using 1
  by_cases hzero : q.gap e = 0 <;> simp [hzero]

/-- At a single step zero-gap labels divide the limiting mass in proportion to
their base weights, and positive-gap labels vanish. -/
theorem Outgoing.probability_limit (q : Outgoing ι) {e : ι} (he : e ∈ q.labels) :
    Tendsto (fun w => q.probability w e) atTop
      (𝓝 (if q.gap e = 0 then q.base e / q.maxWeight else 0)) := by
  have h := ((tendsto_gap_exp (q.gap e) (q.gap_nonneg e he)).const_mul (q.base e)).div
    q.denominator_limit q.maxWeight_pos.ne'
  change Tendsto (fun w => q.base e * Real.exp (-(w * q.gap e)) / q.denominator w)
    atTop (𝓝 ((q.base e * (if q.gap e = 0 then 1 else 0)) / q.maxWeight)) at h
  by_cases hg : q.gap e = 0 <;> simpa [Outgoing.probability, hg] using h

def Outgoing.ofRatios (labels : Finset ι) (base ratio : ι → ℝ) (best : ℝ)
    (base_pos : ∀ e ∈ labels, 0 < base e) (ratio_pos : ∀ e ∈ labels, 0 < ratio e)
    (upper : ∀ e ∈ labels, ratio e ≤ best) (attained : ∃ e ∈ labels, ratio e = best) :
    Outgoing ι where
  labels := labels
  base := base
  gap e := Real.log (best / ratio e)
  base_pos := base_pos
  gap_nonneg e he := Real.log_nonneg ((le_div_iff₀ (ratio_pos e he)).2 (by simpa using upper e he))
  has_maximizer := by
    obtain ⟨e, he, hr⟩ := attained
    exact ⟨e, he, by simp [← hr, (ratio_pos e he).ne']⟩

theorem gap_zero_iff_maximizer {ratio best : ℝ} (h₁ : 0 < ratio) (h₂ : 0 < best) :
    Real.log (best / ratio) = 0 ↔ ratio = best := by
  constructor
  · intro h
    have hd := Real.eq_one_of_pos_of_log_eq_zero (div_pos h₂ h₁) h
    exact ((div_eq_one_iff_eq (ne_of_gt h₁)).1 hd).symm
  · intro h
    simp [h, h₂.ne']

/-- The log gaps encode the original normalized weights `base * ratio ^ w`.
The common baseline `best ^ w` cancels. -/
theorem Outgoing.probability_eq_rpow (q : Outgoing ι) (ratio : ι → ℝ) (best : ℝ)
    (best_pos : 0 < best) (ratio_pos : ∀ e ∈ q.labels, 0 < ratio e)
    (gap_eq : ∀ e ∈ q.labels, q.gap e = Real.log (best / ratio e))
    (w : ℝ) {e : ι} (he : e ∈ q.labels) :
    q.probability w e =
      q.base e * ratio e ^ w / ∑ j ∈ q.labels, q.base j * ratio j ^ w := by
  have factor : ∀ j ∈ q.labels, q.base j * ratio j ^ w =
      Real.exp (w * Real.log best) * (q.base j * Real.exp (-(w * q.gap j))) := by
    intro j hj
    rw [Real.rpow_def_of_pos (ratio_pos j hj), gap_eq j hj,
      Real.log_div best_pos.ne' (ratio_pos j hj).ne']
    calc
      _ = q.base j * Real.exp (w * Real.log best + -(w * (Real.log best - Real.log (ratio j)))) := by
        congr 2
        ring
      _ = _ := by rw [Real.exp_add]; ring
  have hsum : (∑ j ∈ q.labels, q.base j * ratio j ^ w) =
      Real.exp (w * Real.log best) * q.denominator w := by
    rw [Outgoing.denominator, Finset.mul_sum]
    exact Finset.sum_congr rfl factor
  rw [hsum, factor e he, Outgoing.probability]
  field_simp [(Real.exp_pos (w * Real.log best)).ne', (q.denominator_pos w).ne']

theorem tendsto_normalized_rpow (labels : Finset ι) (base ratio : ι → ℝ) (best : ℝ)
    (base_pos : ∀ e ∈ labels, 0 < base e) (ratio_pos : ∀ e ∈ labels, 0 < ratio e)
    (upper : ∀ e ∈ labels, ratio e ≤ best) (attained : ∃ e ∈ labels, ratio e = best)
    {e : ι} (he : e ∈ labels) :
    Tendsto (fun w : ℝ => base e * ratio e ^ w / ∑ j ∈ labels, base j * ratio j ^ w) atTop
      (𝓝 (if ratio e = best then base e / ∑ j ∈ labels, (if ratio j = best then base j else 0)
        else 0)) := by
  let q := Outgoing.ofRatios labels base ratio best base_pos ratio_pos upper attained
  have hb : 0 < best := (ratio_pos e he).trans_le (upper e he)
  have hz : ∀ j ∈ labels, q.gap j = 0 ↔ ratio j = best := fun j hj =>
    gap_zero_iff_maximizer (ratio_pos j hj) hb
  have hm : q.maxWeight = ∑ j ∈ labels, (if ratio j = best then base j else 0) := by
    change (∑ j ∈ labels, if q.gap j = 0 then base j else 0) = _
    exact Finset.sum_congr rfl (fun j hj => if_congr (hz j hj) rfl rfl)
  have hl := q.probability_limit (e := e) he
  have hbase : q.base = base := rfl
  have hlabels : q.labels = labels := rfl
  simp only [hz e he, hm, hbase] at hl
  refine hl.congr (fun w => ?_)
  simpa only [hbase, hlabels] using
    q.probability_eq_rpow ratio best hb ratio_pos (fun _ _ => rfl) w he

/-- Every outgoing guidance ratio has the same parent posterior in its
denominator. It cancels when measuring the gap from the best child. -/
theorem posterior_gap (parent child bestChild : ℝ) (hp : 0 < parent) (hc : 0 < child) :
    Real.log ((bestChild / parent) / (child / parent)) = Real.log (bestChild / child) := by
  congr 1
  field_simp [hp.ne', hc.ne']

/-- A finite admissible path, along with the entire list of choices competing
with its selected edge at each step. -/
structure RevealPath (n : ℕ) (ι : Type*) where
  outgoing : Fin n → Outgoing ι
  edge : Fin n → ι
  admissible : ∀ k, edge k ∈ (outgoing k).labels

variable {n : ℕ}

def RevealPath.cost (p : RevealPath n ι) : ℝ :=
  ∑ k, (p.outgoing k).gap (p.edge k)

theorem RevealPath.cost_nonneg (p : RevealPath n ι) : 0 ≤ p.cost :=
  Finset.sum_nonneg (fun k _ => (p.outgoing k).gap_nonneg _ (p.admissible k))

theorem RevealPath.cost_eq_zero_iff (p : RevealPath n ι) :
    p.cost = 0 ↔ ∀ k, (p.outgoing k).gap (p.edge k) = 0 := by
  unfold RevealPath.cost
  simpa using (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun k => (p.outgoing k).gap (p.edge k))
    (fun k _ => (p.outgoing k).gap_nonneg _ (p.admissible k)))

def RevealPath.probability (p : RevealPath n ι) (w : ℝ) : ℝ :=
  ∏ k, (p.outgoing k).probability w (p.edge k)

def RevealPath.coefficient (p : RevealPath n ι) (w : ℝ) : ℝ :=
  ∏ k, (p.outgoing k).base (p.edge k) / (p.outgoing k).denominator w

def RevealPath.limitCoefficient (p : RevealPath n ι) : ℝ :=
  ∏ k, (p.outgoing k).base (p.edge k) / (p.outgoing k).maxWeight

theorem RevealPath.limitCoefficient_pos (p : RevealPath n ι) : 0 < p.limitCoefficient := by
  exact Finset.prod_pos (fun k _ => div_pos ((p.outgoing k).base_pos _ (p.admissible k))
    (p.outgoing k).maxWeight_pos)

theorem RevealPath.coefficient_limit (p : RevealPath n ι) :
    Tendsto p.coefficient atTop (𝓝 p.limitCoefficient) := by
  unfold RevealPath.coefficient RevealPath.limitCoefficient
  apply tendsto_finsetProd
  intro k _
  exact tendsto_const_nhds.div (p.outgoing k).denominator_limit (p.outgoing k).maxWeight_pos.ne'

theorem RevealPath.probability_factorization (p : RevealPath n ι) (w : ℝ) :
    p.probability w = p.coefficient w * Real.exp (-(w * p.cost)) := by
  unfold RevealPath.probability RevealPath.coefficient RevealPath.cost
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  unfold Outgoing.probability
  ring

variable {ω : Type*}

def endpointMass (paths : Finset ω) (path : ω → RevealPath n ι) (w : ℝ) : ℝ :=
  ∑ a ∈ paths, (path a).probability w

def endpointCoefficient (paths : Finset ω) (path : ω → RevealPath n ι) (minimum : ℝ) : ℝ :=
  ∑ a ∈ paths, if (path a).cost = minimum then (path a).limitCoefficient else 0

/-- Multiplying terminal mass by the exponential of the minimum path cost
leaves a strictly positive limit, given by the sum over all minimum-cost paths.
This applies to arbitrary finite path indices, including reveal permutations. -/
theorem endpoint_leakage (paths : Finset ω) (path : ω → RevealPath n ι) (minimum : ℝ)
    (below : ∀ a ∈ paths, minimum ≤ (path a).cost)
    (attained : ∃ a ∈ paths, (path a).cost = minimum) :
    Tendsto (fun w => Real.exp (w * minimum) * endpointMass paths path w) atTop
      (𝓝 (endpointCoefficient paths path minimum)) ∧
      0 < endpointCoefficient paths path minimum := by
  constructor
  · simp only [endpointMass, endpointCoefficient, Finset.mul_sum]
    apply tendsto_finsetSum
    intro a ha
    have h := ((path a).coefficient_limit).mul
      (tendsto_gap_exp ((path a).cost - minimum) (sub_nonneg.mpr (below a ha)))
    simp only [sub_eq_zero] at h
    by_cases hzero : (path a).cost = minimum
    · simp only [hzero, ite_true, mul_one] at h ⊢
      apply h.congr
      intro w
      rw [(path a).probability_factorization, ← mul_assoc, mul_comm (Real.exp (w * minimum)),
        mul_assoc, ← Real.exp_add]
      rw [hzero]
      simp
    · simp only [hzero, ite_false, mul_zero] at h ⊢
      apply h.congr
      intro w
      rw [(path a).probability_factorization, ← mul_assoc, mul_comm (Real.exp (w * minimum)),
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
  · unfold endpointCoefficient
    obtain ⟨a, ha, heq⟩ := attained
    refine Finset.sum_pos' (fun b _ => ?_) ⟨a, ha, ?_⟩
    · split_ifs
      · exact (path b).limitCoefficient_pos.le
      · exact le_rfl
    · simpa only [heq, ite_true] using (path a).limitCoefficient_pos

theorem endpointMass_pos (paths : Finset ω) (path : ω → RevealPath n ι)
    (nonempty : paths.Nonempty) (w : ℝ) : 0 < endpointMass paths path w := by
  have h : ∀ a ∈ paths, 0 < (path a).probability w := by
    intro a _
    apply Finset.prod_pos
    intro k _
    exact div_pos (mul_pos ((path a).outgoing k |>.base_pos _ ((path a).admissible k))
      (Real.exp_pos _)) (((path a).outgoing k).denominator_pos w)
  obtain ⟨a, ha⟩ := nonempty
  exact Finset.sum_pos' (fun b hb => (h b hb).le) ⟨a, ha, h a ha⟩

def minimumCost (paths : Finset ω) (path : ω → RevealPath n ι) (nonempty : paths.Nonempty) : ℝ := by
  classical
  exact (paths.image (fun a => (path a).cost)).min' (nonempty.image _)

theorem minimumCost_spec (paths : Finset ω) (path : ω → RevealPath n ι)
    (nonempty : paths.Nonempty) :
    (∀ a ∈ paths, minimumCost paths path nonempty ≤ (path a).cost) ∧
    (∃ a ∈ paths, (path a).cost = minimumCost paths path nonempty) := by
  classical
  unfold minimumCost
  exact ⟨fun a ha => Finset.min'_le _ _ (Finset.mem_image_of_mem _ ha),
    Finset.mem_image.1 (Finset.min'_mem _ _)⟩

theorem minimumCost_eq_zero_iff (paths : Finset ω) (path : ω → RevealPath n ι)
    (nonempty : paths.Nonempty) : minimumCost paths path nonempty = 0 ↔
    ∃ a ∈ paths, ∀ k, ((path a).outgoing k).gap ((path a).edge k) = 0 := by
  obtain ⟨hb, a, ha, hamin⟩ := minimumCost_spec paths path nonempty
  constructor
  · intro hz
    exact ⟨a, ha, (path a).cost_eq_zero_iff.1 (hamin.trans hz)⟩
  · rintro ⟨b, hbp, hzg⟩
    exact le_antisymm ((hb b hbp).trans_eq ((path b).cost_eq_zero_iff.2 hzg))
      (hamin ▸ (path a).cost_nonneg)

/-- A terminal word has positive limiting mass exactly when some reveal order
has only locally maximizing choices. -/
theorem endpoint_limit (paths : Finset ω) (path : ω → RevealPath n ι)
    (nonempty : paths.Nonempty) :
    let minimum := minimumCost paths path nonempty
    Tendsto (endpointMass paths path) atTop
      (𝓝 (if minimum = 0 then endpointCoefficient paths path minimum else 0)) := by
  let minimum := minimumCost paths path nonempty
  change Tendsto (endpointMass paths path) atTop
    (𝓝 (if minimum = 0 then endpointCoefficient paths path minimum else 0))
  obtain ⟨hb, ha⟩ := minimumCost_spec paths path nonempty
  obtain ⟨hl, _⟩ := endpoint_leakage paths path minimum hb ha
  by_cases hz : minimum = 0
  · simpa [hz] using hl
  · obtain ⟨a, _, hamin⟩ := ha
    have hn : 0 ≤ minimum := by
      change 0 ≤ minimumCost paths path nonempty
      rw [← hamin]
      exact (path a).cost_nonneg
    have h := ((tendsto_gap_exp minimum hn).mul hl)
    rw [ite_eq_right hz, zero_mul] at h
    rw [ite_eq_right hz]
    apply h.congr
    intro w
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The endpoint's negative log probability divided by the guidance strength
converges to the least additive log gap among paths to that endpoint. -/
theorem endpoint_log_rate (paths : Finset ω) (path : ω → RevealPath n ι)
    (nonempty : paths.Nonempty) :
    Tendsto (fun w => -Real.log (endpointMass paths path w) / w) atTop
      (𝓝 (minimumCost paths path nonempty)) := by
  let minimum := minimumCost paths path nonempty
  obtain ⟨hb, ha⟩ := minimumCost_spec paths path nonempty
  obtain ⟨hl, hp⟩ := endpoint_leakage paths path minimum hb ha
  have hlog := (Real.continuousAt_log hp.ne').tendsto.comp hl
  have hratio := hlog.div_atTop (show Tendsto (fun w : ℝ => w) atTop atTop from tendsto_id)
  have hdiff := (tendsto_const_nhds (x := minimum)).sub hratio
  rw [sub_zero] at hdiff
  apply hdiff.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  change minimum - Real.log (Real.exp (w * minimum) * endpointMass paths path w) / w =
    -Real.log (endpointMass paths path w) / w
  rw [Real.log_mul (Real.exp_pos _).ne' (endpointMass_pos paths path nonempty w).ne', Real.log_exp]
  field_simp [hw.ne']
  ring

variable {Token : Type*}

/-- Coordinates strictly earlier than a step in the reveal permutation. -/
def revealedBefore (order : Equiv.Perm (Fin n)) (step : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun i => i < step)).image order

theorem next_not_revealed (order : Equiv.Perm (Fin n)) (step : Fin n) :
    order step ∉ revealedBefore order step := by
  simp only [revealedBefore, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨i, hi, hei⟩
  exact (lt_irrefl step) (order.injective hei ▸ hi)

def stateBefore (word : Fin n → Token) (order : Equiv.Perm (Fin n)) (step : Fin n) :
    Fin n → Option Token :=
  fun j => if j ∈ revealedBefore order step then some (word j) else none

def orderPath (outgoing : (Fin n → Option Token) → Outgoing (Fin n × Token))
    (word : Fin n → Token)
    (feasible : ∀ (order : Equiv.Perm (Fin n)) (step : Fin n),
      (order step, word (order step)) ∈ (outgoing (stateBefore word order step)).labels)
    (order : Equiv.Perm (Fin n)) : RevealPath n (Fin n × Token) where
  outgoing step := outgoing (stateBefore word order step)
  edge step := (order step, word (order step))
  admissible step := feasible order step

/-- All reveal orders for a feasible complete word. Distinct permutations are
kept distinct even if they have the same additive cost. -/
def revealOrders (n : ℕ) : Finset (Equiv.Perm (Fin n)) := Finset.univ

theorem revealOrders_nonempty (n : ℕ) : (revealOrders n).Nonempty :=
  ⟨Equiv.refl _, Finset.mem_univ _⟩

/-- All permutations of the coordinates contribute to the terminal law. The
leading coefficient includes every minimizing order, so this also covers ties.
In masked diffusion the outgoing gap is `log (max_child_posterior / child_posterior)`
and the base weight is the conditional target probability of its revealed token. -/
theorem reveal_order_leakage
    (outgoing : (Fin n → Option Token) → Outgoing (Fin n × Token)) (word : Fin n → Token)
    (feasible : ∀ (order : Equiv.Perm (Fin n)) (step : Fin n),
      (order step, word (order step)) ∈ (outgoing (stateBefore word order step)).labels) :
    let paths := revealOrders n
    let path := orderPath outgoing word feasible
    let minimum := minimumCost paths path (revealOrders_nonempty n)
    Tendsto (fun w => Real.exp (w * minimum) * endpointMass paths path w) atTop
      (𝓝 (endpointCoefficient paths path minimum)) ∧
      0 < endpointCoefficient paths path minimum ∧
      Tendsto (fun w => -Real.log (endpointMass paths path w) / w) atTop (𝓝 minimum) := by
  dsimp only
  obtain ⟨hb, ha⟩ := minimumCost_spec (revealOrders n) (orderPath outgoing word feasible)
    (revealOrders_nonempty n)
  obtain ⟨hl, hp⟩ := endpoint_leakage (revealOrders n) (orderPath outgoing word feasible) _ hb ha
  exact ⟨hl, hp, endpoint_log_rate (revealOrders n) (orderPath outgoing word feasible)
    (revealOrders_nonempty n)⟩

end

end CFGSelection
