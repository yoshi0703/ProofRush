import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CanonneNearOne

open scoped BigOperators
noncomputable section

variable {α : Type*} [Fintype α]

structure IsLaw (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  total : ∑ a, p a = 1

def mass (q : α → ℝ) (s : Finset α) : ℝ := ∑ a ∈ s, q a

def totalVariation (p q : α → ℝ) : ℝ := (∑ a, |p a - q a|) / 2

theorem totalVariation_eq_one_sub_overlap {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) :
    totalVariation p q = 1 - ∑ a, min (p a) (q a) := by
  have h (a : α) : |p a - q a| = p a + q a - 2 * min (p a) (q a) := by
    rcases le_total (p a) (q a) with hl | hr
    · rw [abs_of_nonpos (sub_nonpos.mpr hl), min_eq_left hl]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr hr), min_eq_right hr]
      ring
  simp only [totalVariation, h, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp.total, hq.total]
  ring

variable [DecidableEq α]

def discard (q : α → ℝ) (removed : Finset α) (a : α) : ℝ :=
  if a ∈ removed then 0 else q a / (1 - mass q removed)

/-- Removing and renormalizing costs exactly the discarded reference mass
in one draw, including when some discarded or retained atoms are zero. -/
theorem discard_law_and_exact_tv {q : α → ℝ} (hq : IsLaw q) (removed : Finset α)
    (hsmall : mass q removed < 1) :
    IsLaw (discard q removed) ∧ totalVariation (discard q removed) q = mass q removed := by
  have hmass : 0 ≤ mass q removed := Finset.sum_nonneg (fun a _ => hq.nonneg a)
  have hretained : mass q removedᶜ = 1 - mass q removed := by
    have heq := Finset.sum_compl_add_sum removed q
    change mass q removedᶜ + mass q removed = ∑ a, q a at heq
    rw [hq.total] at heq
    linarith
  have hpos : 0 < 1 - mass q removed := sub_pos.mpr hsmall
  have hsplit (f : α → ℝ) :
      (∑ a, f a) = (∑ a ∈ removedᶜ, f a) + ∑ a ∈ removed, f a :=
    (Finset.sum_compl_add_sum removed f).symm
  have hkeep (a : α) (ha : a ∈ removedᶜ) : discard q removed a =
      q a / (1 - mass q removed) := by
    simp [discard, Finset.mem_compl.mp ha]
  have hs : ∀ a ∈ removed, discard q removed a = 0 := by
    intro a ha
    simp [discard, ha]
  have hLaw : IsLaw (discard q removed) := by
    constructor
    · intro a
      unfold discard
      split
      · exact le_rfl
      · exact div_nonneg (hq.nonneg a) hpos.le
    · rw [hsplit, Finset.sum_congr rfl hkeep, Finset.sum_congr rfl hs, Finset.sum_const_zero,
        add_zero]
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      change mass q removedᶜ * (1 - mass q removed)⁻¹ = 1
      rw [hretained, mul_inv_cancel₀ hpos.ne']
  refine ⟨hLaw, ?_⟩
  have hmkeep (a : α) (ha : a ∈ removedᶜ) :
      min (discard q removed a) (q a) = q a := by
    apply min_eq_right
    rw [hkeep a ha, le_div_iff₀ hpos]
    nlinarith [mul_nonneg (hq.nonneg a) hmass]
  have hmremoved (a : α) (ha : a ∈ removed) :
      min (discard q removed a) (q a) = 0 := by
    rw [hs a ha, min_eq_left (hq.nonneg a)]
  rw [totalVariation_eq_one_sub_overlap hLaw hq, hsplit,
    Finset.sum_congr rfl hmkeep, Finset.sum_congr rfl hmremoved, Finset.sum_const_zero, add_zero]
  change 1 - mass q removedᶜ = mass q removed
  rw [hretained]
  ring

def nearOneMoment (q : α → ℝ) (δ : ℝ) : ℝ :=
  ∑ a, q a * min 1 (Real.sqrt (q a / δ))

omit [DecidableEq α] in
/-- For the threshold δ/16, the discarded mass is at most four times the
truncated moment of the original null. -/
theorem heavy_mass_le_four_moment {q : α → ℝ} (hq : IsLaw q)
    {δ : ℝ} (hδ : 0 < δ) :
    mass q (Finset.univ.filter (fun a => δ / 16 < q a)) ≤ 4 * nearOneMoment q δ := by
  classical
  unfold mass nearOneMoment
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  split_ifs with h
  · have hquot : (1 / 16 : ℝ) ≤ q a / δ := by
      apply (le_div_iff₀ hδ).mpr
      linarith
    have hsqrt : 1 / 4 ≤ Real.sqrt (q a / δ) := by
      calc
        (1 / 4 : ℝ) = Real.sqrt (1 / 16) := by
          rw [show (1 / 16 : ℝ) = (1 / 4)^2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ _ := Real.sqrt_le_sqrt hquot
    have hm : 1 / 4 ≤ min 1 (Real.sqrt (q a / δ)) := le_min (by norm_num) hsqrt
    nlinarith [mul_le_mul_of_nonneg_left hm (hq.nonneg a)]
  · exact mul_nonneg (by norm_num)
      (mul_nonneg (hq.nonneg a) (le_min zero_le_one (Real.sqrt_nonneg _)))

variable {B : Type*} [Fintype B]

abbrev Slot (k : B → ℕ) := Σ b : B, Fin (k b)

/-- A deterministic finite list collection with bin tops u and lengths k.
A repeated label consumes multiple slots but is charged only once in its
reference support mass. -/
theorem support_mass_le_slot_cost {q : α → ℝ} (hq : IsLaw q)
    {k : B → ℕ} {u : B → ℝ} (x : Slot k → α)
    (htop : ∀ i, q (x i) ≤ u i.1) :
    mass q (Finset.univ.image x) ≤ ∑ b, (k b : ℝ) * u b := by
  classical
  have hpoint (a : α) :
      (if a ∈ Finset.univ.image x then q a else 0) ≤
        ∑ i : Slot k, if x i = a then q a else 0 := by
    by_cases ha : a ∈ Finset.univ.image x
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      rw [ite_eq_left ha]
      calc
        q a = (if x i = a then q a else 0) := (ite_eq_left hi).symm
        _ ≤ ∑ j : Slot k, if x j = a then q a else 0 :=
          Finset.single_le_sum
            (f := fun j : Slot k => if x j = a then q a else 0)
            (fun _ _ => by split <;> simp [hq.nonneg a]) (Finset.mem_univ i)
    · rw [ite_eq_right ha]
      exact Finset.sum_nonneg fun i _ => by split <;> simp [hq.nonneg a]
  calc
    _ = ∑ a, if a ∈ Finset.univ.image x then q a else 0 := by
      unfold mass
      rw [← Finset.sum_filter]
      congr
      ext a
      simp
    _ ≤ ∑ a, ∑ i : Slot k, if x i = a then q a else 0 := Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ∑ i : Slot k, q (x i) := by
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ i : Slot k, u i.1 := Finset.sum_le_sum fun i _ => htop i
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp [nsmul_eq_mul]

/-- The strict alternative follows pathwise from the list budget. The candidate law
may allocate any nonnegative mass to the selected labels and may repeat a label
in its lists. The test threshold is exactly 1 − δ. -/
theorem strict_far_of_pilot_support_budget {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {δ : ℝ} {k : B → ℕ} {u : B → ℝ} (x : Slot k → α)
    (htop : ∀ i, q (x i) ≤ u i.1)
    (hvanish : ∀ a ∉ Finset.univ.image x, p a = 0)
    (hbudget : (∑ b, (k b : ℝ) * u b) < δ) :
    1 - δ < totalVariation p q := by
  classical
  let used : Finset α := Finset.univ.image x
  have hoverlap : (∑ a, min (p a) (q a)) ≤ mass q used := by
    rw [← Finset.sum_compl_add_sum used]
    have hvanishing : ∑ a ∈ usedᶜ, min (p a) (q a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hvanish a (Finset.mem_compl.mp ha), min_eq_left (hq.nonneg a)]
    rw [hvanishing, zero_add]
    exact Finset.sum_le_sum fun a _ => min_le_right _ _
  rw [totalVariation_eq_one_sub_overlap hp hq]
  have hmass : mass q used < δ := (support_mass_le_slot_cost hq x htop).trans_lt hbudget
  linarith

/-- The exact ceiling rule used for empirical lists within the light bins. -/
def pilotCount (n δ : ℝ) (b u : B → ℝ) (j : B) : ℕ :=
  ⌈n * Real.sqrt δ * b j / Real.sqrt (u j)⌉₊

/-- Rounding the pilot size contributes at most one additional bin top,
uniformly even if every bin has its own fractional target. -/
theorem rounded_pilot_cost_le {n δ : ℝ} {b u : B → ℝ}
    (hn : 0 ≤ n) (hb : ∀ j, 0 ≤ b j) (hu : ∀ j, 0 < u j) :
    (∑ j, (pilotCount n δ b u j : ℝ) * u j) ≤
      n * Real.sqrt δ * (∑ j, b j * Real.sqrt (u j)) + ∑ j, u j := by
  calc
    _ ≤ ∑ j, (n * Real.sqrt δ * b j / Real.sqrt (u j) + 1) * u j := by
      apply Finset.sum_le_sum
      intro j _
      have hp : 0 ≤ n * Real.sqrt δ * b j / Real.sqrt (u j) :=
        div_nonneg (mul_nonneg (mul_nonneg hn (Real.sqrt_nonneg δ)) (hb j))
          (Real.sqrt_nonneg (u j))
      exact mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hp).le (hu j).le
    _ = _ := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hs : (Real.sqrt (u j)) ^ 2 = u j := Real.sq_sqrt (hu j).le
      have hne := (Real.sqrt_pos.2 (hu j)).ne'
      have hdiv : u j / Real.sqrt (u j) = Real.sqrt (u j) :=
        (div_eq_iff hne).mpr (by simpa only [pow_two] using hs.symm)
      calc
        _ = n * Real.sqrt δ * b j * (u j / Real.sqrt (u j)) + u j := by ring
        _ = _ := by rw [hdiv]; ring

/-- Applying the ceiling rule to the two summable charges in the near-one
construction yields strict separation of every finite planted law. -/
theorem strict_far_of_rounded_pilots {p q : α → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {δ n : ℝ} (hδ : 0 < δ) (hn : 0 ≤ n) {b u : B → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hu : ∀ j, 0 < u j)
    (x : Slot (pilotCount n δ b u) → α)
    (htop : ∀ i, q (x i) ≤ u i.1)
    (hvanish : ∀ a ∉ Finset.univ.image x, p a = 0)
    (hmoment : n * Real.sqrt δ * (∑ j, b j * Real.sqrt (u j)) ≤ δ / 16)
    (hgeometric : (∑ j, u j) ≤ δ / 8) :
    1 - δ < totalVariation p q := by
  apply strict_far_of_pilot_support_budget hp hq x htop hvanish
  exact (rounded_pilot_cost_le hn hb hu).trans_lt (by linarith)

/-- Null mass of a light bin after dividing by the mass retained. The assignment
may omit null-zero labels and is single-valued, hence no label is double counted. -/
def normalizedBinMass (q : α → ℝ) (retained : ℝ) (bin : α → Option B)
    [DecidableEq B] (j : B) : ℝ :=
  ∑ a, if bin a = some j then q a / retained else 0

omit [DecidableEq α] in
/-- Dyadic lower endpoints and retained mass at least one half suffice to
control the renormalized light-bin charge by the original moment. -/
theorem normalized_light_charge_le {q : α → ℝ} (hq : IsLaw q) {δ retained : ℝ}
    (hδ : 0 < δ) (hret : 1 / 2 ≤ retained) [DecidableEq B]
    (bin : α → Option B) (u : B → ℝ) (hu : ∀ j, 0 < u j)
    (hlight : ∀ a j, bin a = some j → q a ≤ δ)
    (hdyadic : ∀ a j, bin a = some j → u j ≤ 2 * q a) :
    Real.sqrt δ *
      (∑ j, normalizedBinMass q retained bin j * Real.sqrt (u j)) ≤
      4 * δ * nearOneMoment q δ := by
  have hpos : 0 < retained := by linarith
  unfold nearOneMoment
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [normalizedBinMass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  cases hg : bin a with
  | none =>
    simp only [reduceCtorEq, ite_false, zero_mul, mul_zero, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) (mul_nonneg (hq.nonneg a)
      (le_min zero_le_one (Real.sqrt_nonneg _)))
  | some j =>
    have hs : Real.sqrt (q a / δ) ≤ 1 := by
      calc
        _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ((div_le_iff₀ hδ).mpr (by simpa using hlight a j hg))
        _ = _ := Real.sqrt_one
    have hb : q a / retained ≤ 2 * q a := by
      apply (div_le_iff₀ hpos).mpr
      nlinarith [mul_nonneg (hq.nonneg a) (sub_nonneg.mpr hret)]
    have hsqrt : Real.sqrt δ * Real.sqrt (u j) ≤ 2 * δ * Real.sqrt (q a / δ) := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow (Real.sqrt δ), Real.sq_sqrt hδ.le, Real.sq_sqrt (hu j).le,
        mul_pow (2 * δ), Real.sq_sqrt (div_nonneg (hq.nonneg a) hδ.le)]
      have hid : (2 * δ) ^ 2 * (q a / δ) = 4 * δ * q a := by
        field_simp
        ring
      rw [hid]
      nlinarith [mul_le_mul_of_nonneg_left (hdyadic a j hg) hδ.le, mul_nonneg hδ.le (hq.nonneg a)]
    simp only [Option.some.injEq, ite_mul, mul_ite, zero_mul, min_eq_right hs]
    calc
      _ = Real.sqrt δ * (q a / retained) * Real.sqrt (u j) := by
        classical
        rw [Finset.sum_eq_single j]
        · simp [mul_assoc]
        · intro i _ hi
          simp [Ne.symm hi]
        · simp
      _ = (q a / retained) * (Real.sqrt δ * Real.sqrt (u j)) := by ring
      _ ≤ (2 * q a) * (2 * δ * Real.sqrt (q a / δ)) := by
        exact mul_le_mul hb hsqrt (by positivity) (mul_nonneg (by norm_num) (hq.nonneg a))
      _ = _ := by ring

/-- If nJ ≤ 1/64, discarding q_i > δ/16 leaves at least 15/16 of q.
For any resulting dyadic light bins, the marked ceiling scheme gives a strict
alternative from every possible pilot tuple. -/
theorem strict_far_at_small_near_one_moment {p q : α → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) {δ n : ℝ} (hδ : 0 < δ) (hn : 1 ≤ n)
    (hsmall : n * nearOneMoment q δ ≤ 1 / 64) [DecidableEq B]
    (bin : α → Option B) (u : B → ℝ) (hu : ∀ j, 0 < u j)
    (hlight : ∀ a j, bin a = some j → q a ≤ δ / 16)
    (hdyadic : ∀ a j, bin a = some j → u j ≤ 2 * q a)
    (hgeometric : (∑ j, u j) ≤ δ / 8)
    (x : Slot (pilotCount n δ
      (normalizedBinMass q (1 - mass q (Finset.univ.filter (fun a => δ / 16 < q a))) bin) u) → α)
    (htop : ∀ i, q (x i) ≤ u i.1)
    (hvanish : ∀ a ∉ Finset.univ.image x, p a = 0) :
    1 - δ < totalVariation p q := by
  have hj : 0 ≤ nearOneMoment q δ := by
    unfold nearOneMoment
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hq.nonneg a)
      (le_min zero_le_one (Real.sqrt_nonneg _))
  have hjbound : nearOneMoment q δ ≤ 1 / 64 :=
    (le_mul_of_one_le_left hj hn).trans hsmall
  have hret : 1 / 2 ≤ 1 - mass q (Finset.univ.filter (fun a => δ / 16 < q a)) := by
    have hheavy := heavy_mass_le_four_moment hq hδ
    linarith
  have hb (j : B) : 0 ≤ normalizedBinMass q
      (1 - mass q (Finset.univ.filter (fun a => δ / 16 < q a))) bin j := by
    unfold normalizedBinMass
    apply Finset.sum_nonneg
    intro a _
    split
    · exact div_nonneg (hq.nonneg a) (by linarith)
    · exact le_rfl
  apply strict_far_of_rounded_pilots hp hq hδ (by linarith) hb hu x htop hvanish _ hgeometric
  have hlight' (a : α) (j : B) (hg : bin a = some j) : q a ≤ δ := by
    have := hlight a j hg
    linarith
  have hcharge := normalized_light_charge_le hq hδ hret bin u hu hlight' hdyadic
  calc
    _ = n * (Real.sqrt δ * _) := by ring
    _ ≤ n * (4 * δ * nearOneMoment q δ) := mul_le_mul_of_nonneg_left hcharge (by linarith)
    _ = 4 * δ * (n * nearOneMoment q δ) := by ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsmall hδ.le]

end
end CanonneNearOne
