import BirthdayCoupling
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {A : Type*}

def tailOverlap (T : Finset A) (p q : A → ℝ) : ℝ :=
  ∑ i ∈ T, min (p i) (q i)

def tailScore (T : Finset A) (p q : A → ℝ) : ℝ :=
  ∑ i ∈ T, p i * Real.sqrt (q i)

def tailSquareMass (T : Finset A) (p : A → ℝ) : ℝ :=
  ∑ i ∈ T, (p i)^2

/-- A large observed-law score at small reference overlap requires a
large collision probability, for arbitrary finite subprobabilities. -/
theorem excess_score_forces_tail_collision (T : Finset A) (p q : A → ℝ) {b z : ℝ}
    (hp : ∀ i ∈ T, 0 ≤ p i) (hq : ∀ i ∈ T, 0 ≤ q i)
    (hmax : ∀ i ∈ T, q i ≤ b) (hz : 0 ≤ z)
    (hscore : z + Real.sqrt b * tailOverlap T p q ≤ tailScore T p q) :
    z^2 ≤ tailOverlap T p q * tailSquareMass T p := by
  classical
  let rich := T.filter fun i => q i ≤ p i
  let light := T.filter fun i => ¬q i ≤ p i
  have light_sub : light ⊆ T := Finset.filter_subset _ _
  have rich_sub : rich ⊆ T := Finset.filter_subset _ _
  have overlap_nonneg (i : A) (hi : i ∈ T) : 0 ≤ min (p i) (q i) :=
    le_min (hp i hi) (hq i hi)
  have light_mass : ∑ i ∈ light, p i ≤ tailOverlap T p q := by
    unfold tailOverlap
    calc
      _ = ∑ i ∈ light, min (p i) (q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (min_eq_left (le_of_not_ge ((Finset.mem_filter.mp hi).2))).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg light_sub (fun i hi _ => overlap_nonneg i hi)
  have rich_mass : ∑ i ∈ rich, q i ≤ tailOverlap T p q := by
    unfold tailOverlap
    calc
      _ = ∑ i ∈ rich, min (p i) (q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (min_eq_right ((Finset.mem_filter.mp hi).2)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg rich_sub (fun i hi _ => overlap_nonneg i hi)
  have small_score : ∑ i ∈ light, p i * Real.sqrt (q i) ≤
      Real.sqrt b * tailOverlap T p q := by
    calc
      _ ≤ ∑ i ∈ light, p i * Real.sqrt b :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hmax i (light_sub hi))) (hp i (light_sub hi)))
      _ = (∑ i ∈ light, p i) * Real.sqrt b := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := by
        rw [mul_comm (Real.sqrt b)]
        exact mul_le_mul_of_nonneg_right light_mass (Real.sqrt_nonneg b)
  have split_score : (∑ i ∈ rich, p i * Real.sqrt (q i)) +
      (∑ i ∈ light, p i * Real.sqrt (q i)) = tailScore T p q :=
    Finset.sum_filter_add_sum_filter_not T (fun i => q i ≤ p i) _
  have rich_score : z ≤ ∑ i ∈ rich, p i * Real.sqrt (q i) := by linarith
  have rich_squares : ∑ i ∈ rich, (p i)^2 ≤ tailSquareMass T p :=
    Finset.sum_le_sum_of_subset_of_nonneg rich_sub (fun i _ _ => sq_nonneg (p i))
  have cs := Finset.sum_mul_sq_le_sq_mul_sq rich p (fun i => Real.sqrt (q i))
  have sqrt_sq : ∑ i ∈ rich, (Real.sqrt (q i))^2 = ∑ i ∈ rich, q i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hq i (rich_sub hi)))
  rw [sqrt_sq] at cs
  calc
    _ ≤ (∑ i ∈ rich, p i * Real.sqrt (q i))^2 := pow_le_pow_left₀ hz rich_score 2
    _ ≤ (∑ i ∈ rich, (p i)^2) * ∑ i ∈ rich, q i := cs
    _ ≤ tailSquareMass T p * tailOverlap T p q :=
      mul_le_mul rich_squares rich_mass
        (Finset.sum_nonneg (fun i hi => hq i (rich_sub hi)))
        (Finset.sum_nonneg (fun i _ => sq_nonneg (p i)))
    _ = _ := mul_comm _ _

/-- The raw second moment of a weighted tail observation is bounded by
sqrt of the reference cap times its first moment. -/
theorem tail_score_second_moment (T : Finset A) (p q : A → ℝ) {b : ℝ}
    (hp : ∀ i ∈ T, 0 ≤ p i)
    (hmax : ∀ i ∈ T, q i ≤ b) :
    ∑ i ∈ T, p i * (Real.sqrt (q i))^2 ≤ Real.sqrt b * tailScore T p q := by
  rw [tailScore, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hmax i hi))
    (mul_nonneg (hp i hi) (Real.sqrt_nonneg (q i)))
  calc
    _ = Real.sqrt (q i) * (p i * Real.sqrt (q i)) := by ring
    _ ≤ _ := h

variable [Fintype A] [DecidableEq A]

/-- An exact two-position repeat probability in an actual ordered iid law. -/
theorem tail_pair_probability {n : ℕ} (T : Finset A) {p : A → ℝ}
    (hp : IsLaw p) {i j : Fin n} (hne : i ≠ j) :
    eventMass (pilotLaw p) (fun x : Fin n → A => x i = x j ∧ x i ∈ T) =
      tailSquareMass T p := by
  classical
  rw [eventMass_eq_sum]
  have pointwise (x : Fin n → A) :
      (if x i = x j ∧ x i ∈ T then pilotLaw p x else 0) =
        ∑ a ∈ T, if x i = a ∧ x j = a then pilotLaw p x else 0 := by
    by_cases h : x i = x j
    · simp only [← h, and_self, true_and]
      simp [eq_comm]
    · have contra (a : A) : ¬(x i = a ∧ x j = a) :=
        fun ha => h (ha.1.trans ha.2.symm)
      simp [h, contra]
  simp only [pointwise, Finset.sum_comm (s := Finset.univ)]
  unfold tailSquareMass
  apply Finset.sum_congr rfl
  intro a _
  rw [← eventMass_eq_sum, two_coordinate_event hp hne]
  ring

/-- Expected number of unordered repeated tail pairs, computed exactly. -/
theorem expected_tail_pairs {n : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    (∑ x : Fin n → A, pilotLaw p x *
      ∑ z ∈ orderedPairs n, (if x z.1 = x z.2 ∧ x z.1 ∈ T then 1 else 0 : ℝ)) =
      (n.choose 2 : ℝ) * tailSquareMass T p := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z ∈ orderedPairs n,
        eventMass (pilotLaw p) (fun x : Fin n → A => x z.1 = x z.2 ∧ x z.1 ∈ T) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp_all
    _ = _ := by
      have step (z : Fin n × Fin n) (hz : z ∈ orderedPairs n) :
          eventMass (pilotLaw p) (fun x : Fin n → A => x z.1 = x z.2 ∧ x z.1 ∈ T) =
            tailSquareMass T p :=
        tail_pair_probability T hp (Finset.mem_filter.mp hz).2.ne
      rw [Finset.sum_congr rfl step]
      simp [orderedPairs_card, nsmul_eq_mul]

/-- The union bound giving the actual null probability of the repeat gate. -/
theorem any_tail_repeat_le {n : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    eventMass (pilotLaw p)
      (fun x : Fin n → A => ∃ z ∈ orderedPairs n, x z.1 = x z.2 ∧ x z.1 ∈ T) ≤
      (n.choose 2 : ℝ) * tailSquareMass T p := by
  classical
  refine (eventMass_union_le _ (pilotLaw_isLaw hp).nonneg (orderedPairs n) _).trans ?_
  have exact_pair (z : Fin n × Fin n) (hz : z ∈ orderedPairs n) :
      eventMass (pilotLaw p) (fun x : Fin n → A => x z.1 = x z.2 ∧ x z.1 ∈ T) =
        tailSquareMass T p :=
    tail_pair_probability T hp (Finset.mem_filter.mp hz).2.ne
  rw [Finset.sum_congr rfl exact_pair]
  simp [orderedPairs_card, nsmul_eq_mul]

/-- An exact higher repeat moment. At any nonempty collection of distinct
positions, the probability that all their labels equal one tail label is
the corresponding power sum of the original tail subprobability. -/
theorem tail_repeat_power_probability {m n : ℕ} (hm : 0 < m) (T : Finset A)
    {p : A → ℝ} (hp : IsLaw p) (f : Fin m → Fin n) (hinj : Function.Injective f) :
    eventMass (pilotLaw p) (fun x : Fin n → A => ∃ a ∈ T, ∀ i, x (f i) = a) =
      ∑ a ∈ T, (p a)^m := by
  classical
  rw [eventMass_eq_sum]
  have pointwise (x : Fin n → A) :
      (if ∃ a ∈ T, ∀ i, x (f i) = a then pilotLaw p x else 0) =
        ∑ a ∈ T, if ∀ i, x (f i) = a then pilotLaw p x else 0 := by
    by_cases he : ∃ a ∈ T, ∀ i, x (f i) = a
    · obtain ⟨a, ha, hx⟩ := he
      rw [ite_eq_left (show ∃ b ∈ T, ∀ i, x (f i) = b from ⟨a, ha, hx⟩)]
      rw [Finset.sum_eq_single_of_mem a ha]
      · simp [hx]
      · intro b _ hba
        have no : ¬∀ i, x (f i) = b := by
          intro hh
          let zero : Fin m := ⟨0, hm⟩
          exact hba ((hh zero).symm.trans (hx zero))
        simp [no]
    · rw [ite_eq_right he]
      refine (Finset.sum_eq_zero ?_).symm
      intro a ha
      exact ite_eq_right (fun hx => he ⟨a, ha, hx⟩)
  simp only [pointwise, Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← eventMass_eq_sum, injective_pilot_draws hp f hinj (fun _ => a)]
  simp [pilotLaw]

/-- Disjoint observation pairs have zero repeat-indicator covariance. The
two pair labels may coincide, but the four positions are distinct. -/
theorem disjoint_tail_pair_probability {n : ℕ} (T : Finset A) {p : A → ℝ}
    (hp : IsLaw p) (f : Fin 2 ⊕ Fin 2 → Fin n) (hinj : Function.Injective f) :
    eventMass (pilotLaw p) (fun x : Fin n → A => ∃ pair ∈ T ×ˢ T,
      ∀ i, x (f i) = Sum.elim (fun _ => pair.1) (fun _ => pair.2) i) =
      (tailSquareMass T p)^2 := by
  classical
  let P (x : Fin n → A) (pair : A × A) :=
    ∀ i, x (f i) = Sum.elim (fun _ : Fin 2 => pair.1) (fun _ : Fin 2 => pair.2) i
  change eventMass (pilotLaw p) (fun x => ∃ pair ∈ T ×ˢ T, P x pair) = _
  rw [eventMass_eq_sum]
  have pointwise (x : Fin n → A) :
      (if ∃ pair ∈ T ×ˢ T, P x pair then pilotLaw p x else 0) =
        ∑ pair ∈ T ×ˢ T, if P x pair then pilotLaw p x else 0 := by
    by_cases he : ∃ pair ∈ T ×ˢ T, P x pair
    · obtain ⟨pair, hpair, hx⟩ := he
      rw [ite_eq_left (show ∃ z ∈ T ×ˢ T, P x z from ⟨pair, hpair, hx⟩)]
      rw [Finset.sum_eq_single_of_mem pair hpair]
      · simp [hx]
      · intro z _ hz
        have hnp : ¬ P x z := by
          intro h
          apply hz
          apply Prod.ext
          · exact (h (Sum.inl 0)).symm.trans (hx (Sum.inl 0))
          · exact (h (Sum.inr 0)).symm.trans (hx (Sum.inr 0))
        simp [hnp]
    · rw [ite_eq_right he]
      refine (Finset.sum_eq_zero ?_).symm
      intro pair hpair
      exact ite_eq_right (fun hx => he ⟨pair, hpair, hx⟩)
  simp only [pointwise, Finset.sum_comm (s := Finset.univ)]
  have exactValues (pair : A × A) (_hpair : pair ∈ T ×ˢ T) :
      (∑ x : Fin n → A, if P x pair then pilotLaw p x else 0) =
        (p pair.1)^2 * (p pair.2)^2 := by
    rw [← eventMass_eq_sum]
    unfold P
    rw [injective_pilot_draws hp f hinj]
    simp [pilotLaw, Fintype.prod_sum_type]
  rw [Finset.sum_congr rfl exactValues, Finset.sum_product]
  unfold tailSquareMass
  rw [pow_two, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.mul_sum T (fun i => (p i)^2) ((p a)^2)).symm

end
end CanonneQuantile
