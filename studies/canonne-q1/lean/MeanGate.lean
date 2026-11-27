import WeightedTail

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem one_coordinate_expectation {n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    (i : Fin n) (g : A → ℝ) :
    (∑ x : Fin n → A, pilotLaw p x * g (x i)) = ∑ a, p a * g a := by
  classical
  let w (j : Fin n) (a : A) := if j = i then g a else 1
  have pointwise (x : Fin n → A) : (∏ j, w j (x j)) = g (x i) := by
    simp [w]
  have averaged (j : Fin n) :
      (∑ a, p a * w j a) = if j = i then (∑ a, p a * g a) else 1 := by
    by_cases h : j = i <;> simp [w, h, hp.total]
  calc
    _ = ∑ x : Fin n → A, pilotLaw p x * ∏ j, w j (x j) := by simp only [pointwise]
    _ = ∏ j, ∑ a, p a * w j a := pilot_weighted_product p w
    _ = _ := by simp [averaged]

omit [DecidableEq A] in
/-- Exact second centered moment of an iid sum of arbitrary real scores. -/
theorem centered_sum_second_moment {n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    (g : A → ℝ) (zeroMean : ∑ a, p a * g a = 0) :
    (∑ x : Fin n → A, pilotLaw p x * (∑ i, g (x i))^2) =
      (n : ℝ) * ∑ a, p a * (g a)^2 := by
  classical
  have crossed (i j : Fin n) :
      (∑ x : Fin n → A, pilotLaw p x * (g (x i) * g (x j))) =
        if i = j then ∑ a, p a * (g a)^2 else 0 := by
    by_cases he : i = j
    · subst j
      rw [ite_eq_left rfl]
      simpa only [pow_two] using one_coordinate_expectation hp i (fun a => g a * g a)
    · rw [pilot_two_marginal hp he g g, zeroMean]
      simp [he]
  calc
    _ = ∑ x : Fin n → A, ∑ i : Fin n, ∑ j : Fin n,
      pilotLaw p x * (g (x i) * g (x j)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → A,
      pilotLaw p x * (g (x i) * g (x j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      simp [crossed, nsmul_eq_mul]

omit [DecidableEq A] in
theorem finite_squared_deviation_bound {p : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (g : A → ℝ) {d : ℝ} (hd : 0 < d) :
    eventMass p (fun a => d ≤ |g a|) ≤ (∑ a, p a * (g a)^2) / d^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hd), eventMass_eq_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : d ≤ |g a|
  · rw [ite_eq_left h]
    have hs : d^2 ≤ (g a)^2 := by
      rw [← sq_abs (g a)]
      exact pow_le_pow_left₀ hd.le h 2
    exact mul_le_mul_of_nonneg_left hs (hp a)
  · rw [ite_eq_right h, zero_mul]
    exact mul_nonneg (hp a) (sq_nonneg (g a))

omit [DecidableEq A] in
/-- Finite iid Chebyshev bound for the actual centered sum. -/
theorem iid_centered_sum_deviation {n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    (score : A → ℝ) {d : ℝ} (hd : 0 < d) :
    eventMass (pilotLaw p) (fun x : Fin n → A =>
      d ≤ |(∑ i, score (x i)) - (n : ℝ) * ∑ a, p a * score a|) ≤
      ((n : ℝ) * ∑ a, p a * (score a)^2) / d^2 := by
  let m := ∑ a, p a * score a
  let g (a : A) := score a - m
  have hm : ∑ a, p a * m = m := by rw [← Finset.sum_mul, hp.total, one_mul]
  have zeroMean : ∑ a, p a * g a = 0 := by
    simp only [g, mul_sub, Finset.sum_sub_distrib, hm, m, sub_self]
  have same (x : Fin n → A) :
      (∑ i, g (x i)) = (∑ i, score (x i)) - (n : ℝ) * m := by
    simp [g, Finset.sum_sub_distrib, nsmul_eq_mul]
  have moment : (∑ a, p a * (g a)^2) = (∑ a, p a * (score a)^2) - m^2 := by
    have pointwise (a : A) :
        p a * (g a)^2 = p a * (score a)^2 - 2 * m * (p a * score a) + p a * m^2 := by
      simp only [g]
      ring
    simp only [pointwise, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.sum_mul, hp.total, one_mul]
    change _ - 2 * m * m + m^2 = _ - m^2
    ring
  calc
    _ = eventMass (pilotLaw p) (fun x : Fin n → A => d ≤ |∑ i, g (x i)|) := by
      simp only [same, m]
    _ ≤ (∑ x : Fin n → A, pilotLaw p x * (∑ i, g (x i))^2) / d^2 :=
      finite_squared_deviation_bound (pilotLaw_isLaw hp).nonneg _ hd
    _ = ((n : ℝ) * ∑ a, p a * (g a)^2) / d^2 := by
      rw [centered_sum_second_moment hp g zeroMean]
    _ ≤ _ := by
      rw [moment]
      gcongr
      linarith [sq_nonneg m]

def tailValue (T : Finset A) (q : A → ℝ) (a : A) : ℝ :=
  if a ∈ T then Real.sqrt (q a) else 0

/-- The empirical weighted-score gate on full iid samples. Values outside
the tail are zero, so the count of tail draws requires no conditioning. -/
theorem weighted_tail_deviation {n : ℕ} {p q : A → ℝ} (hp : IsLaw p)
    (T : Finset A) {b d : ℝ} (hmax : ∀ a ∈ T, q a ≤ b) (hd : 0 < d) :
    eventMass (pilotLaw p) (fun x : Fin n → A =>
      d ≤ |(∑ i, tailValue T q (x i)) - (n : ℝ) * tailScore T p q|) ≤
      ((n : ℝ) * (Real.sqrt b * tailScore T p q)) / d^2 := by
  have mean_eq : (∑ a, p a * tailValue T q a) = tailScore T p q := by
    simp [tailValue, tailScore, mul_ite]
  have second_eq : (∑ a, p a * (tailValue T q a)^2) =
      ∑ a ∈ T, p a * (Real.sqrt (q a))^2 := by
    simp [tailValue, ite_pow, mul_ite]
  have h := iid_centered_sum_deviation (n := n) hp (tailValue T q) hd
  rw [mean_eq, second_eq] at h
  refine h.trans ?_
  gcongr
  exact tail_score_second_moment T p q (fun a _ => hp.nonneg a) hmax

end
end CanonneQuantile
