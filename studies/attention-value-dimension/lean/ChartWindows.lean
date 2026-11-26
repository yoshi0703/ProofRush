import RationalWindows
import Mathlib.Data.Nat.Choose.Bounds

namespace AttentionWindows
noncomputable section

/-- Every polynomially parameterized family, including all zero-leading
parameters, misses a set of simultaneous sign changes on the rational grid. -/
theorem chart_windows {m T : ℕ} (small : m < T)
    (coefficient : ℕ → MvPolynomial (Fin m) ℝ) :
    ∃ l u : Fin T → ℚ,
      (∀ i, 0 < l i ∧ l i < u i ∧ u i < 1) ∧
      (∀ i j, i < j → u i < l j) ∧
      ∀ (x : Fin m → ℝ) (p : Polynomial ℝ), p.natDegree ≤ T →
        (∀ j, MvPolynomial.eval x (coefficient j) = p.coeff j) →
        ¬ (∀ i, p.eval (l i : ℝ) * p.eval (u i : ℝ) < 0) := by
  let num : Unit → Fin T → MvPolynomial (Fin m) ℝ := fun _ i => coefficient (T-(i.val+1))
  let den : Unit → MvPolynomial (Fin m) ℝ := fun _ => coefficient T
  obtain ⟨f, nonzero, vanish⟩ := AttentionDimension.exists_relation_finite_charts
    (fun _ : Unit => m) (fun _ => small) num den
  obtain ⟨l,u,inside,sep,exclude⟩ := rational_windows nonzero (lt_of_le_of_lt (Nat.zero_le _) small)
  refine ⟨l,u,inside,sep,?_⟩
  intro x p degree coeff jumps
  obtain ⟨good,notZero⟩ := exclude p degree jumps
  have chartGood : MvPolynomial.eval x (den ()) ≠ 0 := by simpa [den,coeff] using good
  apply notZero
  simpa [num,den,coeff,coordinates] using vanish () x chartGood

/-- The near-tight obstruction at logarithmic readout degree, also for
the enlarged chart which keeps the constant coefficient of the denominator. -/
theorem parameter_shortage {H D d : ℕ} (large : 4^D ≤ H) (atLeast : 3 ≤ D)
    (narrow : d+2 ≤ D) :
    (d+1)*(H+1) + (D+d).choose d < H*D := by
  have ratio : 2^((D+d)+1) ≤ 2^(2*D) := Nat.pow_le_pow_right (by decide) (by omega)
  have twoPow : (2:ℕ)^(2*D) = 4^D := by rw [pow_mul]; norm_num
  rw [twoPow, pow_succ] at ratio
  have c := Nat.choose_le_two_pow (D+d) d
  have square := Nat.two_mul_sq_add_one_le_two_pow_two_mul D
  rw [twoPow] at square
  have below : 2*(d+1) < H := by nlinarith [Nat.mul_le_mul_left D (show 1 ≤ D by omega)]
  have scaled := Nat.mul_le_mul_right H narrow
  nlinarith

end
end AttentionWindows
