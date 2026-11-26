import ChartWindows
import GridSigns

namespace AttentionWindows
noncomputable section
open AttentionGrid

/-- The target is a polynomial threshold on actual binary vectors. Its
evaluation depends only on the Hamming weight, and is nonzero on every input. -/
theorem boolean_obstruction {m T : ℕ} (small : m < T)
    (coefficient : ℕ → MvPolynomial (Fin m) ℝ) :
    ∃ n : ℕ, 0 < n ∧ ∃ (target : Polynomial ℝ) (b : MvPolynomial (Fin n) ℝ),
      target.natDegree = T ∧ b.totalDegree ≤ T ∧
      (∀ bits : Fin n → Bool, MvPolynomial.eval (booleanReals bits) b =
        target.eval (grid n (hammingWeight bits))) ∧
      (∀ k : Fin (n+1), target.eval (grid n k) ≠ 0) ∧
      ∀ (x : Fin m → ℝ) (p : Polynomial ℝ), p.natDegree ≤ T →
        (∀ j, MvPolynomial.eval x (coefficient j) = p.coeff j) →
        ¬ agreesOnGrid n target p := by
  obtain ⟨l,u,inside,sep,bad⟩ := chart_windows small coefficient
  obtain ⟨n,hn,L,R,locations,target,b,_,degree,boolean,vals,strict,changes⟩ :=
    exists_boolean_grid_with_sign_changes l u (fun i => (inside i).1)
      (fun i => (inside i).2.1) (fun i => (inside i).2.2) sep
  refine ⟨n,hn,target,b,degree,boolean,vals,strict,?_⟩
  intro x p bound coeff agrees
  apply bad x p bound coeff
  intro i
  rw [← (locations i).1, ← (locations i).2]
  exact opposite_of_agreesOnGrid (L i) (R i) (changes i) agrees

/-- Grid values lie in the interval where all softmax denominators are positive. -/
theorem grid_bounds {n : ℕ} (hn : 0 < n) (k : Fin (n+1)) :
    0 ≤ grid n k ∧ grid n k ≤ 1 := by
  have den : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨div_nonneg (by positivity) den.le, (div_le_one den).2 ?_⟩
  exact_mod_cast (show k.val ≤ n by omega)

end
end AttentionWindows
