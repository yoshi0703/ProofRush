import RootWindows
import Mathlib.Tactic.Positivity

namespace AttentionWindows
noncomputable section

variable {T : ℕ}

private def baseL (i : Fin T) : ℝ := (2*(i.val : ℝ)+1)/(2*(T : ℝ)+2)
private def baseU (i : Fin T) : ℝ := (2*(i.val : ℝ)+2)/(2*(T : ℝ)+2)

private theorem base_bounds (i : Fin T) :
    0 < baseL i ∧ baseL i < baseU i ∧ baseU i < 1 := by
  unfold baseL baseU
  have den : 0 < 2*(T:ℝ)+2 := by positivity
  have below : (i.val:ℝ) < (T:ℝ) := by exact_mod_cast i.isLt
  exact ⟨by positivity, (div_lt_div_iff_of_pos_right den).2 (by linarith),
    (div_lt_one den).2 (by linarith)⟩

private theorem base_sep {i j : Fin T} (h : i < j) : baseU i < baseL j := by
  unfold baseU baseL
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < 2*(T:ℝ)+2)).2
  have step : i.val+1 ≤ j.val := h
  have realStep : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by exact_mod_cast step
  linarith

/-- A nonzero polynomial relation on monic coefficients fails throughout
the sign cell of finitely many rational pairs. Coefficients are listed from
degree T-1 down to degree zero, including all T affine chart coordinates. -/
theorem rational_windows {f : MvPolynomial (Fin T) ℝ} (nonzero : f ≠ 0) (pos : 0 < T) :
    ∃ l u : Fin T → ℚ,
      (∀ i, 0 < l i ∧ l i < u i ∧ u i < 1) ∧
      (∀ i j, i < j → u i < l j) ∧
      ∀ (p : Polynomial ℝ), p.natDegree ≤ T →
        (∀ i, p.eval (l i : ℝ) * p.eval (u i : ℝ) < 0) →
        p.coeff T ≠ 0 ∧ MvPolynomial.eval (fun i => coordinates p i / p.coeff T) f ≠ 0 := by
  classical
  let side : Fin T → Set ℝ := fun i => Set.Ioo (-(baseU i)) (-(baseL i))
  have inf : ∀ i, (side i).Infinite := fun i => Set.Ioo_infinite (neg_lt_neg (base_bounds i).2.1)
  obtain ⟨z, hz, good⟩ : ∃ z ∈ Set.pi Set.univ side, MvPolynomial.eval z (pullback f) ≠ 0 := by
    by_contra! bad
    apply pullback_ne nonzero
    apply MvPolynomial.funext_set side inf
    intro x hx
    simpa using bad x hx
  let W : Set (Fin T → ℝ) := {v | MvPolynomial.eval v (pullback f) ≠ 0}
  have op : IsOpen W := isOpen_ne_fun (pullback f).continuous_eval continuous_const
  obtain ⟨ε, he, ball⟩ := Metric.isOpen_iff.mp op z good
  have inner (i : Fin T) : baseL i < -(z i) ∧ -(z i) < baseU i := by
    obtain ⟨a,b⟩ := hz i (Set.mem_univ i)
    exact ⟨by linarith, by linarith⟩
  have left (i : Fin T) : ∃ a : ℚ, max (baseL i) (-(z i)-ε) < (a:ℝ) ∧ (a:ℝ) < -(z i) :=
    exists_rat_btwn (max_lt (inner i).1 (sub_lt_self _ he))
  have right (i : Fin T) : ∃ a : ℚ, -(z i) < (a:ℝ) ∧ (a:ℝ) < min (baseU i) (-(z i)+ε) :=
    exists_rat_btwn (lt_min (inner i).2 (lt_add_of_pos_right _ he))
  choose l ll lr using left
  choose u ul ur using right
  have lefts (i : Fin T) := max_lt_iff.mp (ll i)
  have rights (i : Fin T) := lt_min_iff.mp (ur i)
  have sep (i j : Fin T) (h : i < j) : (u i : ℝ) < (l j : ℝ) :=
    (rights i).1.trans ((base_sep h).trans (lefts j).1)
  refine ⟨l, u, ?_, ?_, ?_⟩
  · intro i
    exact ⟨by exact_mod_cast (base_bounds i).1.trans (lefts i).1,
      by exact_mod_cast (lr i).trans (ul i),
      by exact_mod_cast (rights i).1.trans (base_bounds i).2.2⟩
  · intro i j h
    exact_mod_cast sep i j h
  intro p degree jumps
  choose c mem root using fun i => root_in_interval p ((lr i).trans (ul i)).le (jumps i)
  have cm : StrictMono c := fun i j h => (mem i).2.trans_lt ((sep i j h).trans_le (mem j).1)
  let b : Fin T → ℝ := fun i => -(c i)
  have bij : Function.Injective b := fun _ _ h => cm.injective (neg_inj.mp h)
  have br (i) : p.eval (-(b i)) = 0 := by simpa [b] using root i
  have eq := identifies degree pos b bij br
  have valid : p.coeff T ≠ 0 := by
    intro zero
    have nil : p = 0 := by simpa [zero] using eq
    simpa [nil] using jumps ⟨0,pos⟩
  have near : b ∈ Metric.ball z ε := by
    apply (dist_pi_lt_iff he).2
    intro i
    rw [Real.dist_eq, abs_lt]
    change -ε < -(c i)-z i ∧ -(c i)-z i < ε
    obtain ⟨cl,cu⟩ := mem i
    constructor <;> linarith [(rights i).2,(lefts i).2]
  have coeffs : (fun i : Fin T => coordinates p i / p.coeff T) = coordinates (rootPoly b) := by
    funext i
    have e := congrArg (fun v : Polynomial ℝ => v.coeff (T-(i.val+1))) eq
    change p.coeff (T-(i.val+1)) = _ at e
    rw [Polynomial.coeff_C_mul] at e
    unfold coordinates
    rw [e]
    exact mul_div_cancel_left₀ _ valid
  refine ⟨valid, ?_⟩
  rw [coeffs, ←pullback_eval]
  exact ball near

end
end AttentionWindows
