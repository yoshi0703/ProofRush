import MarkerTilt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Sigma

namespace CanonneRefinement

open CanonneMarker
open scoped BigOperators
noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]

def pushed (q : A → ℝ) (K : A → B → ℝ) (b : B) : ℝ := ∑ a, q a*K a b

def pull {n : ℕ} (K : A → B → ℝ) (test : (Fin n → B) → ℝ) (x : Fin n → A) : ℝ :=
  ∑ z : Fin n → B, (∏ i, K (x i) (z i))*test z

omit [Fintype A] in
theorem pull_unit {n : ℕ} {K : A → B → ℝ} (hK : ∀ a b, 0 ≤ K a b)
    (hrow : ∀ a, ∑ b, K a b = 1) {test : (Fin n → B) → ℝ} (h : ∀ z, 0 ≤ test z ∧ test z ≤ 1)
    (x : Fin n → A) : 0 ≤ pull K test x ∧ pull K test x ≤ 1 := by
  classical
  constructor
  · exact Finset.sum_nonneg fun z _ => mul_nonneg (Finset.prod_nonneg fun i _ => hK _ _) (h z).1
  · calc
      _ ≤ ∑ z : Fin n → B, ∏ i, K (x i) (z i) := Finset.sum_le_sum fun z _ =>
        mul_le_of_le_one_right (Finset.prod_nonneg fun i _ => hK _ _) (h z).2
      _ = ∏ i, ∑ b, K (x i) b := (Fintype.prod_sum (fun i b => K (x i) b)).symm
      _ = 1 := by simp [hrow]

theorem pull_rejection {n : ℕ} (q : A → ℝ) (K : A → B → ℝ) (test : (Fin n → B) → ℝ) :
    (∑ x : Fin n → A, recordLaw q x * pull K test x) =
    ∑ z : Fin n → B, recordLaw (pushed q K) z * test z := by
  classical
  have hmass (z : Fin n → B) :
      (∑ x : Fin n → A, recordLaw q x * ∏ i, K (x i) (z i)) = recordLaw (pushed q K) z := by
    simp only [recordLaw,pushed,← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i a => q a*K a (z i))).symm
  unfold pull
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [← mul_assoc, ← Finset.sum_mul, hmass]

variable [DecidableEq A]

abbrev Labels (m : A → ℕ) := Σ a, Fin (m a)

def clone (m : A → ℕ) (q : A → ℝ) (s : Labels m) : ℝ := q s.1 / (m s.1 : ℝ)

def splitKernel (m : A → ℕ) (a : A) (s : Labels m) : ℝ :=
  if s.1 = a then 1/(m s.1 : ℝ) else 0

theorem split_stochastic (m : A → ℕ) (hm : ∀ a, 0 < m a) :
    (∀ a s, 0 ≤ splitKernel m a s) ∧ ∀ a, ∑ s, splitKernel m a s = 1 := by
  classical
  constructor
  · intro a s
    unfold splitKernel
    split <;> positivity
  · intro a
    rw [Fintype.sum_sigma]
    simp only [splitKernel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hterm (b : A) : (m b : ℝ)*(if b=a then 1/(m b : ℝ) else 0) = if b=a then 1 else 0 := by
      by_cases heq : b = a <;> simp [heq, Nat.ne_of_gt (hm a)]
    simp only [hterm]
    simp

theorem split_push (m : A → ℕ) (q : A → ℝ) : pushed q (splitKernel m) = clone m q := by
  classical
  funext s
  unfold pushed splitKernel clone
  simp only [mul_ite, mul_zero]
  simp [div_eq_mul_inv]

omit [DecidableEq A] in
theorem clone_moment (m : A → ℕ) (hm : ∀ a, 0 < m a) (q : A → ℝ) (f : ℝ → ℝ) :
    (∑ s, clone m q s*f (clone m q s)) = ∑ a, q a*f (q a/(m a : ℝ)) := by
  rw [Fintype.sum_sigma]
  simp only [clone,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast (hm a).ne')]

omit [DecidableEq A] in
theorem clone_overlap (m : A → ℕ) (hm : ∀ a, 0 < m a) (q p : A → ℝ) :
    (∑ s, min (clone m p s) (clone m q s)) = ∑ a, min (p a) (q a) := by
  rw [Fintype.sum_sigma]
  simp only [clone,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (0 : ℝ) < m a := by exact_mod_cast hm a
  rcases le_total (p a) (q a) with h | h
  · rw [min_eq_left h, min_eq_left (div_le_div_of_nonneg_right h hp.le), mul_div_cancel₀ _ hp.ne']
  · rw [min_eq_right h, min_eq_right (div_le_div_of_nonneg_right h hp.le), mul_div_cancel₀ _ hp.ne']

def multiplicity (cap x : ℝ) : ℕ := max 1 ⌈x/cap⌉₊

theorem multiplicity_pos (cap x : ℝ) : 0 < multiplicity cap x :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem clone_atom_le {cap x : ℝ} (hc : 0 < cap) : x/(multiplicity cap x : ℝ) ≤ cap := by
  have hk : 0 < (multiplicity cap x : ℝ) := by exact_mod_cast multiplicity_pos cap x
  have hceil : (⌈x/cap⌉₊ : ℝ) ≤ multiplicity cap x := by exact_mod_cast le_max_right 1 ⌈x/cap⌉₊
  have hx := (div_le_iff₀ hc).mp ((Nat.le_ceil _).trans hceil)
  exact (div_le_iff₀ hk).mpr (by linarith)

theorem sqrt_atom_clipped {cap x : ℝ} (hc : 0 < cap) (hx : 0 ≤ x) :
    Real.sqrt (x/(multiplicity cap x : ℝ)) ≤ min (Real.sqrt x) (Real.sqrt cap) ∧
    min (Real.sqrt x) (Real.sqrt cap) ≤ Real.sqrt 2*Real.sqrt (x/(multiplicity cap x : ℝ)) := by
  have h1 : (1 : ℝ) ≤ multiplicity cap x := by exact_mod_cast le_max_left 1 ⌈x/cap⌉₊
  have hk : (0 : ℝ) < multiplicity cap x := by linarith
  constructor
  · exact le_min (Real.sqrt_le_sqrt (div_le_self hx h1)) (Real.sqrt_le_sqrt (clone_atom_le hc))
  · rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    by_cases h : x ≤ cap
    · have hceil : ⌈x/cap⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using (div_le_one hc).mpr h)
      have h1' : multiplicity cap x = 1 := max_eq_left hceil
      rw [h1',Nat.cast_one,div_one,min_eq_left (Real.sqrt_le_sqrt h)]
      exact Real.sqrt_le_sqrt (by linarith)
    · have hlt : cap < x := lt_of_not_ge h
      have hc1 : 1 ≤ x/cap := (one_le_div hc).mpr hlt.le
      have hceil := (Nat.ceil_lt_add_one (div_nonneg hx hc.le)).le
      have hp : (multiplicity cap x : ℝ) ≤ 2*(x/cap) := by
        unfold multiplicity
        rw [Nat.cast_max]
        exact max_le (by norm_cast; linarith) (by linarith)
      have h2 : cap ≤ 2*(x/(multiplicity cap x : ℝ)) := by
        have h3 := mul_le_mul_of_nonneg_left hp hc.le
        have heq : cap*(2*(x/cap))=2*x := by field_simp
        rw [heq] at h3
        rw [mul_div_assoc', le_div_iff₀ hk]
        exact h3
      rw [min_eq_right (Real.sqrt_le_sqrt hlt.le)]
      exact Real.sqrt_le_sqrt h2

def height {C : Type*} [Fintype C] (q : C → ℝ) : ℝ := ∑ a, q a*Real.sqrt (q a)

def clippedMoment (q : A → ℝ) (cap : ℝ) : ℝ := ∑ a, q a*min (Real.sqrt (q a)) (Real.sqrt cap)

def nearMoment (q : A → ℝ) (δ : ℝ) : ℝ := ∑ a, q a * min 1 (Real.sqrt (q a/δ))

omit [DecidableEq A] in
theorem actual_split_height (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) {cap : ℝ} (hc : 0 < cap) :
    let m := fun a => multiplicity cap (q a)
    height (clone m q) ≤ clippedMoment q cap ∧
    clippedMoment q cap ≤ Real.sqrt 2 * height (clone m q) := by
  dsimp only
  unfold height clippedMoment
  rw [clone_moment _ (fun a => multiplicity_pos cap (q a)) q Real.sqrt, Finset.mul_sum]
  constructor
  · exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (sqrt_atom_clipped hc (hq a)).1 (hq a)
  · apply Finset.sum_le_sum
    intro a _
    calc
      _ ≤ q a*(Real.sqrt 2*Real.sqrt (q a / (multiplicity cap (q a) : ℝ))) :=
        mul_le_mul_of_nonneg_left (sqrt_atom_clipped hc (hq a)).2 (hq a)
      _ = _ := by ring

omit [DecidableEq A] in
theorem scaled_near_moment (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) {δ : ℝ} (hδ : 0 < δ) :
    Real.sqrt δ * nearMoment q δ = clippedMoment q δ := by
  unfold nearMoment clippedMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.sqrt_div (hq a)]
  have h := Real.sqrt_pos.mpr hδ
  by_cases hcmp : Real.sqrt (q a) ≤ Real.sqrt δ
  · rw [min_eq_left hcmp, min_eq_right ((div_le_one h).mpr hcmp)]
    field_simp
  · rw [min_eq_right (le_of_not_ge hcmp), min_eq_left ((one_le_div h).mpr (le_of_not_ge hcmp))]
    ring

omit [DecidableEq A] in
theorem actual_near_one_height (q : A → ℝ) (hq : ∀ a, 0 ≤ q a) {δ : ℝ} (hδ : 0 < δ)
    (hthreshold : 16*δ ≤ nearMoment q δ) :
    let m := fun a => multiplicity δ (q a)
    8*δ*Real.sqrt δ ≤ height (clone m q) := by
  let m := fun a => multiplicity δ (q a)
  have hpos : 0 ≤ height (clone m q) := Finset.sum_nonneg fun a _ =>
    mul_nonneg (div_nonneg (hq _) (by positivity)) (Real.sqrt_nonneg _)
  have hheight := (actual_split_height q hq hδ).2
  rw [← scaled_near_moment q hq hδ] at hheight
  have h2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_nonneg (Real.sqrt 2-2)]
  have h1 := mul_le_mul_of_nonneg_right h2 hpos
  change Real.sqrt δ*nearMoment q δ ≤ Real.sqrt 2*height (clone m q) at hheight
  change 8*δ*Real.sqrt δ ≤ height (clone m q)
  nlinarith [mul_le_mul_of_nonneg_left hthreshold (Real.sqrt_nonneg δ)]

omit [DecidableEq A] in
theorem clone_totalVariation (m : A → ℕ) (hm : ∀ a, 0 < m a) (q p : A → ℝ) :
    (∑ s, |clone m p s-clone m q s|)/2 = (∑ a, |p a-q a|)/2 := by
  congr 1
  rw [Fintype.sum_sigma]
  simp only [clone,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (0 : ℝ) < m a := by exact_mod_cast hm a
  rw [← sub_div, abs_div, abs_of_pos hp, mul_div_cancel₀ _ hp.ne']

theorem clone_test (m : A → ℕ) (hm : ∀ a, 0 < m a) (q : A → ℝ) {n : ℕ}
    (f : (Fin n → Labels m) → ℝ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    (∀ x, 0 ≤ pull (splitKernel m) f x ∧ pull (splitKernel m) f x ≤ 1) ∧
    (∑ x : Fin n → A, recordLaw q x*pull (splitKernel m) f x) =
      ∑ z : Fin n → Labels m, recordLaw (clone m q) z*f z := by
  obtain ⟨hn,hs⟩ := split_stochastic m hm
  refine ⟨pull_unit hn hs hf, ?_⟩
  rw [pull_rejection, split_push]

end
end CanonneRefinement
