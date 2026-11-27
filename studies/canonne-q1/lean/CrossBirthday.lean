import MeanGate
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

private def crossLeft {l : ℕ} (i : Fin l) : Fin (l + l) := Fin.castAdd l i
private def crossRight {l : ℕ} (i : Fin l) : Fin (l + l) := Fin.natAdd l i

private theorem left_injective (l : ℕ) : Function.Injective (@crossLeft l) := by
  intro i j h
  have hh := congrArg (fun q : Fin (l+l) => q.val) h
  exact Fin.ext hh

private theorem right_injective (l : ℕ) : Function.Injective (@crossRight l) := by
  intro i j h
  have hval := congrArg Fin.val h
  apply Fin.ext
  change l + i.val = l + j.val at hval
  omega

private theorem opposite_ne {l : ℕ} (i j : Fin l) : crossLeft i ≠ crossRight j := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = l + j.val at hh
  omega

def tailCubeMass (T : Finset A) (p : A → ℝ) : ℝ := ∑ a ∈ T, (p a)^3

def crossEvent {l : ℕ} (T : Finset A) (i j : Fin l) (x : Fin (l + l) → A) : Prop :=
  x (crossLeft i) = x (crossRight j) ∧ x (crossLeft i) ∈ T

instance {l : ℕ} (T : Finset A) (i j : Fin l) (x : Fin (l + l) → A) :
    Decidable (crossEvent T i j x) := by unfold crossEvent; infer_instance

def crossIndicator {l : ℕ} (T : Finset A) (i j : Fin l) (x : Fin (l+l) → A) : ℝ :=
  if crossEvent T i j x then 1 else 0

def crossCount {l : ℕ} (T : Finset A) (x : Fin (l+l) → A) : ℝ :=
  ∑ i : Fin l, ∑ j : Fin l, crossIndicator T i j x

theorem cross_event_mass {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) (i j : Fin l) :
    eventMass (pilotLaw p) (crossEvent T i j) = tailSquareMass T p :=
  tail_pair_probability T hp (opposite_ne i j)

private theorem same_label_three {n : ℕ} {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    eventMass (pilotLaw p) (fun x : Fin n → A =>
      x a = x b ∧ x a = x c ∧ x a ∈ T) = tailCubeMass T p := by
  let f : Fin 3 → Fin n := ![a, b, c]
  have hinj : Function.Injective f := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [f]
  have h := tail_repeat_power_probability (m := 3) (by decide) T hp f hinj
  unfold tailCubeMass
  rw [← h]
  apply eventMass_congr
  intro x
  constructor
  · rintro ⟨hx, hy, ht⟩
    refine ⟨x a, ht, ?_⟩
    intro u
    fin_cases u
    · exact rfl
    · exact hx.symm
    · exact hy.symm
  · rintro ⟨d, hd, hx⟩
    have h0 : x a = d := hx 0
    have h1 : x b = d := hx 1
    have h2 : x c = d := hx 2
    exact ⟨h0.trans h1.symm,h0.trans h2.symm,h0.symm ▸ hd⟩

theorem cross_same_left_mass {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    (i : Fin l) {j j' : Fin l} (hj : j ≠ j') :
    eventMass (pilotLaw p) (fun x => crossEvent T i j x ∧ crossEvent T i j' x) =
      tailCubeMass T p := by
  rw [← same_label_three (opposite_ne i j) (opposite_ne i j')
    (fun h => hj (right_injective l h)) T hp]
  apply eventMass_congr
  intro x
  simpa [crossEvent] using (show
    ((x (crossLeft i) = x (crossRight j) ∧ x (crossLeft i) ∈ T) ∧
      x (crossLeft i) = x (crossRight j') ∧ x (crossLeft i) ∈ T) ↔
      x (crossLeft i) = x (crossRight j) ∧ x (crossLeft i) = x (crossRight j') ∧
        x (crossLeft i) ∈ T by tauto)

theorem cross_same_right_mass {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    {i i' : Fin l} (hi : i ≠ i') (j : Fin l) :
    eventMass (pilotLaw p) (fun x => crossEvent T i j x ∧ crossEvent T i' j x) =
      tailCubeMass T p := by
  rw [← same_label_three (opposite_ne i j).symm (opposite_ne i' j).symm
    (fun h => hi (left_injective l h)) T hp]
  apply eventMass_congr
  intro x
  unfold crossEvent
  constructor
  · rintro ⟨⟨h₁, hmem⟩, h₂, _⟩
    exact ⟨h₁.symm, h₂.symm, h₁ ▸ hmem⟩
  · rintro ⟨h₁, h₂, hmem⟩
    exact ⟨⟨h₁.symm, h₁ ▸ hmem⟩, h₂.symm, h₂ ▸ hmem⟩

theorem cross_disjoint_mass {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    {i i' j j' : Fin l} (hi : i ≠ i') (hj : j ≠ j') :
    eventMass (pilotLaw p) (fun x => crossEvent T i j x ∧ crossEvent T i' j' x) =
      (tailSquareMass T p)^2 := by
  let f : Fin 2 ⊕ Fin 2 → Fin (l + l) :=
    Sum.elim ![crossLeft i, crossRight j] ![crossLeft i', crossRight j']
  have hleft : crossLeft i ≠ crossLeft i' := fun h => hi (left_injective l h)
  have hright : crossRight j ≠ crossRight j' := fun h => hj (right_injective l h)
  have hinj : Function.Injective f := by
    intro u v huv
    rcases u with u | u <;> rcases v with v | v <;>
      fin_cases u <;> fin_cases v <;>
      simp_all [f, opposite_ne, fun x y => (opposite_ne x y).symm]
  rw [← disjoint_tail_pair_probability T hp f hinj]
  apply eventMass_congr
  intro x
  constructor
  · rintro ⟨⟨h₁, hmem⟩, h₂, hmem'⟩
    refine ⟨(x (crossLeft i), x (crossLeft i')), Finset.mem_product.mpr ⟨hmem,hmem'⟩, ?_⟩
    intro u
    rcases u with u | u <;> fin_cases u <;> simp [f, h₁, h₂]
  · rintro ⟨d, hd, hx⟩
    have h0 : x (crossLeft i) = d.1 := hx (Sum.inl 0)
    have h1 : x (crossRight j) = d.1 := hx (Sum.inl 1)
    have h2 : x (crossLeft i') = d.2 := hx (Sum.inr 0)
    have h3 : x (crossRight j') = d.2 := hx (Sum.inr 1)
    have hmem := Finset.mem_product.mp hd
    exact ⟨⟨h0.trans h1.symm,h0.symm ▸ hmem.1⟩, h2.trans h3.symm,h2.symm ▸ hmem.2⟩

private def expectation {n : ℕ} (p : A → ℝ) (f : (Fin n → A) → ℝ) : ℝ :=
  ∑ x, pilotLaw p x * f x

omit [DecidableEq A] in
private theorem expectation_sum {n : ℕ} {I : Type*} [Fintype I]
    (p : A → ℝ) (f : I → (Fin n → A) → ℝ) :
    expectation p (fun x => ∑ i, f i x) = ∑ i, expectation p (f i) := by
  unfold expectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq A] in
private theorem indicator_expectation {n : ℕ} {p : A → ℝ} (E : (Fin n → A) → Prop)
    [DecidablePred E] :
    expectation p (fun x => if E x then 1 else 0) = eventMass (pilotLaw p) E := by
  rw [expectation, eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x <;> simp [h]

theorem cross_count_mean {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    (∑ x : Fin (l+l) → A, pilotLaw p x * crossCount T x) =
      (l : ℝ)^2 * tailSquareMass T p := by
  change expectation p (crossCount T) = _
  unfold crossCount
  rw [expectation_sum]
  simp only [expectation_sum, crossIndicator, indicator_expectation, cross_event_mass T hp,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem cross_pair_product {l : ℕ} (T : Finset A) (p : A → ℝ) (i j i' j' : Fin l) :
    expectation p (fun x => crossIndicator T i j x * crossIndicator T i' j' x) =
      eventMass (pilotLaw p) (fun x => crossEvent T i j x ∧ crossEvent T i' j' x) := by
  classical
  unfold crossIndicator expectation
  rw [eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : crossEvent T i j x <;> by_cases h' : crossEvent T i' j' x <;> simp [h, h']

private theorem cross_pair_upper {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    (i j i' j' : Fin l) :
    expectation p (fun x => crossIndicator T i j x * crossIndicator T i' j' x) ≤
      (tailSquareMass T p)^2
        + (if i' = i then if j' = j then tailSquareMass T p else 0 else 0)
        + (if i' = i then tailCubeMass T p else 0)
        + (if j' = j then tailCubeMass T p else 0) := by
  have hc : 0 ≤ tailCubeMass T p := Finset.sum_nonneg fun a _ => pow_nonneg (hp.nonneg a) _
  rw [cross_pair_product]
  by_cases hi : i' = i <;> by_cases hj : j' = j
  · subst i'
    subst j'
    simp only [and_self, ite_true, cross_event_mass T hp]
    linarith [sq_nonneg (tailSquareMass T p)]
  · subst i'
    simp only [ite_true, hj, ite_false, add_zero, cross_same_left_mass T hp i (Ne.symm hj)]
    linarith [sq_nonneg (tailSquareMass T p)]
  · subst j'
    simp only [hi, ite_false, add_zero, ite_true, cross_same_right_mass T hp (Ne.symm hi) j]
    linarith [sq_nonneg (tailSquareMass T p)]
  · simp [hi, hj, cross_disjoint_mass T hp (Ne.symm hi) (Ne.symm hj)]

theorem cross_count_raw_second {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    (∑ x : Fin (l+l) → A, pilotLaw p x * (crossCount T x)^2) ≤
      (l : ℝ)^4 * (tailSquareMass T p)^2 +
        (l : ℝ)^2 * tailSquareMass T p + 2 * (l : ℝ)^3 * tailCubeMass T p := by
  have expand (x : Fin (l+l) → A) :
      (crossCount T x)^2 =
        ∑ i : Fin l, ∑ j : Fin l, ∑ i' : Fin l, ∑ j' : Fin l,
          crossIndicator T i j x * crossIndicator T i' j' x := by
    unfold crossCount
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.mul_sum]
  change expectation p (fun x => (crossCount T x)^2) ≤ _
  simp only [expand, expectation_sum]
  calc
    _ ≤ ∑ i : Fin l, ∑ j : Fin l, ∑ i' : Fin l, ∑ j' : Fin l,
       ((tailSquareMass T p)^2 +
         (if i' = i then if j' = j then tailSquareMass T p else 0 else 0) +
         (if i' = i then tailCubeMass T p else 0) +
         (if j' = j then tailCubeMass T p else 0)) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro i' _
      apply Finset.sum_le_sum; intro j' _
      exact cross_pair_upper T hp i j i' j'
    _ = _ := by
      simp [Finset.sum_add_distrib, nsmul_eq_mul]
      ring

/-- The actual centered second moment of the bipartite repeat count. -/
theorem cross_count_variance {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    (∑ x : Fin (l+l) → A, pilotLaw p x *
      (crossCount T x - (l : ℝ)^2 * tailSquareMass T p)^2) ≤
        (l : ℝ)^2 * tailSquareMass T p + 2 * (l : ℝ)^3 * tailCubeMass T p := by
  let m := (l : ℝ)^2 * tailSquareMass T p
  have expand (x : Fin (l+l) → A) :
      pilotLaw p x * (crossCount T x - m)^2 =
        pilotLaw p x * (crossCount T x)^2 -
          (2*m) * (pilotLaw p x * crossCount T x) + pilotLaw p x * m^2 := by ring
  change (∑ x : Fin (l+l) → A, pilotLaw p x * (crossCount T x - m)^2) ≤ _
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.sum_mul, (pilotLaw_isLaw hp).total, one_mul, cross_count_mean T hp]
  have raw := cross_count_raw_second (l := l) T hp
  dsimp [m]
  nlinarith

omit [DecidableEq A] in
theorem tail_cube_le_square_sqrt (T : Finset A) {p : A → ℝ} (hp : IsLaw p) :
    tailCubeMass T p ≤ tailSquareMass T p * Real.sqrt (tailSquareMass T p) := by
  unfold tailCubeMass
  rw [tailSquareMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  have hSq : (p a)^2 ≤ ∑ i ∈ T, (p i)^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (p i)) ha
  have hrt := Real.sqrt_le_sqrt hSq
  rw [Real.sqrt_sq (hp.nonneg a)] at hrt
  calc
    _ = (p a)^2 * p a := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrt (sq_nonneg _)

/-- Chebyshev on the actual cross-batch repeat statistic. -/
theorem cross_count_deviation {l : ℕ} (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    {d : ℝ} (hd : 0 < d) :
    eventMass (pilotLaw p) (fun x : Fin (l+l) → A =>
      d ≤ |crossCount T x - (l : ℝ)^2 * tailSquareMass T p|) ≤
      ((l : ℝ)^2 * tailSquareMass T p
       + 2 * (l : ℝ)^3 * tailSquareMass T p * Real.sqrt (tailSquareMass T p)) / d^2 := by
  refine (finite_squared_deviation_bound (pilotLaw_isLaw hp).nonneg _ hd).trans ?_
  apply div_le_div_of_nonneg_right _ (sq_nonneg d)
  refine (cross_count_variance T hp).trans ?_
  rw [mul_assoc (2 * (l : ℝ)^3)]
  gcongr
  exact tail_cube_le_square_sqrt T hp

omit [DecidableEq A] in
theorem finite_eventMass_mono {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) {E F : A → Prop}
    (imp : ∀ a, E a → F a) : eventMass p E ≤ eventMass p F := by
  classical
  rw [eventMass_eq_sum, eventMass_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases he : E a
  · simp [he, imp a he]
  · by_cases hf : F a
    · simp [he, hf, hp a]
    · simp [he, hf]

private theorem square_rate (L r : ℝ) (hr : 0 ≤ r) :
    L^2 * r = (L * Real.sqrt r)^2 := by
  rw [mul_pow, Real.sq_sqrt hr]

private theorem cube_rate (L r : ℝ) (hr : 0 ≤ r) :
    L^3 * r * Real.sqrt r = (L * Real.sqrt r)^3 := by
  rw [mul_pow, pow_succ (Real.sqrt r) 2, Real.sq_sqrt hr]
  ring

private theorem cross_null_numeric {L r B : ℝ} (hL : 0 < L) (hr : 0 < r)
    (_hB : 0 ≤ B) (hhigh : B ≤ r/8) (hscale : 8192 ≤ L*Real.sqrt r) :
    (L^2*B+2*L^3*B*Real.sqrt B)/(L^2*r/16)^2 ≤ 1/100 := by
  have hsqrt : Real.sqrt B ≤ Real.sqrt r :=
    Real.sqrt_le_sqrt (hhigh.trans (by linarith))
  have htop : L^2*B+2*L^3*B*Real.sqrt B ≤ L^2*(r/8)+2*L^3*(r/8)*Real.sqrt r := by
    gcongr
  let t := L*Real.sqrt r
  have ht : 8192 ≤ t := hscale
  have he₂ : L^2 * r = t^2 := square_rate L r hr.le
  have he₃ : L^3 * r * Real.sqrt r = t^3 := cube_rate L r hr.le
  have hetop : L^2*(r/8)+2*L^3*(r/8)*Real.sqrt r = t^2/8+t^3/4 := by
    calc
      _ = (L^2 * r)/8 + (L^3*r*Real.sqrt r)/4 := by ring
      _ = _ := by rw [he₂, he₃]
  rw [hetop] at htop
  rw [he₂]
  refine (div_le_div_of_nonneg_right htop (sq_nonneg _)).trans ?_
  rw [div_le_iff₀ (show 0 < (t^2/16)^2 by positivity)]
  have main : 3200+6400*t ≤ t^2 := by
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr ht)]
  nlinarith [mul_le_mul_of_nonneg_right main (sq_nonneg t)]

private theorem cross_alt_numeric {L r B : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hhigh : r/4 ≤ B) (hscale : 8192 ≤ L*Real.sqrt r) :
    (L^2*B+2*L^3*B*Real.sqrt B)/(L^2*B/4)^2 ≤ 1/100 := by
  have hpos : 0 < B := by linarith
  have hsqrt : Real.sqrt r/2 ≤ Real.sqrt B := by
    have hs := Real.sqrt_le_sqrt (show r ≤ 4*B by linarith)
    have four : Real.sqrt (4 : ℝ) = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg (4 : ℝ)]
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num), four] at hs
    linarith
  let t := L*Real.sqrt B
  have ht : 4096 ≤ t := by
    have h := mul_le_mul_of_nonneg_left hsqrt hL.le
    dsimp [t]
    linarith
  have he₂ : L^2 * B = t^2 := square_rate L B hpos.le
  have he₃ : L^3 * B * Real.sqrt B = t^3 := cube_rate L B hpos.le
  have hetop : L^2*B+2*L^3*B*Real.sqrt B = t^2+2*t^3 := by
    calc
      _ = L^2*B + 2*(L^3*B*Real.sqrt B) := by ring
      _ = _ := by rw [he₂, he₃]
  rw [hetop, he₂, div_le_iff₀ (show 0 < (t^2/4)^2 by positivity)]
  have main : 1600+3200*t ≤ t^2 := by
    nlinarith [mul_nonneg (show 0 ≤ t by linarith) (sub_nonneg.mpr ht)]
  nlinarith [mul_le_mul_of_nonneg_right main (sq_nonneg t)]

/-- Actual null error for the cross-batch collision proportion threshold
3r/16, assuming a reference squared tail mass at most r/8. -/
theorem cross_gate_null {l : ℕ} (hl : 0 < l) (T : Finset A) {p : A → ℝ} (hp : IsLaw p)
    {r : ℝ} (hr : 0 < r) (hb : tailSquareMass T p ≤ r/8)
    (hscale : 8192 ≤ (l : ℝ)*Real.sqrt r) :
    eventMass (pilotLaw p) (fun x : Fin (l+l) → A =>
      3*r*(l : ℝ)^2/16 < crossCount T x) ≤ 1/100 := by
  have hL : 0 < (l : ℝ) := by exact_mod_cast hl
  have hD : 0 < (l : ℝ)^2*r/16 := by positivity
  have hmass : 0 ≤ tailSquareMass T p := Finset.sum_nonneg fun a _ => sq_nonneg (p a)
  refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg ?_).trans
    ((cross_count_deviation (l := l) T hp hD).trans (cross_null_numeric hL hr hmass hb hscale))
  intro x hx
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (l : ℝ))
  refine le_trans (b := crossCount T x - (l : ℝ)^2*tailSquareMass T p) ?_ (le_abs_self _)
  nlinarith

/-- Actual miss probability for the same cross-batch collision test under
an alternative with squared tail mass at least r/4. -/
theorem cross_gate_alternative {l : ℕ} (hl : 0 < l) (T : Finset A)
    {p : A → ℝ} (hp : IsLaw p)
    {r : ℝ} (hr : 0 < r) (hb : r/4 ≤ tailSquareMass T p)
    (hscale : 8192 ≤ (l : ℝ)*Real.sqrt r) :
    eventMass (pilotLaw p) (fun x : Fin (l+l) → A =>
      crossCount T x ≤ 3*r*(l : ℝ)^2/16) ≤ 1/100 := by
  have hL : 0 < (l : ℝ) := by exact_mod_cast hl
  have hmass : 0 < tailSquareMass T p := by linarith
  have hD : 0 < (l : ℝ)^2*tailSquareMass T p/4 := by positivity
  refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg ?_).trans
    ((cross_count_deviation (l := l) T hp hD).trans (cross_alt_numeric hL hr hb hscale))
  intro x hx
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (l : ℝ))
  refine le_trans (b := -(crossCount T x - (l : ℝ)^2*tailSquareMass T p)) ?_ (neg_le_abs _)
  nlinarith

end
end CanonneQuantile
