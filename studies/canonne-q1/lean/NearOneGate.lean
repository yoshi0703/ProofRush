import CrossBirthday
import Mathlib.Algebra.Order.Floor.Ring

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem sample_projection_event {m n : ℕ} {p : A → ℝ} (hp : IsLaw p)
    (f : Fin m → Fin n) (hinj : Function.Injective f) (E : (Fin m → A) → Prop) :
    eventMass (pilotLaw p) (fun x : Fin n → A => E (fun i => x (f i))) =
    eventMass (pilotLaw p) E := by
  classical
  rw [eventMass_eq_sum, eventMass_eq_sum]
  have exp (x : Fin n → A) :
      (if E (fun i => x (f i)) then pilotLaw p x else 0) =
      ∑ y : Fin m → A, if (fun i => x (f i)) = y ∧ E y then pilotLaw p x else 0 := by
    let z : Fin m → A := fun i => x (f i)
    change (if E z then pilotLaw p x else 0) = ∑ y : Fin m → A, if z = y ∧ E y then _ else _
    rw [Finset.sum_eq_single_of_mem z (Finset.mem_univ _)]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
  simp only [exp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : E y
  · simp only [hy, and_true, ite_true]
    rw [← eventMass_eq_sum]
    have shape (x : Fin n → A) : (fun i => x (f i)) = y ↔ ∀ i, x (f i) = y i :=
      ⟨fun h => congrFun h, fun h => funext h⟩
    rw [eventMass_congr _ shape, injective_pilot_draws hp f hinj y]
  · simp [hy]

private theorem near_one_score_error {l : ℕ} (hl : 0 < l) (T : Finset A)
    {p q : A → ℝ} (hp : IsLaw p) {d M : ℝ} (hM : 0 < M)
    (hcap : ∀ a ∈ T, q a ≤ d) (hmean : tailScore T p q ≤ M)
    (hscale : 8192*Real.sqrt d ≤ (l : ℝ)*M) :
    eventMass (pilotLaw p) (fun x : Fin l → A =>
      (l : ℝ)*M/8 ≤ |(∑ i, tailValue T q (x i)) - (l : ℝ)*tailScore T p q|) ≤ 1/100 := by
  have hL : 0 < (l : ℝ) := by exact_mod_cast hl
  have hdev : 0 < (l : ℝ)*M/8 := by positivity
  refine (weighted_tail_deviation hp T hcap hdev).trans ?_
  have hmul := mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg d)
  have hm := mul_le_mul_of_nonneg_left hmul hL.le
  have hx := mul_le_mul_of_nonneg_right hscale (show 0 ≤ (l : ℝ)*M by positivity)
  rw [div_le_iff₀ (sq_pos_of_pos hdev)]
  nlinarith [mul_nonneg (Real.sqrt_nonneg d) (show 0 ≤ (l : ℝ)*M by positivity)]

omit [DecidableEq A] in
private theorem null_split_square (T : Finset A) {q : A → ℝ}
    (hq : IsLaw q) {b d : ℝ} (hd : 0 < d) (hcap : ∀ a ∈ T, q a ≤ b)
    (hwide : 8*d*Real.sqrt b ≤ tailScore T q q) :
    tailSquareMass T q ≤ (tailScore T q q)^2/d/8 := by
  let M := tailScore T q q
  have upper := tail_score_second_moment T q q (fun a _ => hq.nonneg a) hcap
  have exactSq : (∑ a ∈ T, q a * (Real.sqrt (q a))^2) = tailSquareMass T q := by
    unfold tailSquareMass
    exact Finset.sum_congr rfl (fun a _ => by rw [Real.sq_sqrt (hq.nonneg a)]; ring)
  rw [exactSq] at upper
  have hM : 0 ≤ M :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hq.nonneg a) (Real.sqrt_nonneg _)
  have mul := mul_le_mul_of_nonneg_right hwide hM
  rw [div_div, le_div_iff₀ (show 0 < d*8 by positivity)]
  have ub := mul_le_mul_of_nonneg_right upper (show 0 ≤ d*8 by positivity)
  change tailSquareMass T q*(d*8) ≤ M^2
  change tailSquareMass T q*(d*8) ≤ (Real.sqrt b*M)*(d*8) at ub
  change (8*d*Real.sqrt b)*M ≤ M*M at mul
  nlinarith

omit [DecidableEq A] in
private theorem high_score_split_square (T : Finset A) {p q : A → ℝ}
    (hp : IsLaw p) (hq : IsLaw q) {b d : ℝ} (hd : 0 < d)
    (hcap : ∀ a ∈ T, q a ≤ b) (hwide : 8*d*Real.sqrt b ≤ tailScore T q q)
    (hoverlap : tailOverlap T p q ≤ d)
    (hscore : 3*tailScore T q q/4 ≤ tailScore T p q) :
    (tailScore T q q)^2/d/4 ≤ tailSquareMass T p := by
  let M := tailScore T q q
  have hM : 0 ≤ M :=
    Finset.sum_nonneg fun a _ => mul_nonneg (hq.nonneg a) (Real.sqrt_nonneg _)
  have hs := mul_le_mul_of_nonneg_left hoverlap (Real.sqrt_nonneg b)
  have need : M/2 + Real.sqrt b * tailOverlap T p q ≤ tailScore T p q := by
    dsimp [M]
    nlinarith
  have result := excess_score_forces_tail_collision T p q
    (fun a _ => hp.nonneg a) (fun a _ => hq.nonneg a) hcap (div_nonneg hM (by norm_num)) need
  have hSq : 0 ≤ tailSquareMass T p := Finset.sum_nonneg fun a _ => sq_nonneg (p a)
  have hprod := mul_le_mul_of_nonneg_right hoverlap hSq
  rw [div_div, div_le_iff₀ (show 0 < d*4 by positivity)]
  change M^2 ≤ tailSquareMass T p*(d*4)
  nlinarith

private def scoreBatch {l : ℕ} (x : Fin (l+(l+l)) → A) : Fin l → A :=
  fun i => x (Fin.castAdd (l+l) i)

private def repeatBatch {l : ℕ} (x : Fin (l+(l+l)) → A) : Fin (l+l) → A :=
  fun i => x (Fin.natAdd l i)

private theorem score_indices_injective (l : ℕ) :
    Function.Injective (Fin.castAdd (l+l) : Fin l → Fin (l+(l+l))) := by
  intro i j h
  have hval := congrArg (fun i : Fin (l+(l+l)) => i.val) h
  exact Fin.ext hval

private theorem repeat_indices_injective (l : ℕ) :
    Function.Injective (Fin.natAdd l : Fin (l+l) → Fin (l+(l+l))) :=
  Fin.natAdd_injective (l+l) l

/-- Rejection on a literal ordered sample of size 3l, with the mean score
on the first batch and cross-batch collisions on the next two batches. -/
def nearOneReject {l : ℕ} (T : Finset A) (q : A → ℝ) (δ : ℝ) (x : Fin (l+(l+l)) → A) : Prop :=
  let M := tailScore T q q
  (∑ i, tailValue T q (scoreBatch x i)) < 7*(l : ℝ)*M/8 ∨
    3*(M^2/δ)*(l : ℝ)^2/16 < crossCount T (repeatBatch x)

/-- Both errors for the common overlap test on already-refined laws, with
an atom cap b at most the overlap threshold δ. -/
theorem overlap_capped_test {l : ℕ} (hl : 0 < l) (T : Finset A)
    {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) {b δ : ℝ} (hd : 0 < δ) (hb : b ≤ δ)
    (hcap : ∀ a ∈ T, q a ≤ b)
    (hwide : 8*δ*Real.sqrt b ≤ tailScore T q q)
    (hscale : 8192*Real.sqrt δ ≤ (l : ℝ)*tailScore T q q)
    (hoverlap : tailOverlap T p q ≤ δ) :
    eventMass (pilotLaw q) (nearOneReject (l := l) T q δ) ≤ 1/50 ∧
      eventMass (pilotLaw p) (fun x => ¬ nearOneReject (l := l) T q δ x) ≤ 1/100 := by
  classical
  let M := tailScore T q q
  let r := M^2/δ
  have hL : 0 < (l : ℝ) := by exact_mod_cast hl
  have htotal : 0 < (l : ℝ)*M :=
    lt_of_lt_of_le (show 0 < 8192*Real.sqrt δ by positivity) hscale
  have hM : 0 < M := pos_of_mul_pos_right htotal hL.le
  have hr : 0 < r := by positivity
  have hscale_b : 8192*Real.sqrt b ≤ (l : ℝ)*M :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb) (by norm_num)).trans hscale
  have hroot : Real.sqrt r = M/Real.sqrt δ := by
    rw [show r = M^2/δ by rfl, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hM.le]
  have rate : 8192 ≤ (l : ℝ)*Real.sqrt r := by
    rw [hroot, ← mul_div_assoc, le_div_iff₀ (Real.sqrt_pos.2 hd)]
    exact hscale
  let low (x : Fin l → A) := (∑ i, tailValue T q (x i)) < 7*(l : ℝ)*M/8
  let high (x : Fin (l+l) → A) := 3*r*(l : ℝ)^2/16 < crossCount T x
  have loNull : eventMass (pilotLaw q) low ≤ 1/100 := by
    refine (finite_eventMass_mono (pilotLaw_isLaw hq).nonneg ?_).trans
      (near_one_score_error (l := l) hl T hq hM hcap le_rfl hscale_b)
    intro x hx
    change (∑ i, tailValue T q (x i)) < 7*(l : ℝ)*M/8 at hx
    refine le_trans (b := -((∑ i, tailValue T q (x i)) - (l : ℝ)*M)) ?_ (neg_le_abs _)
    linarith
  have hiNull : eventMass (pilotLaw q) high ≤ 1/100 :=
    cross_gate_null hl T hq hr (null_split_square T hq hd hcap hwide) rate
  constructor
  · let f (k : Bool) (x : Fin (l+(l+l)) → A) :=
      if k then high (repeatBatch x) else low (scoreBatch x)
    have equ : eventMass (pilotLaw q) (nearOneReject (l := l) T q δ) =
        eventMass (pilotLaw q) (fun x => ∃ k ∈ (Finset.univ : Finset Bool), f k x) := by
      apply eventMass_congr
      intro x
      simp [nearOneReject, f, Bool.exists_bool, low, high, M, r]
    rw [equ]
    refine (eventMass_union_le _ (pilotLaw_isLaw hq).nonneg Finset.univ f).trans ?_
    rw [Fintype.sum_bool]
    have lo := sample_projection_event hq _ (score_indices_injective l) low
    have hi := sample_projection_event hq _ (repeat_indices_injective l) high
    change eventMass (pilotLaw q) (fun x => low (scoreBatch x)) = _ at lo
    change eventMass (pilotLaw q) (fun x => high (repeatBatch x)) = _ at hi
    simp only [f, Bool.false_eq_true, ite_false, ite_true, lo, hi]
    linarith
  · by_cases hlow : tailScore T p q ≤ 3*M/4
    · have meanMiss : eventMass (pilotLaw p) (fun x => ¬ low x) ≤ 1/100 := by
        have hsM : tailScore T p q ≤ M := by linarith
        refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg ?_).trans
          (near_one_score_error (l := l) hl T hp hM hcap hsM hscale_b)
        intro x hx
        have hx' : 7*(l : ℝ)*M/8 ≤ ∑ i, tailValue T q (x i) := le_of_not_gt hx
        have hsmall := mul_le_mul_of_nonneg_left hlow hL.le
        refine le_trans (b := (∑ i, tailValue T q (x i)) - (l : ℝ)*tailScore T p q)
          ?_ (le_abs_self _)
        linarith
      refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg
        (E := fun x => ¬ nearOneReject (l := l) T q δ x)
        (F := fun x => ¬ low (scoreBatch x)) ?_).trans ?_
      · intro x hx
        exact (not_or.mp hx).1
      · have hproj := sample_projection_event hp _ (score_indices_injective l) (fun x => ¬ low x)
        change eventMass (pilotLaw p) (fun x => ¬ low (scoreBatch x)) = _ at hproj
        rw [hproj]
        exact meanMiss
    · have repeatMiss : eventMass (pilotLaw p) (fun x => ¬ high x) ≤ 1/100 := by
        have bound := high_score_split_square T hp hq hd hcap hwide hoverlap (le_of_not_ge hlow)
        have h := cross_gate_alternative hl T hp hr bound rate
        refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg ?_).trans h
        intro x hx
        exact le_of_not_gt hx
      refine (finite_eventMass_mono (pilotLaw_isLaw hp).nonneg
        (E := fun x => ¬ nearOneReject (l := l) T q δ x)
        (F := fun x => ¬ high (repeatBatch x)) ?_).trans ?_
      · intro x hx
        exact (not_or.mp hx).2
      · have hproj := sample_projection_event hp _ (repeat_indices_injective l) (fun x => ¬ high x)
        change eventMass (pilotLaw p) (fun x => ¬ high (repeatBatch x)) = _ at hproj
        rw [hproj]
        exact repeatMiss

/-- The exactly capped near-one specialization on the already-refined law. -/
theorem near_one_capped_test {l : ℕ} (hl : 0 < l) (T : Finset A)
    {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) {δ : ℝ} (hd : 0 < δ)
    (hcap : ∀ a ∈ T, q a ≤ δ)
    (hwide : 8*δ*Real.sqrt δ ≤ tailScore T q q)
    (hscale : 8192*Real.sqrt δ ≤ (l : ℝ)*tailScore T q q)
    (hoverlap : tailOverlap T p q ≤ δ) :
    eventMass (pilotLaw q) (nearOneReject (l := l) T q δ) ≤ 1/50 ∧
      eventMass (pilotLaw p) (fun x => ¬ nearOneReject (l := l) T q δ x) ≤ 1/100 :=
  overlap_capped_test hl T hp hq hd le_rfl hcap hwide hscale hoverlap

/-- The same statistical gate at regular scale n, with the smaller atom
cap 1/(n² x) supplied by the tail refinement. -/
theorem regular_capped_test {l : ℕ} (hl : 0 < l) (T : Finset A)
    {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) {n x : ℝ} (hn : 0 < n) (hx : 0 < x)
    (hnx : 1 ≤ n*x) (hcap : ∀ a ∈ T, q a ≤ 1/(n^2*x))
    (hmoment : 8*Real.sqrt x/n ≤ tailScore T q q)
    (hscale : 8192*Real.sqrt x ≤ (l : ℝ)*tailScore T q q)
    (hoverlap : tailOverlap T p q ≤ x) :
    eventMass (pilotLaw q) (nearOneReject (l := l) T q x) ≤ 1/50 ∧
      eventMass (pilotLaw p) (fun s => ¬ nearOneReject (l := l) T q x s) ≤ 1/100 := by
  have hb : 1/(n^2*x) ≤ x := by
    rw [div_le_iff₀ (show 0 < n^2*x by positivity)]
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hnx 2
    nlinarith
  have eqRoot : Real.sqrt (1/(n^2*x)) = 1/(n*Real.sqrt x) := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one,
      Real.sqrt_mul (sq_nonneg n), Real.sqrt_sq hn.le]
  have hwide : 8*x*Real.sqrt (1/(n^2*x)) ≤ tailScore T q q := by
    rw [eqRoot]
    have hx' := Real.sqrt_pos.mpr hx
    have sq := Real.sq_sqrt hx.le
    calc
      _ = 8*Real.sqrt x/n := by
        field_simp [hn.ne', hx'.ne']
        nlinarith
      _ ≤ _ := hmoment
  exact overlap_capped_test hl T hp hq hx hb hcap hwide hscale hoverlap

def overlapBatchSize (M x : ℝ) : ℕ := ⌈8192*Real.sqrt x/M⌉₊

/-- Concrete sample budget and both errors at the regular tail scale. -/
theorem regular_capped_ceiling (T : Finset A) {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (hnx : 1 ≤ (n : ℝ)*x)
    (hcap : ∀ a ∈ T, q a ≤ 1/((n : ℝ)^2*x))
    (hmoment : 8*Real.sqrt x/(n : ℝ) ≤ tailScore T q q)
    (hoverlap : tailOverlap T p q ≤ x) :
    let l := overlapBatchSize (tailScore T q q) x
    l+(l+l) ≤ 3072*n ∧
    eventMass (pilotLaw q) (nearOneReject (l := l) T q x) ≤ 1/50 ∧
    eventMass (pilotLaw p) (fun s => ¬ nearOneReject (l := l) T q x s) ≤ 1/100 := by
  let M := tailScore T q q
  let l := overlapBatchSize M x
  change l+(l+l) ≤ 3072*n ∧
    eventMass (pilotLaw q) (nearOneReject (l := l) T q x) ≤ 1/50 ∧
    eventMass (pilotLaw p) (fun s => ¬ nearOneReject (l := l) T q x s) ≤ 1/100
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : 0 < M :=
    lt_of_lt_of_le (show 0 < 8*Real.sqrt x/(n : ℝ) by positivity) hmoment
  have hlo : 0 < l := Nat.ceil_pos.mpr (by positivity)
  have base := Nat.le_ceil (8192*Real.sqrt x/M)
  have hscale : 8192*Real.sqrt x ≤ (l : ℝ)*M := (div_le_iff₀ hM).mp base
  have ratio : 8192*Real.sqrt x/M ≤ ((1024*n : ℕ) : ℝ) := by
    rw [div_le_iff₀ hM, Nat.cast_mul, Nat.cast_ofNat]
    have scaled := (div_le_iff₀ hn').mp hmoment
    nlinarith
  have budget : l ≤ 1024*n := Nat.ceil_le.mpr ratio
  exact ⟨by omega, regular_capped_test hlo T hp hq hn' hx hnx hcap hmoment hscale hoverlap⟩

end
end CanonneQuantile
