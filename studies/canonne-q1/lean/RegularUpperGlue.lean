import GroupMassGate
import BatchTests

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def headOffDistance (T : Finset A) (a : A) (p q : A → ℝ) : ℝ :=
  ∑ i ∈ Tᶜ.erase a, |p i-q i|

/-- Changes outside one selected head label plus the change of total
mass bound the directed deficit on the whole head. -/
theorem head_deficit_from_off_distance (T : Finset A) {a : A} (ha : a ∉ T)
    {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    deficit p q Tᶜ ≤ |mass p T-mass q T| + headOffDistance T a p q := by
  let H := Tᶜ
  let O := H.erase a
  let D := ∑ j ∈ O, max (q j-p j) 0
  let U := ∑ j ∈ O, max (p j-q j) 0
  have am : a ∈ H := Finset.mem_compl.mpr ha
  have eqnet : (∑ j ∈ H, (q j-p j)) = mass p T-mass q T := by
    have eqP := Finset.sum_compl_add_sum T p
    have eqQ := Finset.sum_compl_add_sum T q
    rw [hp.total] at eqP
    rw [hq.total] at eqQ
    rw [Finset.sum_sub_distrib]
    unfold H mass
    linarith
  have diff : (∑ j ∈ O, (q j-p j)) = D-U := by
    dsimp [D, U]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hh : p j ≤ q j
    · simp [max_eq_left (sub_nonneg.mpr hh), max_eq_right (sub_nonpos.mpr hh)]
    · simp [max_eq_right (sub_nonpos.mpr (le_of_not_ge hh)), max_eq_left (sub_nonneg.mpr (le_of_not_ge hh))]
  have absolute : headOffDistance T a p q = D+U := by
    dsimp [headOffDistance, D, U, O, H]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hh : p j ≤ q j
    · rw [abs_of_nonpos (sub_nonpos.mpr hh), max_eq_left (sub_nonneg.mpr hh),
        max_eq_right (sub_nonpos.mpr hh), add_zero]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hh)),
        max_eq_right (sub_nonpos.mpr (le_of_not_ge hh)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge hh)), zero_add]
  rw [← Finset.sum_erase_add H (fun j => q j-p j) am, diff] at eqnet
  have ub : max (q a-p a) 0 ≤ |mass p T-mass q T| + U := by
    apply max_le
    · have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => le_max_right _ _)
      linarith [le_abs_self (mass p T-mass q T)]
    · have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => le_max_right _ _)
      positivity
  change (∑ j ∈ H, max (q j-p j) 0) ≤ _
  rw [← Finset.sum_erase_add H (fun j => max (q j-p j) 0) am, absolute]
  change D+max (q a-p a) 0 ≤ |mass p T-mass q T|+(D+U)
  linarith

def groupedIdentityTest (q : A → ℝ) (e : ℝ) (n : ℕ) (f : (Fin n → A) → ℝ) : Prop :=
  (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧ tailRejection q f ≤ 1/3 ∧
  ∀ p : A → ℝ, IsLaw p → e < totalVariation p q → 2/3 ≤ tailRejection p f

/-- Compose actual unconditional tests for the group mass, off-largest
head differences, and a strict tail-overlap tolerance. -/
theorem regular_upper_from_tests (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {a : A} (ha : a ∉ T) {n m k : ℕ} (hn : 0 < n) {e r x : ℝ}
    (hgap : 1024*groupScale q T n/(n : ℝ)+r ≤ e-mass q T+x)
    {shape : (Fin m → A) → ℝ}
    (shUnit : ∀ z, 0 ≤ shape z ∧ shape z ≤ 1) (shNull : tailRejection q shape ≤ 1/10)
    (shAlt : ∀ p : A → ℝ, IsLaw p → r < headOffDistance T a p q →
      9/10 ≤ tailRejection p shape)
    {tailTest : (Fin k → A) → ℝ}
    (tUnit : ∀ z, 0 ≤ tailTest z ∧ tailTest z ≤ 1) (tNull : tailRejection q tailTest ≤ 1/50)
    (tAlt : ∀ p : A → ℝ, IsLaw p → tailOverlap T p q < x → 99/100 ≤ tailRejection p tailTest) :
    ∃ f, groupedIdentityTest q e (n+m+k) f := by
  classical
  let E := groupMassReject (n := n) q T
  let g (z : Fin n → A) : ℝ := if E z then 1 else 0
  let gs := batchOr g shape
  let f := batchOr gs tailTest
  have gUnit (z) : 0 ≤ g z ∧ g z ≤ 1 := by by_cases h : E z <;> simp [g, h]
  have gsUnit := batchOr_unit gUnit shUnit
  have gNull : tailRejection q g ≤ 1/100 := by
    rw [show tailRejection q g = eventMass (pilotLaw q) E from rejection_indicator q E]
    exact group_gate_null q hq T
  have gAlt (p : A → ℝ) (hp : IsLaw p)
      (h : 1024*groupScale q T n < (n : ℝ)*|mass p T-mass q T|) :
      99/100 ≤ tailRejection p g := by
    rw [show tailRejection p g = eventMass (pilotLaw p) E from rejection_indicator p E]
    have err := group_gate_alternative q hq T hp h
    have comp := eventMass_complement (pilotLaw_isLaw hp) E
    linarith
  refine ⟨f, batchOr_unit gsUnit tUnit, ?_, ?_⟩
  · have h1 := (batchOr_bounds hq gUnit shUnit).2.2
    have h2 := (batchOr_bounds hq gsUnit tUnit).2.2
    change tailRejection q gs ≤ tailRejection q g+tailRejection q shape at h1
    change tailRejection q f ≤ tailRejection q gs+tailRejection q tailTest at h2
    linarith
  · intro p hp hfar
    have gsB := batchOr_bounds hp gUnit shUnit
    have both := batchOr_bounds hp gsUnit tUnit
    by_cases hmass : 1024*groupScale q T n < (n : ℝ)*|mass p T-mass q T|
    · have h := (gAlt p hp hmass).trans (gsB.1.trans both.1)
      linarith
    by_cases hshape : r < headOffDistance T a p q
    · have h := (shAlt p hp hshape).trans (gsB.2.1.trans both.1)
      linarith
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have massBound : |mass p T-mass q T| ≤ 1024*groupScale q T n/(n : ℝ) := by
      rw [le_div_iff₀ hn']
      linarith [le_of_not_gt hmass]
    have headBound := head_deficit_from_off_distance T ha hp hq
    have tv := totalVariation_eq_suffix_mass_add_deficit_sub_overlap hp hq T
    change totalVariation p q = mass q T+deficit p q Tᶜ-tailOverlap T p q at tv
    have hsmall : tailOverlap T p q < x := by linarith [le_of_not_gt hshape]
    have h := (tAlt p hp hsmall).trans both.2.1
    linarith

/-- The no-tail case uses only a group test and the supplied actual
off-largest head statistic. -/
theorem regular_upper_head_only (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {a : A} (ha : a ∉ T) {n m : ℕ} (hn : 0 < n) {e r : ℝ}
    (hgap : 1024*groupScale q T n/(n : ℝ)+r ≤ e-mass q T)
    {shape : (Fin m → A) → ℝ}
    (shUnit : ∀ z, 0 ≤ shape z ∧ shape z ≤ 1) (shNull : tailRejection q shape ≤ 1/10)
    (shAlt : ∀ p : A → ℝ, IsLaw p → r < headOffDistance T a p q →
      9/10 ≤ tailRejection p shape) :
    ∃ f, groupedIdentityTest q e (n+m) f := by
  have hg : 1024*groupScale q T n/(n : ℝ)+r ≤ e-mass q T+0 := by simpa using hgap
  have h := regular_upper_from_tests q hq T ha hn hg shUnit shNull shAlt
    (k := 0) (tailTest := fun _ => 0) (fun _ => ⟨le_rfl, zero_le_one⟩)
    (by simp [tailRejection])
    (fun p hp hov => False.elim (not_lt.mpr (overlap_nonneg hp hq T) hov))
  simpa only [Nat.add_zero] using h

/-- Regular full upper composition at K >= 16, conditional on the supplied
off-largest shape statistic on ordinary full iid samples. -/
theorem regular_upper_with_criterion (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {a : A} (ha : a ∉ T) {n m : ℕ} (hn : 0 < n) {e r x : ℝ}
    (hx : 0 < x) (hnx : 1 ≤ (n : ℝ)*x)
    (hlarge : 16 ≤ criterion (tailMask T q) (n : ℝ) x)
    (hgap : 1024*groupScale q T n/(n : ℝ)+r ≤ e-mass q T+x)
    {shape : (Fin m → A) → ℝ}
    (shUnit : ∀ z, 0 ≤ shape z ∧ shape z ≤ 1) (shNull : tailRejection q shape ≤ 1/10)
    (shAlt : ∀ p : A → ℝ, IsLaw p → r < headOffDistance T a p q →
      9/10 ≤ tailRejection p shape) :
    ∃ j ≤ 3073*n+m, ∃ f, groupedIdentityTest q e j f := by
  obtain ⟨k, hk, f, hunit, hnull, halt⟩ := regular_tail_from_criterion q hq T hn hx hnx hlarge
  have done := regular_upper_from_tests q hq T ha hn hgap shUnit shNull shAlt
    hunit hnull (fun p hp h => halt p hp h.le)
  exact ⟨n+m+k, by omega, done⟩

end
end CanonneQuantile
