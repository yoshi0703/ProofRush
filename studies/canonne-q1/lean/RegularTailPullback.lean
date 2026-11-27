import NearOneGate
import TailCalibration

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneRefinement
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def tailMask (T : Finset A) (q : A → ℝ) (a : A) : ℝ :=
  if a ∈ T then q a else 0

def tailCloneCounts (T : Finset A) (q : A → ℝ) (cap : ℝ) (a : A) : ℕ :=
  multiplicity cap (tailMask T q a)

def clonedTail (T : Finset A) (m : A → ℕ) : Finset (Labels m) :=
  Finset.univ.filter (fun s => s.1 ∈ T)

omit [Fintype A] in
private theorem tail_counts_pos (T : Finset A) (q : A → ℝ) (cap : ℝ) :
    ∀ a, 0 < tailCloneCounts T q cap a :=
  fun a => multiplicity_pos _ (tailMask T q a)

omit [Fintype A] in
theorem tailCloneCounts_off_tail (T : Finset A) (q : A → ℝ) (cap : ℝ)
    {a : A} (ha : a ∉ T) : tailCloneCounts T q cap a = 1 := by
  simp [tailCloneCounts, tailMask, ha, multiplicity]

omit [DecidableEq A] in
private theorem cloned_isLaw (m : A → ℕ) (hm : ∀ a, 0 < m a) {p : A → ℝ}
    (hp : IsLaw p) : IsLaw (clone m p) := by
  refine ⟨fun a => div_nonneg (hp.nonneg _) (by positivity), ?_⟩
  simpa only [mul_one, hp.total] using clone_moment m hm p (fun _ => 1)

theorem cloned_tail_height (T : Finset A) (m : A → ℕ) (q : A → ℝ) :
    tailScore (clonedTail T m) (clone m q) (clone m q) =
      height (clone m (tailMask T q)) := by
  unfold tailScore clonedTail height
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a.1 ∈ T <;> simp [h, tailMask, clone]

theorem cloned_tail_overlap (T : Finset A) (m : A → ℕ) (hm : ∀ a, 0 < m a) (p q : A → ℝ) :
    tailOverlap (clonedTail T m) (clone m p) (clone m q) = tailOverlap T p q := by
  calc
    _ = ∑ a, min (clone m (tailMask T p) a) (clone m (tailMask T q) a) := by
      unfold tailOverlap clonedTail
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a.1 ∈ T <;> simp [h, tailMask, clone]
    _ = ∑ a, min (tailMask T p a) (tailMask T q a) :=
      clone_overlap m hm (tailMask T q) (tailMask T p)
    _ = _ := by
      have hfilter : T = Finset.univ.filter (fun a => a ∈ T) := by ext a; simp
      unfold tailOverlap
      rw [hfilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a ∈ T <;> simp [h, tailMask]

theorem cloned_tail_atom_cap (T : Finset A) (q : A → ℝ) {cap : ℝ} (hc : 0 < cap) :
    let m := tailCloneCounts T q cap
    ∀ a ∈ clonedTail T m, clone m q a ≤ cap := by
  intro m a ha
  have mem : a.1 ∈ T := (Finset.mem_filter.mp ha).2
  change q a.1/(multiplicity cap (tailMask T q a.1) : ℝ) ≤ cap
  rw [tailMask, ite_eq_left mem]
  exact clone_atom_le hc

/-- Rejection probability against an actual ordered iid law on the
original labels, evaluated for a randomized decision kernel. -/
def tailRejection {k : ℕ} (p : A → ℝ) (f : (Fin k → A) → ℝ) : ℝ :=
  ∑ x, pilotLaw p x * f x

/-- A test that distinguishes the original reference from every
full law having small overlap on the specified tail. -/
def GoodTailTest (q : A → ℝ) (T : Finset A) (x : ℝ) (k : ℕ) (f : (Fin k → A) → ℝ) : Prop :=
  (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
  tailRejection q f ≤ 1/50 ∧
  ∀ p : A → ℝ, IsLaw p → tailOverlap T p q ≤ x → 99/100 ≤ tailRejection p f

/-- Pull the regular overlap test back through a finite stochastic
refinement that splits only the selected tail. The head labels and
their total mass remain available and unchanged in the full sample. -/
theorem regular_tail_good_test (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (hnx : 1 ≤ (n : ℝ)*x)
    (hmoment : 8*Real.sqrt x/(n : ℝ) ≤
      height (clone (tailCloneCounts T q (1/((n : ℝ)^2*x))) (tailMask T q))) :
    ∃ k ≤ 3072*n, ∃ f, GoodTailTest q T x k f := by
  classical
  let cap := 1/((n : ℝ)^2*x)
  let m := tailCloneCounts T q cap
  let U := clonedTail T m
  let Q := clone m q
  let M := tailScore U Q Q
  let l := overlapBatchSize M x
  have hc : 0 < cap := by positivity
  have hm := tail_counts_pos T q cap
  have hQ := cloned_isLaw m hm hq
  have mass_cap : ∀ a ∈ U, Q a ≤ 1/((n : ℝ)^2*x) := cloned_tail_atom_cap T q hc
  have thick : 8*Real.sqrt x/(n : ℝ) ≤ M := by
    dsimp only [M, U, Q]
    rw [cloned_tail_height]
    exact hmoment
  by_cases nonempty : ∃ p : A → ℝ, IsLaw p ∧ tailOverlap T p q ≤ x
  · let E := nearOneReject (l := l) U Q x
    let I (z : Fin (l+(l+l)) → Labels m) : ℝ := if E z then 1 else 0
    let f := pull (splitKernel m) I
    have hI (z) : 0 ≤ I z ∧ I z ≤ 1 := by by_cases h : E z <;> simp [I,h]
    have pull_eq (p : A → ℝ) :
        tailRejection p f = eventMass (pilotLaw (clone m p)) E := by
      change (∑ z, CanonneMarker.recordLaw p z * pull (splitKernel m) I z) = _
      rw [(clone_test m hm p I hI).2, eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : E z <;> simp [I,hz,CanonneMarker.recordLaw,pilotLaw]
    have gate {p : A → ℝ} (hp : IsLaw p) (hov : tailOverlap T p q ≤ x) :
        l+(l+l) ≤ 3072*n ∧ eventMass (pilotLaw Q) E ≤ 1/50 ∧
        eventMass (pilotLaw (clone m p)) (fun z => ¬ E z) ≤ 1/100 := by
      have hs : tailOverlap U (clone m p) Q ≤ x :=
        (cloned_tail_overlap T m hm p q).trans_le hov
      exact regular_capped_ceiling U (cloned_isLaw m hm hp) hQ hn hx hnx mass_cap thick hs
    obtain ⟨p₀, hp₀, h₀⟩ := nonempty
    obtain ⟨budget, null, _⟩ := gate hp₀ h₀
    refine ⟨l+(l+l), budget, f, (clone_test m hm q I hI).1, ?_, ?_⟩
    · rw [pull_eq]
      exact null
    · intro p hp hov
      rw [pull_eq]
      have total : (∑ z : Fin (l+(l+l)) → Labels m, pilotLaw (clone m p) z) = 1 :=
        (pilotLaw_isLaw (cloned_isLaw m hm hp)).total
      have compl : eventMass (pilotLaw (clone m p)) E +
          eventMass (pilotLaw (clone m p)) (fun z => ¬ E z) = 1 := by
        rw [eventMass_eq_sum, eventMass_eq_sum, ← Finset.sum_add_distrib, ← total]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : E z <;> simp [hz]
      linarith [(gate hp hov).2.2]
  · refine ⟨0, by omega, fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩
    · simp [tailRejection]
    · intro p hp hov
      exact (nonempty ⟨p,hp,hov⟩).elim

theorem tailMask_nonneg (T : Finset A) {q : A → ℝ} (hq : IsLaw q) :
    ∀ a, 0 ≤ tailMask T q a := by
  intro a
  unfold tailMask
  split <;> simp [hq.nonneg]

/-- The regular tail test on the original label space at the explicit
truncated-moment criterion. -/
theorem regular_tail_from_criterion (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (hnx : 1 ≤ (n : ℝ)*x)
    (hlarge : 16 ≤ criterion (tailMask T q) (n : ℝ) x) :
    ∃ k ≤ 3072*n, ∃ f, GoodTailTest q T x k f := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have H := calibrated_split_height (tailMask T q) (tailMask_nonneg T hq) hn' hx hlarge
  exact regular_tail_good_test q hq T hn hx hnx H

/-- The same test with the positive root of the tail criterion as input. -/
theorem regular_tail_from_root (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) (hnx : 1 ≤ (n : ℝ)*x)
    (hroot : 16*Real.sqrt x ≤ root (tailMask T q) (tailMask_nonneg T hq)
      (n : ℝ) (Nat.cast_nonneg n)) :
    ∃ k ≤ 3072*n, ∃ f, GoodTailTest q T x k f := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := criterion_at_forward_scale (tailMask T q) (tailMask_nonneg T hq) hn' hx hroot
  exact regular_tail_from_criterion q hq T hn hx hnx h

end
end CanonneQuantile
