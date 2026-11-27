import SplitLabels
import NearOneBins
import NearOneGate

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneRefinement CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def nearBatch (q : A → ℝ) (δ : ℝ) : ℕ := ⌈16384 / nearMoment q δ⌉₊

theorem near_one_good_test (q : A → ℝ) (hq : IsLaw q) {δ : ℝ} (hd : 0 < δ)
    (hJ : 16*δ ≤ nearMoment q δ) :
    let l := nearBatch q δ
    ∃ f, GoodTest q (1-δ) (l+(l+l)) f := by
  classical
  let J := nearMoment q δ
  let l := nearBatch q δ
  let m (a : A) := multiplicity δ (q a)
  have hm a : 0 < m a := multiplicity_pos _ _
  have hj : 0 < J := lt_of_lt_of_le (by positivity : 0 < 16*δ) hJ
  have hl : 0 < l := Nat.ceil_pos.mpr (div_pos (by norm_num) hj)
  have hreal : 16384/J ≤ (l : ℝ) := Nat.le_ceil _
  let Q := clone m q
  have clones (p : A → ℝ) (hp : IsLaw p) : IsLaw (clone m p) := by
    refine ⟨fun a => div_nonneg (hp.nonneg _) (by positivity), ?_⟩
    simpa only [mul_one,hp.total] using clone_moment m hm p (fun _ => 1)
  have hQ := clones q hq
  let H := height Q
  have hH : 0 ≤ H := Finset.sum_nonneg fun a _ => mul_nonneg (hQ.nonneg a) (Real.sqrt_nonneg _)
  have hcap : ∀ a ∈ (Finset.univ : Finset (Labels m)), Q a ≤ δ := fun a _ => clone_atom_le hd
  have hwide : 8*δ*Real.sqrt δ ≤ H := actual_near_one_height q hq.nonneg hd hJ
  have hscale : 8192*Real.sqrt δ ≤ (l : ℝ)*H := by
    have h1 := (actual_split_height q hq.nonneg hd).2
    rw [← scaled_near_moment q hq.nonneg hd] at h1
    change Real.sqrt δ*J ≤ Real.sqrt 2 * H at h1
    have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), sq_nonneg (Real.sqrt 2-2)]
    have h3 := (div_le_iff₀ hj).mp hreal
    have h4 := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hH))
      (by positivity : 0 ≤ (l : ℝ))
    nlinarith [mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg δ)]
  by_cases nonempty : ∃ p : A → ℝ, IsLaw p ∧ 1-δ < totalVariation p q
  · let E := nearOneReject (l := l) Finset.univ Q δ
    let I (x : Fin (l+(l+l)) → Labels m) : ℝ := if E x then 1 else 0
    let f := pull (splitKernel m) I
    have hI (x) : 0 ≤ I x ∧ I x ≤ 1 := by by_cases h : E x <;> simp [I,h]
    have test_eq (p : A → ℝ) :
        rejection (pilotLaw p) f = eventMass (pilotLaw (clone m p)) E := by
      change (∑ x, CanonneMarker.recordLaw p x * pull (splitKernel m) I x) = _
      rw [(clone_test m hm p I hI).2, eventMass_eq_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : E x <;> simp [I,hx,CanonneMarker.recordLaw,pilotLaw]
    have gate {p : A → ℝ} (hp : IsLaw p) (hfar : 1-δ < totalVariation p q) :
        eventMass (pilotLaw Q) E ≤ 1/50 ∧
        eventMass (pilotLaw (clone m p)) (fun x => ¬ E x) ≤ 1/100 := by
      have hTV := CanonneNearOne.totalVariation_eq_one_sub_overlap
        (p := p) (q := q) ⟨hp.nonneg,hp.total⟩ ⟨hq.nonneg,hq.total⟩
      change totalVariation p q = 1-∑ a, min (p a) (q a) at hTV
      have hov : tailOverlap Finset.univ (clone m p) Q ≤ δ := by
        change (∑ a, min (clone m p a) (clone m q a)) ≤ δ
        rw [clone_overlap]
        · linarith
        · exact hm
      exact near_one_capped_test hl Finset.univ (clones p hp) hQ hd hcap hwide hscale hov
    refine ⟨f, (clone_test m hm q I hI).1, ?_, ?_⟩
    · obtain ⟨p,hp,hfar⟩ := nonempty
      rw [test_eq]
      linarith [(gate hp hfar).1]
    · intro p hp hfar
      rw [test_eq]
      have htotal : (∑ x : Fin (l+(l+l)) → Labels m, pilotLaw (clone m p) x) = 1 :=
        (pilotLaw_isLaw (clones p hp)).total
      have hsum : eventMass (pilotLaw (clone m p)) E +
          eventMass (pilotLaw (clone m p)) (fun x => ¬ E x) = 1 := by
        rw [eventMass_eq_sum,eventMass_eq_sum,← Finset.sum_add_distrib,← htotal]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      linarith [(gate hp hfar).2]
  · refine ⟨fun _ => 0, fun _ => ⟨le_rfl,zero_le_one⟩, ?_, ?_⟩
    · simp [rejection]
    · intro p hp hfar
      exact (nonempty ⟨p,hp,hfar⟩).elim

omit [DecidableEq A] in
theorem no_zero_test_with_alternative (q : A → ℝ) {e : ℝ} {p : A → ℝ}
    (hp : IsLaw p) (hfar : e < totalVariation p q) : ¬ ∃ f, GoodTest q e 0 f := by
  rintro ⟨f, _, hnull, halt⟩
  have halt' := halt p hp hfar
  have eq : (pilotLaw (I := Fin 0) p) = pilotLaw q := by
    funext x
    simp [pilotLaw]
  rw [eq] at halt'
  linarith

/-- An unconditional fixed-radius comparison for the near-one branch,
with actual tests and explicit integer sample counts. -/
theorem finite_near_one_sample_bounds (q : A → ℝ) (hq : IsLaw q) {δ : ℝ} (hd : 0 < δ)
    (hJ : 16*δ ≤ nearMoment q δ) (nonempty : ∃ p : A → ℝ, IsLaw p ∧ 1-δ < totalVariation p q) :
    (∀ n, (∃ f, GoodTest q (1-δ) n f) → (1/64 : ℝ) < n*nearMoment q δ) ∧
    (∃ f, GoodTest q (1-δ) (3*nearBatch q δ) f) := by
  constructor
  · intro n ht
    by_cases hn : 0 < n
    · by_contra! hsmall
      exact (no_good_test_small_near_one_moment hq hn hd hsmall) ht
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      obtain ⟨p,hp,hfar⟩ := nonempty
      exact (no_zero_test_with_alternative q hp hfar ht).elim
  · rw [show 3*nearBatch q δ = nearBatch q δ + (nearBatch q δ + nearBatch q δ) by omega]
    exact near_one_good_test q hq hd hJ

end
end CanonneQuantile
