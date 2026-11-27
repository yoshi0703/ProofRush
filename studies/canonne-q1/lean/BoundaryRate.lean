import NearComplete

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting CanonneRefinement
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem atom_le_one {q : A → ℝ} (hq : IsLaw q) (i : A) : q i ≤ 1 :=
  (Finset.single_le_sum (fun j _ => hq.nonneg j) (Finset.mem_univ i)).trans_eq hq.total

/-- All symbols of the declared alphabet, including null atoms, enter this check. -/
theorem strict_alternative_iff_atom (q : A → ℝ) (hq : IsLaw q) (e : ℝ) :
    (∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q) ↔ ∃ a, e < 1-q a := by
  classical
  have hover {p : A → ℝ} (hp : IsLaw p) :
      totalVariation p q = 1-∑ a, min (p a) (q a) :=
    CanonneNearOne.totalVariation_eq_one_sub_overlap (p:=p) (q:=q)
      ⟨hp.nonneg,hp.total⟩ ⟨hq.nonneg,hq.total⟩
  constructor
  · rintro ⟨p,hp,hfar⟩
    by_contra! hzero
    have hlo : 1-e ≤ ∑ a, min (p a) (q a) := by
      calc
        _ = (∑ a, p a)*(1-e) := by rw [hp.total,one_mul]
        _ = ∑ a, p a*(1-e) := Finset.sum_mul ..
        _ ≤ ∑ a, p a*q a := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by linarith [hzero i]) (hp.nonneg i)
        _ ≤ _ := Finset.sum_le_sum fun i _ => le_min
          (mul_le_of_le_one_right (hp.nonneg i) (atom_le_one hq i))
          (mul_le_of_le_one_left (hq.nonneg i) (atom_le_one hp i))
    rw [hover hp] at hfar
    linarith
  · rintro ⟨a,ha⟩
    let p (i : A) : ℝ := if i=a then 1 else 0
    have hp : IsLaw p := ⟨fun i => by by_cases h:i=a <;> simp [p,h],by simp [p]⟩
    refine ⟨p,hp,?_⟩
    rw [hover hp]
    have heq : (∑ i, min (p i) (q i)) = q a := by
      calc
        _ = ∑ i, if i=a then q a else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : i=a
          · subst i; simp [p,min_eq_right (atom_le_one hq a)]
          · simp [p,h,min_eq_left (hq.nonneg i)]
        _ = _ := by simp
    rwa [heq]

omit [DecidableEq A] in
theorem zero_budget_when_vacuous (q : A → ℝ) (e : ℝ)
    (h : ¬ ∃ p : A → ℝ, IsLaw p ∧ e < totalVariation p q) : ∃ f, GoodTest q e 0 f := by
  refine ⟨fun _ => 0,fun _ => ⟨le_rfl,zero_le_one⟩,?_,?_⟩
  · simp [rejection]
  · intro p hp hfar
    exact (h ⟨p,hp,hfar⟩).elim

def directRate (q : A → ℝ) (δ : ℝ) : ℕ := ⌈1/nearMoment q δ⌉₊

/-- Fixed absolute factors compare the explicit integer functional to the true testing budget. -/
theorem directRate_comparison (q : A → ℝ) (hq : IsLaw q) {δ : ℝ} (hd : 0 < δ)
    (hJ : 16*δ ≤ nearMoment q δ)
    (hfar : ∃ p : A → ℝ, IsLaw p ∧ 1-δ < totalVariation p q) :
    (∀ m, (∃ f, GoodTest q (1-δ) m f) → directRate q δ ≤ 65*m) ∧
    ∃ n ≤ 49152*directRate q δ, ∃ f, GoodTest q (1-δ) n f := by
  have hj : 0 < nearMoment q δ := lt_of_lt_of_le (by positivity : 0 < 16*δ) hJ
  obtain ⟨hlo,hup⟩ := finite_near_one_sample_bounds q hq hd hJ hfar
  constructor
  · intro m hm
    have h := hlo m hm
    apply Nat.ceil_le.mpr
    rw [Nat.cast_mul,Nat.cast_ofNat]
    apply (div_le_iff₀ hj).mpr
    nlinarith only [h,mul_nonneg (Nat.cast_nonneg m : (0:ℝ)≤m) hj.le]
  · refine ⟨3*nearBatch q δ,?_,hup⟩
    have hceil : 1/nearMoment q δ ≤ (directRate q δ:ℝ) := Nat.le_ceil _
    have hbound : nearBatch q δ ≤ 16384*directRate q δ := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_mul,Nat.cast_ofNat]
      simpa only [div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left hceil (by norm_num : (0:ℝ) ≤ 16384)
    omega

end
end CanonneQuantile
