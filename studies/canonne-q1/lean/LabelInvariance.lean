import CanonicalRegular
import RegularTailPullback

open scoped BigOperators
open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting

namespace CanonneHeadEnvelope

variable {A B : Type*} [Fintype A] [Fintype B]

theorem isLaw_equiv (e : B ≃ A) (q : A → ℝ) : IsLaw (q ∘ e) ↔ IsLaw q := by
  constructor
  · intro h
    refine ⟨?_, (e.sum_comp q).symm.trans h.total⟩
    intro a
    obtain ⟨b,rfl⟩ := e.surjective a
    exact h.nonneg b
  · intro h
    exact ⟨fun b ↦ h.nonneg (e b), (e.sum_comp q).trans h.total⟩

theorem totalVariation_equiv (e : B ≃ A) (p q : A → ℝ) :
    totalVariation (p ∘ e) (q ∘ e) = totalVariation p q := by
  unfold totalVariation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun a ↦ |p a-q a|)]

theorem strict_alternative_equiv (e : B ≃ A) (q : A → ℝ) (ε : ℝ) :
    (∃ p : B → ℝ, IsLaw p ∧ ε < totalVariation p (q ∘ e)) ↔
      ∃ p : A → ℝ, IsLaw p ∧ ε < totalVariation p q := by
  constructor
  · rintro ⟨p,hp,hfar⟩
    refine ⟨p ∘ e.symm, (isLaw_equiv e.symm p).mpr hp,?_⟩
    rw [← totalVariation_equiv e]
    simpa [Function.comp_def] using hfar
  · rintro ⟨p,hp,hfar⟩
    exact ⟨p ∘ e, (isLaw_equiv e p).mpr hp, (totalVariation_equiv e p q).symm ▸ hfar⟩

theorem nearOneMoment_equiv (e : B ≃ A) (q : A → ℝ) (δ : ℝ) :
    CanonneNearOne.nearOneMoment (q ∘ e) δ = CanonneNearOne.nearOneMoment q δ :=
  e.sum_comp (fun a ↦ q a * min 1 (Real.sqrt (q a / δ)))

section Vacuity

variable [Nonempty A]

noncomputable def minimumAtom (q : A → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty q

theorem minimumAtom_le (q : A → ℝ) (a : A) : minimumAtom q ≤ q a :=
  Finset.inf'_le q (Finset.mem_univ a)

theorem exists_minimumAtom (q : A → ℝ) : ∃ a, q a = minimumAtom q := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty) q
  exact ⟨a,ha.symm⟩

theorem minimumAtom_equiv [Nonempty B] (e : B ≃ A) (q : A → ℝ) :
    minimumAtom (q ∘ e) = minimumAtom q := by
  obtain ⟨a,ha⟩ := exists_minimumAtom q
  obtain ⟨b,hb⟩ := exists_minimumAtom (q ∘ e)
  apply le_antisymm
  · have h := minimumAtom_le (q ∘ e) (e.symm a)
    simpa [ha] using h
  · rw [← hb]
    exact minimumAtom_le q (e b)

omit [Nonempty A] in
private theorem atom_le_one {q : A → ℝ} (hq : IsLaw q) (a : A) : q a ≤ 1 := by
  rw [← hq.total]
  exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (Finset.mem_univ a)

theorem totalVariation_le_one_sub_minimum {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    totalVariation p q ≤ 1 - minimumAtom q := by
  have htv := CanonneNearOne.totalVariation_eq_one_sub_overlap
    (p := p) (q := q) ⟨hp.nonneg,hp.total⟩ ⟨hq.nonneg,hq.total⟩
  change totalVariation p q = _ at htv
  obtain ⟨a,ha⟩ := exists_minimumAtom q
  have hmin₀ : 0 ≤ minimumAtom q := ha ▸ hq.nonneg a
  have hmin₁ : minimumAtom q ≤ 1 := (minimumAtom_le q a).trans (atom_le_one hq a)
  have hsum : minimumAtom q ≤ ∑ a, min (p a) (q a) := by
    calc
      _ = ∑ a, minimumAtom q * p a := by rw [← Finset.mul_sum, hp.total, mul_one]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro b _
        refine le_min ?_ ?_
        · exact mul_le_of_le_one_left (hp.nonneg b) hmin₁
        · exact (mul_le_of_le_one_right hmin₀ (atom_le_one hp b)).trans (minimumAtom_le q b)
  rw [htv]
  linarith

theorem exists_strict_alternative_iff {q : A → ℝ} (hq : IsLaw q) (ε : ℝ) :
    (∃ p : A → ℝ, IsLaw p ∧ ε < totalVariation p q) ↔ ε < 1 - minimumAtom q := by
  constructor
  · rintro ⟨p,hp,hfar⟩
    exact hfar.trans_le (totalVariation_le_one_sub_minimum hp hq)
  · intro he
    classical
    obtain ⟨a,ha⟩ := exists_minimumAtom q
    let p := CanonneRegularTransfer.pointLaw a
    have hp : IsLaw p := CanonneRegularTransfer.pointLaw_isLaw a
    refine ⟨p,hp,?_⟩
    have h := CanonneNearOne.totalVariation_eq_one_sub_overlap (p := p) (q := q)
      ⟨hp.nonneg,hp.total⟩ ⟨hq.nonneg,hq.total⟩
    change totalVariation p q = _ at h
    have hpoint (b : A) : min (p b) (q b) = if b = a then q a else 0 := by
      by_cases hb : b = a
      · subst b
        simp [p, CanonneRegularTransfer.pointLaw, min_eq_right (atom_le_one hq a)]
      · simp [p, CanonneRegularTransfer.pointLaw, hb, Ne.symm hb, min_eq_left (hq.nonneg b)]
    simp only [hpoint, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ha] at h
    exact h.symm ▸ he

theorem exists_zero_draw_test_iff {q : A → ℝ} (hq : IsLaw q) (ε : ℝ) :
    (∃ f, GoodTest q ε 0 f) ↔ 1 - minimumAtom q ≤ ε := by
  constructor
  · rintro ⟨f,_,hn,halt⟩
    by_contra h
    obtain ⟨p,hp,hfar⟩ := (exists_strict_alternative_iff hq ε).mpr (lt_of_not_ge h)
    have ha := halt p hp hfar
    simp only [rejection, pilotLaw, Finset.univ_eq_empty, Finset.prod_empty, one_mul] at hn ha
    linarith
  · intro hv
    refine ⟨fun _ ↦ 0,fun _ ↦ ⟨le_rfl,zero_le_one⟩,by simp [rejection],?_⟩
    intro p hp hfar
    exact (not_lt_of_ge ((totalVariation_le_one_sub_minimum hp hq).trans hv) hfar).elim

end Vacuity

namespace CanonicalSplit

variable {q : A → ℝ} {ε : ℝ} [DecidableEq A]

omit [Fintype A] in
theorem tail_set_function_sum (s : CanonicalSplit q ε) (F : ℝ → ℝ) :
    (∑ a ∈ s.tailSet, F (q a)) = ∑ j, F (q (s.tail j)) :=
  Finset.sum_image (fun _ _ _ _ h ↦ Sum.inr.inj (s.label.injective h))

theorem tail_profile_eq (s : CanonicalSplit q ε) (n y : ℝ) :
    CanonneQuantile.tail (CanonneQuantile.tailMask s.tailSet q) n y =
      CanonneQuantile.tail (fun j ↦ q (s.tail j)) n y := by
  let F := fun x : ℝ ↦ n*x*Real.sqrt x / max 1 (n*y*Real.sqrt x)
  have hF : F 0 = 0 := by simp [F]
  change (∑ a, F (CanonneQuantile.tailMask s.tailSet q a)) = ∑ j, F (q (s.tail j))
  rw [← s.tail_set_function_sum F]
  have hs : Finset.univ.filter (fun a ↦ a ∈ s.tailSet) = s.tailSet := by
    ext a
    simp
  conv_rhs => rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ s.tailSet <;> simp [CanonneQuantile.tailMask, ha, hF]

theorem tail_root_eq (s : CanonicalSplit q ε) (hq : IsLaw q) {n : ℝ} (hn : 0 ≤ n) :
    CanonneQuantile.root (CanonneQuantile.tailMask s.tailSet q)
        (CanonneQuantile.tailMask_nonneg s.tailSet hq) n hn =
      CanonneQuantile.root (fun j ↦ q (s.tail j)) (fun _ ↦ hq.nonneg _) n hn := by
  let u := CanonneQuantile.tailMask s.tailSet q
  let v := fun j ↦ q (s.tail j)
  have hu := CanonneQuantile.tailMask_nonneg s.tailSet hq
  have hv : ∀ j, 0 ≤ v j := fun j ↦ hq.nonneg (s.tail j)
  apply (CanonneQuantile.exists_unique_tail_root u hu hn).unique
    (CanonneQuantile.root_spec u hu hn)
  refine ⟨(CanonneQuantile.root_spec v hv hn).1,?_⟩
  exact (s.tail_profile_eq n _).trans (CanonneQuantile.root_spec v hv hn).2

end CanonicalSplit

end CanonneHeadEnvelope
