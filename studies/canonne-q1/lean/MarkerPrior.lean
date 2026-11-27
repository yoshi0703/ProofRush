import HeadProfile
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace CanonneHeadEnvelope

theorem sourceCutoff_scale {d j : ℕ} {n A : ℝ} {h : Fin (d+1) → ℝ}
    (hn : 0 < n) (hA : 0 < A) (hh : ∀ i, 0 ≤ h i) :
    sourceCutoff n j (fun i ↦ A * h i) = A * sourceCutoff (n*A) j h := by
  unfold sourceCutoff
  simp_rw [Real.mul_rpow hA.le (hh _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hh i.succ) _),
    ← Real.rpow_mul hA.le, Real.sqrt_mul hn.le]
  have hExp : (2 : ℝ) / 3 * (3/4 : ℝ) = 1/2 := by norm_num
  rw [hExp, ← Real.sqrt_eq_rpow]
  have hS₁ := (Real.sqrt_pos.mpr hn).ne'
  have hS₂ := (Real.sqrt_pos.mpr hA).ne'
  have hS₃ := Real.sq_sqrt hA.le
  field_simp
  linear_combination (∑ i ∈ cutoffPrefix d j, (h i.succ)^((2 : ℝ)/3))^((3 : ℝ)/4) * hS₃

theorem headProfile_scale {d : ℕ} {n A : ℝ} {h : Fin (d+1) → ℝ}
    (hn : 0 < n) (hA : 0 < A) (hh : ∀ i, 0 ≤ h i) :
    headProfile n (fun i ↦ A * h i) = A * headProfile (n*A) h := by
  unfold headProfile
  simp_rw [sourceCutoff_scale hn hA hh]
  symm
  exact Finset.apply_inf'_eq_inf'_comp _ (fun x ↦ A*x) (fun x y ↦ by
    change A * min x y = min (A*x) (A*y)
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy, min_eq_left (mul_le_mul_of_nonneg_left hxy hA.le)]
    · rw [min_eq_right hyx, min_eq_right (mul_le_mul_of_nonneg_left hyx hA.le)])

theorem finite_deficit_eq_tv {A : Type*} [Fintype A] {p q : A → ℝ}
    (ht : ∑ a, p a = ∑ a, q a) :
    (∑ a, max (q a-p a) 0) = (∑ a, |p a-q a|) / 2 := by
  have h (a : A) : 2 * max (q a-p a) 0 = |p a-q a| + (q a-p a) := by
    by_cases ha : p a ≤ q a
    · rw [max_eq_left (sub_nonneg.mpr ha), abs_of_nonpos (sub_nonpos.mpr ha)]
      ring
    · have hb := (lt_of_not_ge ha).le
      rw [max_eq_right (sub_nonpos.mpr hb), abs_of_nonneg (sub_nonneg.mpr hb)]
      ring
  have hh : 2 * (∑ a, max (q a-p a) 0) = ∑ a, |p a-q a| := by
    rw [Finset.mul_sum]
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ht, sub_self, add_zero]
  linarith

private theorem paired_TV_constant {g : ℝ} (hg : g ≤ 1/2048) :
    Real.sqrt (Real.exp g - 1) / 2 ≤ 1/8 := by
  have hExp : Real.exp g ≤ 1 / (1 - (1 : ℝ)/2048) :=
    (Real.exp_le_exp.mpr hg).trans (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num))
  have ht : Real.sqrt (Real.exp g - 1) ≤ 1/4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  linarith

variable {H : Type*} [Fintype H]

/-- The sample mixture uses the actual original mass of each ordered head label, and one
unchanged tail marker. Its alternatives have far unconditional head deficit. -/
theorem exists_marker_paired_prior {d n : ℕ} (order : Fin (d+1) ≃ H)
    (q : H ⊕ Unit → ℝ) (hn : 0 < n) (hqn : ∀ x, 0 ≤ q x) (hq : ∑ x, q x = 1)
    (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i ↦ q (Sum.inl (order i))))
    {ε : ℝ} (hfar : 32*ε < headProfile n (fun i ↦ q (Sum.inl (order i)))) :
    ∃ p : (Fin ((d+1)/2) → Bool) → (H ⊕ Unit) → ℝ,
      (∀ s x, 0 ≤ p s x) ∧ (∀ s, ∑ x, p s x = 1) ∧
      (∀ s, p s (Sum.inr ()) = q (Sum.inr ())) ∧
      (∀ s, ε < ∑ h : H, max (q (Sum.inl h) - p s (Sum.inl h)) 0) ∧
      let M := mixture (fun s ↦ iidMass n (p s))
      (∑ x, |M x - iidMass n q x|) / 2 ≤ 1/8 := by
  let qH := fun i ↦ q (Sum.inl (order i))
  let a := fun i ↦ (qH i)^((1 : ℝ)/3)
  have ha : ∀ i, 0 < a i := fun i ↦ Real.rpow_pos_of_pos (hpos i) _
  have ho : Antitone a := fun i j hij ↦
    Real.rpow_le_rpow (hpos j).le (horder hij) (by norm_num)
  have hCube (i : Fin (d+1)) : (a i)^3 = qH i := by
    unfold a
    rw [← Real.rpow_mul_natCast (hpos i).le ((1 : ℝ)/3) 3]
    rw [show (1 : ℝ)/3 * (3 : ℕ) = 1 by norm_num, Real.rpow_one]
  have hcut : ∀ j ≤ d, 32*ε < headCutoff n d j a := by
    intro j hj
    have hj' : j ∈ Finset.range (d+1) := Finset.mem_range.mpr (by omega)
    have hp : headProfile n qH ≤ sourceCutoff n j qH := Finset.inf'_le _ hj'
    rw [headCutoff_eq_source hn (fun i ↦ (hpos i).le)]
    exact hfar.trans_le hp
  obtain ⟨z, hz, hzb, hdist, hbudget⟩ := exists_head_paired_shift n d a hn ha ho hcut
  let E : (Fin ((d+1)/2) × Bool) ↪ H ⊕ Unit :=
    ((adjacentEmbedding d).trans order.toEmbedding).trans Function.Embedding.inl
  have hE (i : Fin ((d+1)/2) × Bool) :
      q (E i) = (a (adjacentEmbedding d i))^3 := (hCube _).symm
  have hEp (i : Fin ((d+1)/2) × Bool) : 0 < q (E i) := hpos _
  have hEz (i : Fin ((d+1)/2) × Bool) : z i.1 ≤ q (E i) := by rw [hE]; exact hzb i
  have hBudget : ∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2 ≤ 1/2048 := by
    unfold pairCoefficient
    simp only [Function.comp_apply, hE]
    dsimp only [pairCoefficient, Function.comp_apply] at hbudget
    exact hbudget
  let p := embeddedLaw E q z
  obtain ⟨hp, _⟩ := embedded_iid_mixture_bound n E q z hEp hq hqn hz hEz
  have hMarker (s : Fin ((d+1)/2) → Bool) : p s (Sum.inr ()) = q (Sum.inr ()) := by
    apply embeddedLaw_unchanged
    rintro ⟨i,hi⟩
    cases hi
  refine ⟨p, fun s ↦ (hp s).1, fun s ↦ (hp s).2.1, hMarker, ?_, ?_⟩
  · intro s
    have heq := finite_deficit_eq_tv (p := p s) (q := q) ((hp s).2.1.trans hq.symm)
    have hzEq : (∑ x, |p s x-q x|) / 2 = ∑ j, z j := (hp s).2.2
    rw [← hzEq, ← heq, Fintype.sum_sum_type] at hdist
    simpa [hMarker] using hdist
  · exact (embedded_iid_mixture_tv_bound n E q z hEp hq hqn hz hEz).trans (paired_TV_constant hBudget)

end CanonneHeadEnvelope
