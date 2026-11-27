import RegularBaseline
import RegularHeadPrior

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneNearOneTesting CanonneHeadEnvelope
open CanonneQuantile
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- A stochastic channel even if the declared tail is empty. This branch
is used when the reference and all paired alternatives give their marker
zero mass. Its behavior at the impossible marker has no effect. -/
def zeroTailChannel (q : H ⊕ T → ℝ) : H ⊕ Unit → H ⊕ T → ℝ
  | Sum.inl h => pointLaw (Sum.inl h)
  | Sum.inr _ => q

theorem zeroTailChannel_isLaw {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (v : H ⊕ Unit) : IsLaw (zeroTailChannel q v) := by
  cases v with
  | inl h => exact pointLaw_isLaw (Sum.inl h)
  | inr u => exact hq

omit [Fintype T] in
theorem zero_tail_channel_head (q : H ⊕ T → ℝ) (p : H ⊕ Unit → ℝ)
    (hp : p (Sum.inr ()) = 0) (h : H) :
    mixLaw p (zeroTailChannel q) (Sum.inl h) = p (Sum.inl h) := by
  simp [mixLaw, zeroTailChannel, pointLaw, hp, Fintype.sum_sum_type]

omit [Fintype T] in
theorem zero_tail_channel_tail (q : H ⊕ T → ℝ) (p : H ⊕ Unit → ℝ)
    (hp : p (Sum.inr ()) = 0) (t : T) :
    mixLaw p (zeroTailChannel q) (Sum.inr t) = 0 := by
  simp [mixLaw, zeroTailChannel, pointLaw, hp, Fintype.sum_sum_type]

/-- A zero-tail reference may use a head prior with unchanged zero marker
mass. Its positive-weight components transfer at no additional TV cost. -/
theorem no_good_test_of_zero_tail_prior {I : Type*} [Fintype I] {n : ℕ}
    {q : H ⊕ T → ℝ} (hq : IsLaw q) (hw : (∑ t : T, q (Sum.inr t)) = 0)
    {e : ℝ} {weights : I → ℝ} (hweights : IsLaw weights) {alts : I → H ⊕ Unit → ℝ}
    (halts : ∀ i, IsLaw (alts i)) (hmarker : ∀ i, alts i (Sum.inr ()) = 0)
    (hdef : ∀ i, 0 < weights i → e < trueHeadDeficit q (alts i))
    (hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ 1/8) :
    ¬ ∃ f, GoodTest q e n f := by
  let tape : Unit → ℝ := fun _ => 1
  let K : Unit → (H ⊕ Unit) → H ⊕ T → ℝ := fun _ => zeroTailChannel q
  have htape : IsLaw tape := ⟨fun _ => by norm_num [tape], by simp [tape]⟩
  have hK : ∀ z v, IsLaw (K z v) := fun _ v => zeroTailChannel_isLaw hq v
  have hzero (t : T) : q (Sum.inr t) = 0 := by
    have h := Finset.single_le_sum (f := fun t : T => q (Sum.inr t))
      (fun _ _ => hq.nonneg _) (Finset.mem_univ t)
    rw [hw] at h
    exact h.antisymm (hq.nonneg _)
  have hmarkQ : collapsed q (Sum.inr ()) = 0 := hw
  have heq : mixLaw (collapsed q) (zeroTailChannel q) = q := by
    funext a
    cases a with
    | inl h => exact zero_tail_channel_head q (collapsed q) hmarkQ h
    | inr t => rw [zero_tail_channel_tail q (collapsed q) hmarkQ, hzero]
  have hnull : totalVariation
      (mixLaw tape (fun z => pilotLaw (I := Fin n) (mixLaw (collapsed q) (K z))))
      (pilotLaw q) ≤ 0 := by
    have hpredict : mixLaw tape (fun z => pilotLaw (I := Fin n) (mixLaw (collapsed q) (K z))) =
        pilotLaw q := by
      funext y
      simp [mixLaw, K, tape, heq]
    rw [hpredict]
    simp [totalVariation]
  apply no_good_test_of_common_channel hq (collapsed_isLaw hq) hweights halts htape hK
    (by norm_num) hnull hprior
  intro i z hi _
  let p := mixLaw (alts i) (K z)
  have hp : IsLaw p := mixLaw_isLaw (halts i) (K z) (hK z)
  have hhead (h : H) : p (Sum.inl h) = alts i (Sum.inl h) :=
    zero_tail_channel_head q (alts i) (hmarker i) h
  have htail (t : T) : p (Sum.inr t) = 0 :=
    zero_tail_channel_tail q (alts i) (hmarker i) t
  change e < totalVariation p q
  rw [totalVariation_eq_deficit hp hq]
  unfold deficit
  rw [Fintype.sum_sum_type]
  simp only [hhead, htail, hzero, sub_zero, max_self, Finset.sum_const_zero, add_zero]
  exact hdef i hi

/-- The signed, paired head prior and tail transfer together force the exact
head-cost inequality at the reverse scale, including zero marker mass. -/
theorem head_profile_necessary_at_regular_scale
    {d n : ℕ} (order : Fin (d+1) ≃ H) (hn : 0 < n)
    {q : H ⊕ T → ℝ} (hq : IsLaw q) (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i => q (Sum.inl (order i))))
    {e x : ℝ} (hx : 0 < x) (hfloor : 8 ≤ (n:ℝ)*x)
    (hroot : 64*root (fun t : T => q (Sum.inr t))
      (fun t => hq.nonneg (Sum.inr t)) (n:ℝ) (Nat.cast_nonneg n) ≤ Real.sqrt x)
    (htest : ∃ f, GoodTest q e n f) :
    headMass q * headProfile ((n:ℝ)*headMass q) (orderedConditional order q) ≤
      32*(e-(∑ t : T, q (Sum.inr t))+x) := by
  by_contra hb
  have hfar := lt_of_not_ge hb
  obtain ⟨weights, alts, hweights, halts, hmarker, hdef, hprior⟩ :=
    exists_regular_head_prior order hq hn hpos horder hfar
  have hw0 : 0 ≤ (∑ t : T, q (Sum.inr t)) := Finset.sum_nonneg fun t _ => hq.nonneg _
  by_cases hw : (∑ t : T, q (Sum.inr t)) = 0
  · apply no_good_test_of_zero_tail_prior hq hw hweights halts _ _ hprior htest
    · intro i
      rw [hmarker i]
      exact hw
    · intro i _
      have h := hdef i
      rw [hw] at h
      linarith
  · exact no_good_test_at_regular_scale hn hq (lt_of_le_of_ne hw0 (Ne.symm hw)) hx
      hfloor hroot hweights halts (fun i _ => hdef i) hprior htest

omit [DecidableEq H] [DecidableEq T] in
theorem reverse_tolerance_ready {n : ℕ} (hn : 0 < n) {q : H ⊕ T → ℝ}
    (hq : IsLaw q) :
    let x := reverseTolerance q hq n
    0 < x ∧ 8 ≤ (n:ℝ)*x ∧
      64*root (fun t : T => q (Sum.inr t)) (fun t => hq.nonneg (Sum.inr t))
        (n:ℝ) (Nat.cast_nonneg n) ≤ Real.sqrt x := by
  dsimp only
  let R := root (fun t : T => q (Sum.inr t)) (fun t => hq.nonneg (Sum.inr t)) n (Nat.cast_nonneg n)
  let x := reverseTolerance q hq n
  change 0 < x ∧ 8 ≤ (n:ℝ)*x ∧ 64*R ≤ Real.sqrt x
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hxN : 4096*(1/(n:ℝ)) ≤ x :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  have hx : 0 < x := (by positivity : 0 < 4096*(1/(n:ℝ))).trans_le hxN
  refine ⟨hx, ?_, ?_⟩
  · have heq : (n:ℝ)*(4096*(1/(n:ℝ))) = 4096 := by field_simp [hnR.ne']
    nlinarith only [heq, mul_le_mul_of_nonneg_left hxN hnR.le]
  · have hR : 0 ≤ R := (root_spec (fun t : T => q (Sum.inr t))
      (fun t => hq.nonneg (Sum.inr t)) (Nat.cast_nonneg n)).1
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) hR) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hx.le, show (64*R)^2 = 4096*R^2 by ring]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)

/-- The complete weak crossing inequality for a positive sorted head.
The prior, pilot bins and amplification are internal to the proof. -/
theorem weak_crossing_for_sorted_head
    {d : ℕ} (order : Fin (d+1) ≃ H) {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i => q (Sum.inl (order i))))
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hwe : (∑ t : T, q (Sum.inr t)) ≤ e)
    (hreg : CanonneNearOne.nearOneMoment q (1-e) ≤ 32*(1-e))
    (hnonempty : ∃ p : H ⊕ T → ℝ, IsLaw p ∧ e < totalVariation p q)
    {m : ℕ} (htest : ∃ f, GoodTest q e m f) :
    let n := amplifiedBudget m
    let w := ∑ t : T, q (Sum.inr t)
    let X := tailOverlapSquare q hq n
    let head := headMass q * headProfile ((n:ℝ)*headMass q) (orderedConditional order q)
    Real.sqrt (w*(1-w)/(n:ℝ)) + 1/(n:ℝ) + head ≤ 163881*(e-w+X) := by
  let n := amplifiedBudget m
  let cost := headMass q * headProfile ((n:ℝ)*headMass q) (orderedConditional order q)
  have hm : 0 < m := (testing_baseline_budgets hq he he1 hreg hnonempty htest).1
  have hn : 0 < n := Nat.mul_pos (by decide) hm
  obtain ⟨hx, hnx, hroot⟩ := reverse_tolerance_ready hn hq
  have hhead : ∀ (_ : ∃ f, GoodTest q e n f),
      cost ≤ 32*(e-(∑ t : T, q (Sum.inr t))+reverseTolerance q hq n) :=
    fun h => head_profile_necessary_at_regular_scale order hn hq hpos horder hx hnx hroot h
  have h := weak_crossing_at_fixed_amplification hq he he1 hwe hreg hnonempty htest
    (CH := 32) (cost := cost) (by norm_num) hhead
  change _ ≤ ((8+(32:ℝ))*4097+1)*_ at h
  norm_num only [show ((8+(32:ℝ))*4097+1) = 163881 by norm_num] at h
  exact h

end
end CanonneRegularTransfer
