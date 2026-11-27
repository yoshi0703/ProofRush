import AdjacentPairs
import PairedLowerBound

open scoped BigOperators

namespace CanonneHeadEnvelope

def cutoffPrefix (d j : ℕ) : Finset (Fin d) := Finset.univ.filter (fun i ↦ i.val < j)

theorem active_is_prefix {d : ℕ} (a : Fin d → ℝ) (ha : Antitone a) (l : ℝ) :
    ∃ j ≤ d, Finset.univ.filter (fun i ↦ l < a i) = cutoffPrefix d j := by
  let T : Finset (Fin d) := Finset.univ.filter (fun i ↦ a i ≤ l)
  by_cases ht : T.Nonempty
  · let j := T.min' ht
    have hj : a j ≤ l := (Finset.mem_filter.mp (Finset.min'_mem _ ht)).2
    refine ⟨j.val,j.isLt.le,?_⟩
    ext i
    simp only [cutoffPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      by_contra hn
      exact (not_lt_of_ge ((ha (show j ≤ i from Nat.le_of_not_gt hn)).trans hj)) hi
    · intro hi
      by_contra hn
      have hTi : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hn⟩
      exact (Nat.not_le_of_gt hi) (Finset.min'_le T i hTi)
  · refine ⟨d,le_rfl,?_⟩
    ext i
    simp only [cutoffPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ ↦ i.isLt, fun _ ↦ lt_of_not_ge
      (fun hi ↦ ht ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)⟩

noncomputable def headCutoff (n d j : ℕ) (a : Fin (d+1) → ℝ) : ℝ :=
  cutoffCost Finset.univ (cutoffPrefix d j) (fun i ↦ a i.succ) (1 / (n : ℝ)^2)

private theorem point_coefficient_bound (n : ℕ) (v L R : ℝ) (hR : 0 < R) (hRL : R ≤ L) :
    ((n : ℝ) * (v^2 * (1/L + 1/R)))^2 / 2 ≤
      2 * (n : ℝ)^2 * (v^4 / R^2) := by
  have hL : 0 < L := hR.trans_le hRL
  have hi := one_div_le_one_div_of_le hR hRL
  have hs : v^2 * (1/L + 1/R) ≤ v^2 * (2/R) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [show 2/R = 1/R + 1/R by ring]
  have h0 : 0 ≤ (n : ℝ) * (v^2 * (1/L+1/R)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  calc
    _ ≤ ((n : ℝ) * (v^2 * (2/R)))^2 / 2 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 hm 2) (by norm_num)
    _ = _ := by ring

theorem exists_head_paired_shift (n d : ℕ) (a : Fin (d+1) → ℝ) (hn : 0 < n)
    (ha : ∀ i, 0 < a i) (ho : Antitone a) {ε : ℝ}
    (hfar : ∀ j ≤ d, 32 * ε < headCutoff n d j a) :
    let E := adjacentEmbedding d
    let q := fun i ↦ (a i)^3
    ∃ z : Fin ((d+1)/2) → ℝ,
      (∀ j, 0 ≤ z j) ∧
      (∀ p : Fin ((d+1)/2) × Bool, z p.1 ≤ q (E p)) ∧
      ε < (∑ i, z i) ∧
      ∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2 ≤ 1/2048 := by
  let b := 1 / (n : ℝ)^2
  let a' : Fin d → ℝ := fun i ↦ a i.succ
  obtain ⟨l,hl,hb,_,R,_,hR₀,hR⟩ := exists_clamped_cutoff
    (Finset.univ : Finset (Fin d)) a' (fun i _ ↦ ha i.succ) (b := b) (by positivity)
  let c := clamp a l
  let E := adjacentEmbedding d
  let z := fun j : Fin ((d+1)/2) ↦ c (E (j,true)) / 8
  let q : Fin (d+1) → ℝ := fun i ↦ (a i)^3
  have haq : ∀ i, 0 < q i := fun i ↦ pow_pos (ha i) _
  have hc : ∀ i, 0 ≤ c i := fun i ↦ clamp_nonnegative (ha i).le hl
  have hAnt : Antitone c := clamp_antitone (fun i ↦ (ha i).le) ho hl
  have hcl : ∀ i, c i ≤ q i := fun _ ↦ min_le_left _ _
  have hsorted : Antitone q := fun i j hij ↦ pow_le_pow_left₀ (ha j).le (ho hij) 3
  have hpair (j : Fin ((d+1)/2)) : q (E (j,true)) ≤ q (E (j,false)) :=
    hsorted (adjacentEmbedding_left_le_right d j)
  have hz (i : Fin ((d+1)/2)) : 0 ≤ z i := div_nonneg (hc _) (by norm_num)
  have hzq (i : Fin ((d+1)/2) × Bool) : z i.1 ≤ q (E i) := by
    obtain ⟨j,s⟩ := i
    have hh : z j ≤ q (E (j,true)) := by
      dsimp [z]
      linarith [hc (E (j,true)), hcl (E (j,true))]
    cases s
    · exact hh.trans (hpair j)
    · exact hh
  have hj : ∃ j ≤ d, R = cutoffPrefix d j := by
    rcases hR₀ with hR₀ | hR₁
    · exact ⟨0,Nat.zero_le _,by simp [hR₀,cutoffPrefix]⟩
    · have ha' : Antitone a' := fun i j hij ↦ ho (Fin.succ_le_succ_iff.mpr hij)
      obtain ⟨j,hj,he⟩ := active_is_prefix a' ha' l
      exact ⟨j,hj,hR₁.trans he⟩
  obtain ⟨j,hj,hRj⟩ := hj
  have hstrict : ε < ∑ i, z i := by
    have hs := adjacent_right_recovers_half hc hAnt
    change (∑ i : Fin d, c i.succ) ≤ 2 * ∑ j : Fin ((d+1)/2), c (E (j,true)) at hs
    have hcost : 32 * ε < cutoffCost Finset.univ R a' b := by rw [hRj]; exact hfar j hj
    have ht : ∑ i, z i = (∑ i : Fin ((d+1)/2), c (E (i,true))) / 8 := by
      simp only [z, div_eq_mul_inv, Finset.sum_mul]
    change cutoffCost Finset.univ R a' b ≤ 2 * ∑ i : Fin d, c i.succ at hR
    linarith
  have hbudget : ∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2 ≤ 1/2048 := by
    have hOne : ∀ j : Fin ((d+1)/2),
        ((n : ℝ) * pairCoefficient (q ∘ E) z j)^2 / 2 ≤
          ((n : ℝ)^2 / 2048) * ((clamp a' l (rightOffset d j))^4 / (a' (rightOffset d j))^6) := by
      intro j
      calc
        _ ≤ 2 * (n : ℝ)^2 * ((z j)^4 / (q (E (j,true)))^2) :=
          point_coefficient_bound n (z j) _ _ (haq _) (hpair j)
        _ = _ := by
          rw [show q (E (j,true)) = (a' (rightOffset d j))^3 from
            congrArg q (adjacentEmbedding_right d j)]
          rw [show z j = clamp a' l (rightOffset d j) / 8 from rfl]
          ring
    have hN : 0 ≤ (n : ℝ)^2 / 2048 := by positivity
    calc
      _ ≤ ∑ i, ((n : ℝ)^2 / 2048) * ((clamp a' l (rightOffset d i))^4 / (a' (rightOffset d i))^6) :=
        Finset.sum_le_sum fun i _ ↦ hOne i
      _ ≤ ((n : ℝ)^2 / 2048) * quarticBudget Finset.univ a' (clamp a' l) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (adjacent_right_sum_le (fun i ↦
          div_nonneg (by positivity) (pow_nonneg (ha i.succ).le _))) hN
      _ ≤ ((n : ℝ)^2 / 2048) * b := mul_le_mul_of_nonneg_left hb hN
      _ = _ := by
        have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
        dsimp [b]
        field_simp
  exact ⟨z,hz,hzq,hstrict,hbudget⟩

/-- For a positive sorted finite reference whose probabilities are the cubes of (a_i),
the deterministic minimum cutoff yields a strict-radius iid lower bound at error (1/3).
The sample and shift parameters use the actual distribution, allowing an arbitrary further
unchanged label through the more general `embedded_iid_no_test`. -/
theorem head_cutoff_no_test (n d : ℕ) (a : Fin (d+1) → ℝ) (hn : 0 < n)
    (ha : ∀ i, 0 < a i) (ho : Antitone a) (hq : ∑ i, (a i)^3 = 1)
    {ε : ℝ} (hfar : ∀ j ≤ d, 32 * ε < headCutoff n d j a) :
    let q := fun i ↦ (a i)^3
    ¬ ∃ f : (Fin n → Fin (d+1)) → ℝ,
      (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∑ x, iidMass n q x * f x) ≤ 1/3 ∧
      ∀ p : Fin (d+1) → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i) = 1 →
        ε < (∑ i, |p i - q i|) / 2 →
        1 - 1/3 ≤ ∑ x, iidMass n p x * f x := by
  let E := adjacentEmbedding d
  let q := fun i ↦ (a i)^3
  have haq : ∀ i, 0 < q i := fun i ↦ pow_pos (ha i) _
  obtain ⟨z,hz,hzq,hstrict,hbudget⟩ := exists_head_paired_shift n d a hn ha ho hfar
  have hgap : (1 : ℝ)/3 + 1/3 +
      Real.sqrt (Real.exp (∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2) - 1) / 2 < 1 := by
    have hExp : Real.exp (∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2) ≤
        1 / (1 - (1 : ℝ)/2048) :=
      (Real.exp_le_exp.mpr hbudget).trans (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num))
    have hSqrt : Real.sqrt (Real.exp (∑ i, ((n : ℝ) * pairCoefficient (q ∘ E) z i)^2 / 2)-1) ≤ 1/2 := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> linarith
    linarith
  exact embedded_iid_no_test n E q z (fun i ↦ haq _) hq (fun i ↦ (haq i).le)
    hz hzq hstrict hgap

end CanonneHeadEnvelope
