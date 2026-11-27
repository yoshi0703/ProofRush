import HeadPrefixAdapter
import HeadProfileBridge
import Horizontal

namespace CanonneQuantile

open CanonneDiffuse CanonneNearOneTesting CanonneHeadEnvelope
open scoped BigOperators
noncomputable section

variable {T : Type*} [Fintype T] [DecidableEq T]

private def tailEmbedding (d : ℕ) : T ↪ (Fin (d+1) ⊕ T) :=
  ⟨Sum.inr, Sum.inr_injective⟩

private def offHeadEmbedding (d : ℕ) : Fin d ↪ (Fin (d+1) ⊕ T) :=
  ⟨fun i => Sum.inl i.succ, fun _ _ h => Fin.succ_injective _ (Sum.inl_injective h)⟩

def sumUpperTail (d : ℕ) : Finset (Fin (d+1) ⊕ T) :=
  Finset.univ.map (tailEmbedding d)

def sumUpperCut (d : ℕ) (K : Finset (Fin d)) : Finset (Fin (d+1) ⊕ T) :=
  K.map (offHeadEmbedding d)

def sumUpperCuts (d : ℕ) : Finset (Finset (Fin (d+1) ⊕ T)) :=
  (cutoffCandidates d).image (sumUpperCut d)

omit [Fintype T] in
theorem sumUpperCuts_nonempty (d : ℕ) :
    (sumUpperCuts (T := T) d).Nonempty :=
  (cutoffCandidates_nonempty d).image _

omit [DecidableEq T] in
@[simp] theorem mem_sumUpperTail_left (d : ℕ) (i : Fin (d+1)) :
    Sum.inl i ∉ sumUpperTail (T := T) d := by
  simp [sumUpperTail, tailEmbedding]

omit [DecidableEq T] in
@[simp] theorem mem_sumUpperTail_right (d : ℕ) (j : T) :
    Sum.inr j ∈ sumUpperTail (T := T) d := by
  simp [sumUpperTail, tailEmbedding]

theorem sum_upper_off_labels (d : ℕ) :
    (sumUpperTail (T := T) d)ᶜ.erase (Sum.inl 0) = sumUpperCut d Finset.univ := by
  ext a
  rcases a with i | j
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [sumUpperCut, offHeadEmbedding]
      intro x h
      change Sum.inl x.succ = Sum.inl 0 at h
      exact Fin.succ_ne_zero x (Sum.inl_injective h)
    · simp [sumUpperCut, offHeadEmbedding]
      exact ⟨k, rfl⟩
  · simp [sumUpperCut, offHeadEmbedding]

omit [DecidableEq T] in
theorem sum_upper_tail_mass {d : ℕ} (q : Fin (d+1) ⊕ T → ℝ) :
    mass q (sumUpperTail d) = ∑ j : T, q (Sum.inr j) := by
  simp [mass, sumUpperTail, tailEmbedding]

theorem sum_upper_tail_value {d : ℕ} (q : Fin (d+1) ⊕ T → ℝ) (n y : ℝ) :
    tail (tailMask (sumUpperTail d) q) n y = tail (fun j : T => q (Sum.inr j)) n y := by
  unfold tail
  rw [Fintype.sum_sum_type]
  simp [tailMask]

theorem sum_upper_tail_root {d : ℕ} {q : Fin (d+1) ⊕ T → ℝ}
    (hq : IsLaw q) {n : ℝ} (hn : 0 ≤ n) :
    root (tailMask (sumUpperTail d) q) (tailMask_nonneg _ hq) n hn =
      root (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg (Sum.inr j)) n hn := by
  let yl := root (tailMask (sumUpperTail d) q) (tailMask_nonneg _ hq) n hn
  let yr := root (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg (Sum.inr j)) n hn
  have hl : tail (tailMask (sumUpperTail d) q) n yl = yl :=
    (root_spec (tailMask (sumUpperTail d) q) (tailMask_nonneg _ hq) hn).2
  have hr : tail (fun j : T => q (Sum.inr j)) n yr = yr :=
    (root_spec (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg (Sum.inr j)) hn).2
  rw [sum_upper_tail_value] at hl
  have ant := tail_antitone (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg _) hn
  change yl = yr
  rcases le_total yl yr with h | h
  · have t := ant h
    rw [hl, hr] at t
    exact le_antisymm h t
  · have t := ant h
    rw [hl, hr] at t
    exact le_antisymm t h

private theorem cube_root_cube {x : ℝ} (hx : 0 ≤ x) :
    (x^(1/3 : ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx (1/3 : ℝ) 3]
  rw [show (1/3 : ℝ)*(3:ℕ)=1 by norm_num, Real.rpow_one]

theorem sum_upper_cut_cost {d : ℕ} (q : Fin (d+1) ⊕ T → ℝ)
    (hq : ∀ j, 0 ≤ q j) (K : Finset (Fin d)) (n : ℕ) :
    originalPrefixCost q (fun j => (q j)^(1/3 : ℝ))
        ((sumUpperTail d)ᶜ.erase (Sum.inl 0)) (sumUpperCut d K) n =
      cutCost (fun i : Fin d => (q (Sum.inl i.succ))^(1/3 : ℝ)) K (n : ℝ) := by
  unfold originalPrefixCost cutCost
  rw [sum_upper_off_labels]
  unfold sumUpperCut mass
  rw [← Finset.map_sdiff, Finset.sum_map, Finset.sum_map]
  simp only [Finset.compl_eq_univ_sdiff]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (cube_root_cube (hq _)).symm

theorem sum_upper_head_proxy {d : ℕ} (q : Fin (d+1) ⊕ T → ℝ)
    (hq : ∀ j, 0 ≤ q j) (n : ℕ) :
    canonicalHeadProxy q ((sumUpperTail d)ᶜ.erase (Sum.inl 0))
      (sumUpperCuts d) (sumUpperCuts_nonempty d) n =
      CanonneQuantile.headProfile (fun i : Fin d => (q (Sum.inl i.succ))^(1/3 : ℝ))
        (cutoffCandidates d) (cutoffCandidates_nonempty d) (n : ℝ) := by
  unfold canonicalHeadProxy originalHeadProxy
  let s := fun j => (q j)^(1/3 : ℝ)
  let c := fun R => originalPrefixCost q s ((sumUpperTail d)ᶜ.erase (Sum.inl 0)) R n
  calc
    _ = (cutoffCandidates d).inf' (cutoffCandidates_nonempty d) (c ∘ sumUpperCut d) :=
      (Finset.inf'_comp_eq_image (cutoffCandidates_nonempty d) c).symm
    _ = _ := by
      apply Finset.inf'_congr (cutoffCandidates_nonempty d) rfl
      intro R _
      exact sum_upper_cut_cost q hq R n

/-- Exact regular upper-branch interface on the same individual
cost and slack functions used in the horizontal theorem. -/
theorem regular_quantile_upper_sum {d : ℕ} (q : Fin (d+1) ⊕ T → ℝ) (hq : IsLaw q)
    (positive : ∀ i : Fin (d+1), 0 < q (Sum.inl i))
    {n : ℕ} (hn : 0 < n) {e : ℝ}
    (hwe : (∑ j : T, q (Sum.inr j)) ≤ e)
    (strong :
      let w := ∑ j : T, q (Sum.inr j)
      let s := fun i : Fin d => (q (Sum.inl i.succ))^(1/3 : ℝ)
      cost s (cutoffCandidates d) (cutoffCandidates_nonempty d) (w*(1-w)) (n : ℝ) ≤
        (1/4000000 : ℝ) *
          slack (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg (Sum.inr j))
            (e-w) (n : ℝ) (Nat.cast_nonneg n)) :
    ∃ j ≤ 3076*n, ∃ f, GoodTest q e j f := by
  let U := sumUpperTail (T := T) d
  let off := Uᶜ.erase (Sum.inl 0)
  let c := canonicalHeadProxy q off (sumUpperCuts d) (sumUpperCuts_nonempty d) n
  let w := ∑ j : T, q (Sum.inr j)
  let s := fun i : Fin d => (q (Sum.inl i.succ))^(1/3 : ℝ)
  have ww : mass q U = w := sum_upper_tail_mass q
  have hpos (a : Fin (d+1) ⊕ T) (ha : a ∈ off) : 0 < q a := by
    rcases a with i | j
    · exact positive i
    · exact False.elim ((Finset.mem_compl.mp (Finset.mem_erase.mp ha).2) (mem_sumUpperTail_right d j))
  have hv : 0 ≤ w*(1-w) := by
    rw [← ww]
    exact mul_nonneg (law_mass_bounds U hq).1 (sub_nonneg.mpr (law_mass_bounds U hq).2)
  have hp : c = CanonneQuantile.headProfile s (cutoffCandidates d)
      (cutoffCandidates_nonempty d) (n : ℝ) := sum_upper_head_proxy q hq.nonneg n
  have cost_eq : groupScale q U n/(n : ℝ)+c =
      cost s (cutoffCandidates d) (cutoffCandidates_nonempty d) (w*(1-w)) (n : ℝ) := by
    rw [groupScale_div q hq U hn, ww, Real.sqrt_div hv, hp]
    rfl
  have slack_eq : e-mass q U+(root (tailMask U q) (tailMask_nonneg U hq)
      (n : ℝ) (Nat.cast_nonneg n))^2 =
      slack (fun j : T => q (Sum.inr j)) (fun j => hq.nonneg (Sum.inr j))
        (e-w) (n : ℝ) (Nat.cast_nonneg n) := by
    rw [ww, sum_upper_tail_root hq (Nat.cast_nonneg n)]
    rfl
  have cutsSub (R : Finset (Fin (d+1) ⊕ T)) (hR : R ∈ sumUpperCuts d) : R ⊆ off := by
    obtain ⟨K, _, rfl⟩ := Finset.mem_image.mp hR
    change sumUpperCut d K ⊆ (sumUpperTail d)ᶜ.erase (Sum.inl 0)
    rw [sum_upper_off_labels]
    exact Finset.map_subset_map.mpr (Finset.subset_univ K)
  have strong' : 4000000*(groupScale q U n/(n : ℝ)+c) ≤
      e-mass q U+(root (tailMask U q) (tailMask_nonneg U hq)
        (n : ℝ) (Nat.cast_nonneg n))^2 := by
    rw [cost_eq, slack_eq]
    dsimp only at strong
    linarith
  exact regular_upper_at_canonical_prefix q hq U (mem_sumUpperTail_left d 0) hpos
    (sumUpperCuts d) (sumUpperCuts_nonempty d) cutsSub hn (ww ▸ hwe) strong'

end
end CanonneQuantile
