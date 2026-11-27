import SortedAlphabet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace CanonneHeadEnvelope

/-- A shortest qualifying sorted prefix, with the original finite alphabet kept intact. -/
structure CanonicalSplit {A : Type*} (q : A → ℝ) (ε : ℝ) where
  headPred : ℕ
  tailSize : ℕ
  label : Fin (headPred+1) ⊕ Fin tailSize ≃ A
  head_sorted : Antitone (fun i ↦ q (label (Sum.inl i)))
  tail_sorted : Antitone (fun i ↦ q (label (Sum.inr i)))
  tail_le_head : ∀ (i : Fin (headPred+1)) (j : Fin tailSize),
    q (label (Sum.inr j)) ≤ q (label (Sum.inl i))
  sufficient : 1-ε ≤ ∑ i : Fin (headPred+1), q (label (Sum.inl i))
  previous_short : (∑ i : Fin headPred, q (label (Sum.inl i.castSucc))) < 1-ε

variable {A : Type*} {q : A → ℝ} {ε : ℝ}

namespace CanonicalSplit

def head (s : CanonicalSplit q ε) (i : Fin (s.headPred+1)) : A := s.label (Sum.inl i)

def tail (s : CanonicalSplit q ε) (j : Fin s.tailSize) : A := s.label (Sum.inr j)

noncomputable def headMass (s : CanonicalSplit q ε) : ℝ := ∑ i, q (s.head i)

noncomputable def tailMass (s : CanonicalSplit q ε) : ℝ := ∑ j, q (s.tail j)

def largestLabel (s : CanonicalSplit q ε) : A := s.head 0

def thresholdLabel (s : CanonicalSplit q ε) : A := s.head (Fin.last s.headPred)

def thresholdAtom (s : CanonicalSplit q ε) : ℝ := q s.thresholdLabel

theorem threshold_le_head (s : CanonicalSplit q ε) (i : Fin (s.headPred+1)) :
    s.thresholdAtom ≤ q (s.head i) :=
  s.head_sorted (Fin.le_last i)

theorem tail_le_threshold (s : CanonicalSplit q ε) (i : Fin s.tailSize) :
    q (s.tail i) ≤ s.thresholdAtom :=
  s.tail_le_head (Fin.last _) i

theorem headMass_split (s : CanonicalSplit q ε) :
    s.headMass = (∑ i : Fin s.headPred, q (s.head i.castSucc)) + s.thresholdAtom :=
  Fin.sum_univ_castSucc (fun i ↦ q (s.head i))

theorem threshold_pos (s : CanonicalSplit q ε) : 0 < s.thresholdAtom := by
  have hp := s.previous_short
  have hs : 1-ε ≤ s.headMass := s.sufficient
  rw [headMass_split] at hs
  change (∑ i : Fin s.headPred, q (s.head i.castSucc)) < 1-ε at hp
  linarith

theorem head_pos (s : CanonicalSplit q ε) (i : Fin (s.headPred+1)) :
    0 < q (s.head i) := s.threshold_pos.trans_le (s.threshold_le_head i)

theorem shorter_prefix_insufficient (s : CanonicalSplit q ε) {k : ℕ} (hk : k ≤ s.headPred) :
    (∑ i : Fin k, q (s.head ((Fin.castLE hk i).castSucc))) < 1-ε := by
  let e := Fin.castLEEmb hk
  let g : Fin s.headPred → ℝ := fun i ↦ q (s.head i.castSucc)
  have hnon : ∀ i, 0 ≤ g i := fun i ↦ (s.head_pos i.castSucc).le
  have hsub : (∑ i : Fin k, g (e i)) ≤ ∑ i, g i := by
    rw [← Finset.sum_map]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ ↦ hnon i)
  exact hsub.trans_lt s.previous_short

theorem headMass_tailMass [Fintype A] (s : CanonicalSplit q ε) :
    s.headMass + s.tailMass = ∑ a, q a := by
  have hs := s.label.sum_comp q
  rw [Fintype.sum_sum_type] at hs
  exact hs

theorem tailMass_le [Fintype A] (s : CanonicalSplit q ε) (hq : ∑ a, q a = 1) :
    s.tailMass ≤ ε := by
  have hsum := s.headMass_tailMass.trans hq
  have hs : 1-ε ≤ s.headMass := s.sufficient
  linarith

theorem gap_lt_threshold [Fintype A] (s : CanonicalSplit q ε) (hq : ∑ a, q a = 1) :
    ε - s.tailMass < s.thresholdAtom := by
  have ht := s.headMass_tailMass.trans hq
  have hp := s.previous_short
  rw [headMass_split] at ht
  change (∑ i : Fin s.headPred, q (s.head i.castSucc)) < 1-ε at hp
  linarith

section LabelSets

variable [DecidableEq A]

def headSet (s : CanonicalSplit q ε) : Finset A := Finset.univ.image s.head

def tailSet (s : CanonicalSplit q ε) : Finset A := Finset.univ.image s.tail

def offmaxHeadSet (s : CanonicalSplit q ε) : Finset A :=
  Finset.univ.image (fun i : Fin s.headPred ↦ s.head i.succ)

theorem largest_not_tailSet (s : CanonicalSplit q ε) : s.largestLabel ∉ s.tailSet := by
  intro h
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
  have he : (Sum.inr j : Fin (s.headPred+1) ⊕ Fin s.tailSize) = Sum.inl 0 :=
    s.label.injective hj
  cases he

theorem complement_tailSet [Fintype A] (s : CanonicalSplit q ε) :
    s.tailSetᶜ = s.headSet := by
  ext a
  obtain ⟨i,rfl⟩ := s.label.surjective a
  cases i with
  | inl i =>
    have h : s.label (Sum.inl i) ∉ s.tailSet := by
      rintro ha
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ha
      have he := s.label.injective hj
      cases he
    simp only [Finset.mem_compl, h, not_false_eq_true, true_iff]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  | inr j =>
    have h : s.label (Sum.inr j) ∈ s.tailSet := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    simp only [Finset.mem_compl, h, not_true_eq_false, false_iff]
    rintro ha
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ha
    have he := s.label.injective hi
    cases he

theorem offmaxHeadSet_eq [Fintype A] (s : CanonicalSplit q ε) :
    s.tailSetᶜ.erase s.largestLabel = s.offmaxHeadSet := by
  rw [complement_tailSet]
  ext a
  constructor
  · intro ha
    obtain ⟨hneq,hmem⟩ := Finset.mem_erase.mp ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hmem
    cases i using Fin.cases with
    | zero => exact (hneq rfl).elim
    | succ i => exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,rfl⟩⟩
    intro he
    have h := Sum.inl.inj (s.label.injective he)
    exact Fin.succ_ne_zero i h

theorem tailMass_eq_tailSet (s : CanonicalSplit q ε) :
    (∑ a ∈ s.tailSet, q a) = s.tailMass :=
  Finset.sum_image (fun _ _ _ _ h ↦ Sum.inr.inj (s.label.injective h))

theorem tailSet_le_threshold (s : CanonicalSplit q ε) {a : A} (ha : a ∈ s.tailSet) :
    q a ≤ s.thresholdAtom := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
  exact s.tail_le_threshold j

theorem threshold_le_headSet [Fintype A] (s : CanonicalSplit q ε) {a : A} (ha : a ∉ s.tailSet) :
    s.thresholdAtom ≤ q a := by
  have he : a ∈ s.headSet := s.complement_tailSet ▸ Finset.mem_compl.mpr ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  exact s.threshold_le_head i

theorem zero_mem_tailSet [Fintype A] (s : CanonicalSplit q ε) {a : A} (ha : q a = 0) :
    a ∈ s.tailSet := by
  by_contra h
  have he : a ∈ s.headSet := s.complement_tailSet ▸ Finset.mem_compl.mpr h
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  exact (s.head_pos i).ne' ha

noncomputable def offmaxHeadEquiv [Fintype A] (s : CanonicalSplit q ε) :
    Fin s.headPred ≃ {a : A // a ∈ s.tailSetᶜ.erase s.largestLabel} := by
  let f (i : Fin s.headPred) : {a : A // a ∈ s.tailSetᶜ.erase s.largestLabel} :=
    ⟨s.head i.succ,by
      rw [s.offmaxHeadSet_eq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro i j h
    have h' := Sum.inl.inj (s.label.injective (congrArg Subtype.val h))
    exact Fin.succ_inj.mp h'
  · rintro ⟨a,ha⟩
    rw [s.offmaxHeadSet_eq] at ha
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨j,rfl⟩

@[simp] theorem offmaxHeadEquiv_val [Fintype A] (s : CanonicalSplit q ε) (i : Fin s.headPred) :
    (s.offmaxHeadEquiv i).val = s.head i.succ := rfl

noncomputable def tailEquiv (s : CanonicalSplit q ε) :
    Fin s.tailSize ≃ {a : A // a ∈ s.tailSet} := by
  let f (j : Fin s.tailSize) : {a : A // a ∈ s.tailSet} :=
    ⟨s.tail j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro i j h
    exact Sum.inr.inj (s.label.injective (congrArg Subtype.val h))
  · rintro ⟨a,ha⟩
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨j,rfl⟩

@[simp] theorem tailEquiv_val (s : CanonicalSplit q ε) (j : Fin s.tailSize) :
    (s.tailEquiv j).val = s.tail j := rfl

end LabelSets

end CanonicalSplit

private noncomputable def prefixMass {N : ℕ} (g : Fin N → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N ↦ i.val < k), g i

private theorem prefixMass_eq_castLE {N k : ℕ} (g : Fin N → ℝ) (hk : k ≤ N) :
    prefixMass g k = ∑ i : Fin k, g (Fin.castLE hk i) := by
  let e := Fin.castLEEmb hk
  have hs : Finset.univ.map e = Finset.univ.filter (fun i : Fin N ↦ i.val < k) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j,rfl⟩
      exact j.isLt
    · intro hi
      exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
  unfold prefixMass
  rw [← hs, Finset.sum_map]
  rfl

/-- Construct the shortest sorted prefix with mass at least (1-ε), retaining declared zeros. -/
theorem exists_canonical_split [Fintype A] (q : A → ℝ) (hq : ∑ a, q a = 1)
    {ε : ℝ} (he₀ : 0 ≤ ε) (he₁ : ε < 1) : Nonempty (CanonicalSplit q ε) := by
  classical
  obtain ⟨order,horder⟩ := exists_sorted_equiv q
  let N := Fintype.card A
  let g : Fin N → ℝ := fun i ↦ q (order i)
  have htotal : prefixMass g N = 1 := by
    rw [prefixMass_eq_castLE g le_rfl]
    exact (order.sum_comp q).trans hq
  have hex : ∃ k, 1-ε ≤ prefixMass g k := ⟨N,by rw [htotal]; linarith⟩
  let k := Nat.find hex
  have hk : 1-ε ≤ prefixMass g k := Nat.find_spec hex
  have hkN : k ≤ N := Nat.find_min' hex (by rw [htotal]; linarith)
  have hkPos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz] at hk
    simp [prefixMass] at hk
    linarith
  let d := k-1
  let t := N-k
  have hdk : d+1 = k := by omega
  have hdN : d ≤ N := by omega
  have hdkN : d+1 ≤ N := by omega
  have hLen : (d+1)+t=N := by omega
  let F : Fin (d+1) ⊕ Fin t ≃ Fin N := finSumFinEquiv.trans (finCongr hLen)
  let L : Fin (d+1) ⊕ Fin t ≃ A := F.trans order
  refine ⟨⟨d,t,L,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    apply horder
    exact hij
  · intro i j hij
    apply horder
    change d+1+i.val ≤ d+1+j.val
    exact Nat.add_le_add_left hij _
  · intro i j
    apply horder
    change i.val ≤ d+1+j.val
    have := i.isLt
    omega
  · rw [← hdk, prefixMass_eq_castLE g hdkN] at hk
    exact hk
  · have hd : d < k := by omega
    have hprev : prefixMass g d < 1-ε := lt_of_not_ge (Nat.find_min hex hd)
    rw [prefixMass_eq_castLE g hdN] at hprev
    exact hprev

end CanonneHeadEnvelope
