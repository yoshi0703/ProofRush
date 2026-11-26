import Model

namespace Canonne

open scoped BigOperators
noncomputable section

private theorem exists_retained_prefix {p : ℕ → ℝ} {u : ℝ}
    (hp : Law p) (hu : 0 < u) :
    ∃ k, 1 - u ≤ ∑ i ∈ Finset.range (k + 1), p i := by
  have h : ∀ᶠ n in Filter.atTop, 1 - u < ∑ i ∈ Finset.range n, p i :=
    hp.total.tendsto_sum_nat.eventually (lt_mem_nhds (sub_lt_self 1 hu))
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp h
  exact ⟨n, (hn (n + 1) (Nat.le_succ n)).le⟩

/-- The least index of a retained final coordinate, with the head at zero. -/
def cutIndex {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) : ℕ :=
  Nat.find (exists_retained_prefix hp hu)

theorem cutIndex_le_of_capture {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u)
    {k : ℕ} (h : 1 - u ≤ ∑ i ∈ Finset.range (k + 1), p i) :
    cutIndex hp hu ≤ k :=
  Nat.find_min' (exists_retained_prefix hp hu) h

theorem cutIndex_capture {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) :
    1 - u ≤ ∑ i ∈ Finset.range (cutIndex hp hu + 1), p i :=
  Nat.find_spec (exists_retained_prefix hp hu)

theorem cutIndex_minimal {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u)
    {j : ℕ} (hj : j < cutIndex hp hu) :
    (∑ i ∈ Finset.range (j + 1), p i) < 1 - u :=
  lt_of_not_ge (Nat.find_min (exists_retained_prefix hp hu) hj)

theorem cutIndex_isCut {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) :
    Cut p u (cutIndex hp hu) := by
  refine ⟨cutIndex_capture hp hu, ?_⟩
  cases h : cutIndex hp hu with
  | zero => exact Or.inl rfl
  | succ j =>
    exact Or.inr (cutIndex_minimal hp hu (h.symm ▸ Nat.lt_succ_self j))

/-- The prefix and discarded tail together have the full probability mass. -/
theorem discardedTail_eq {p : ℕ → ℝ} (hp : Law p) (k : ℕ) :
    (∑' i : ℕ, p (i + (k + 1))) = 1 - ∑ i ∈ Finset.range (k + 1), p i := by
  have h := hp.total.summable.sum_add_tsum_nat_add (k + 1)
  rw [hp.total.tsum_eq] at h
  linarith

/-- The same index is the least cutoff whose discarded tail has mass at most
    the radius. This is the tail convention in the original question. -/
theorem cutIndex_discardedTail {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) :
    (∑' i : ℕ, p (i + (cutIndex hp hu + 1))) ≤ u ∧
      ∀ j < cutIndex hp hu, u < ∑' i : ℕ, p (i + (j + 1)) := by
  constructor
  · rw [discardedTail_eq hp]
    linarith [cutIndex_capture hp hu]
  · intro j hj
    rw [discardedTail_eq hp]
    linarith [cutIndex_minimal hp hu hj]

/-- At a radius strictly below one, even the empty prefix is excluded by
    the original discarded-tail criterion. -/
theorem retainedLength_discardedTail {p : ℕ → ℝ} {u : ℝ} (hp : Law p)
    (hu : 0 < u) (hu' : u < 1) :
    let N := cutIndex hp hu + 1
    (∑' i : ℕ, p (i + N)) ≤ u ∧ ∀ j < N, u < ∑' i : ℕ, p (i + j) := by
  obtain ⟨atCutoff, belowCutoff⟩ := cutIndex_discardedTail hp hu
  refine ⟨atCutoff, ?_⟩
  intro j hj
  cases j with
  | zero => simpa only [Nat.add_zero, hp.total.tsum_eq] using hu'
  | succ j => exact belowCutoff j (Nat.lt_of_succ_lt_succ hj)

theorem cutIndex_antitone {p : ℕ → ℝ} {u v : ℝ} (hp : Law p)
    (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    cutIndex hp hv ≤ cutIndex hp hu :=
  cutIndex_le_of_capture hp hv
    (le_trans (sub_le_sub_left huv 1) (cutIndex_capture hp hu))

theorem phiAt_nonneg {p : ℕ → ℝ} (hp : Law p) (k : ℕ) : 0 ≤ phiAt p k := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hp.nonneg (i+1)) _

theorem phiAt_monotone {p : ℕ → ℝ} (hp : Law p) : Monotone (phiAt p) := by
  intro j k hjk
  unfold phiAt
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hp.nonneg (i+1)) _
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk)
      (fun i _ _ => Real.rpow_nonneg (hp.nonneg (i+1)) _)
  · norm_num

/-- The truncated quasinorm, with all of the retained cutoff coordinate
    included and the single largest atom removed. -/
def phi (p : ℕ → ℝ) (u : ℝ) (hp : Law p) (hu : 0 < u) : ℝ :=
  phiAt p (cutIndex hp hu)

theorem phi_nonneg {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : 0 < u) :
    0 ≤ phi p u hp hu :=
  phiAt_nonneg hp _

theorem phi_antitone {p : ℕ → ℝ} {u v : ℝ} (hp : Law p)
    (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    phi p v hp hv ≤ phi p u hp hu :=
  phiAt_monotone hp (cutIndex_antitone hp hu hv huv)


/-- At a positive target level, allowing the zero parameter in the inverse
    leaves the original strictly positive level set unchanged. -/
theorem inverseK_eq_positive_level {p : ℕ → ℝ} {u : ℝ} (hp : Law p) (hu : u < 1) :
    inverseK p u = sInf {t : ℝ | 0 < t ∧ 1 - u ≤ peetre p t} := by
  have hle (i : ℕ) : p i ≤ 1 := by
    rw [← hp.total.tsum_eq]
    exact hp.total.summable.le_tsum i (fun j _ => hp.nonneg j)
  have hs : Summable (fun i => p i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
      rw [pow_two]
      exact mul_le_of_le_one_right (hp.nonneg i) (hle i)) hp.total.summable
  have hzero : peetre p 0 ≤ 0 := by
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro t ⟨a, b, _, _, _, rfl⟩
      simp only [zero_mul, add_zero]
      exact tsum_nonneg fun i => abs_nonneg (a i)
    · exact ⟨fun _ => 0, p, by simp, by simp, hs, by simp⟩
  unfold inverseK
  congr 1
  ext t
  constructor
  · rintro ⟨ht, hcap⟩
    refine ⟨lt_of_le_of_ne ht ?_, hcap⟩
    intro heq
    subst t
    linarith
  · rintro ⟨ht, hcap⟩
    exact ⟨ht.le, hcap⟩

end

end Canonne
