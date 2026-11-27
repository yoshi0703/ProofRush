import CountableBridge

namespace CanonneCountable

open Filter
open scoped Topology BigOperators
noncomputable section

private theorem sum_project_nonnegative {A B : Type*} [Fintype B] [DecidableEq B]
    {p : A → ℝ} (hp : Summable p) (hnp : ∀ a, 0 ≤ p a) (g : A → B) :
    (∑ b, project g p b) = ∑' a, p a := by
  have hs (b : B) : Summable (fun a => if g a = b then p a else 0) := by
    apply hp.of_nonneg_of_le
    · intro a
      split <;> first | exact hnp _ | exact le_rfl
    · intro a
      split <;> first | exact hnp _ | exact le_rfl
  unfold project
  rw [← Summable.tsum_finsetSum (fun b _ => hs b)]
  apply tsum_congr
  intro a
  rw [Finset.sum_eq_single (g a)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

private theorem prefix_total_split {p : ℕ → ℝ} (hp : Summable p) (hnp : ∀ a, 0 ≤ p a)
    (m : ℕ) :
    project (prefixMap m) p none + ∑ a ∈ Finset.range m, p a = ∑' a, p a := by
  have h := sum_project_nonnegative hp hnp (prefixMap m)
  rw [Fintype.sum_option] at h
  simp only [prefix_project_some] at h
  rw [Fin.sum_univ_eq_sum_range p m] at h
  exact h

/-- Pooling the entire tail at one label loses at most the reference's
tail mass in TV, uniformly over the arbitrary alternative law. -/
theorem tv_le_prefix_tv_add_null_tail {p q : ℕ → ℝ} (hp : Law p) (hq : Law q) (m : ℕ) :
    tv p q ≤ tv (project (prefixMap m) p) (project (prefixMap m) q) +
      project (prefixMap m) q none := by
  let f (a : ℕ) := |p a-q a|
  let g := prefixMap m
  have hps := fiber_summable hp g none
  have hqs := fiber_summable hq g none
  have hfs (a : ℕ) : 0 ≤ f a := abs_nonneg _
  have hfm := sum_diff_abs_summable hp hq
  have hft : Summable (fun a => if g a = none then f a else 0) := by
    apply hfm.of_nonneg_of_le
    · intro a
      split <;> first | exact hfs a | exact le_rfl
    · intro a
      split <;> first | exact hfs a | exact le_rfl
  have hsplit := prefix_total_split hfm hfs m
  have htail :
      project g f none ≤ project g p none + project g q none := by
    unfold project
    rw [← hps.tsum_add hqs]
    apply hft.tsum_le_tsum _ (hps.add hqs)
    intro a
    by_cases ha : g a = none
    · simp only [ha, ite_true]
      exact abs_le.mpr ⟨by linarith [hp.nonneg a], by linarith [hq.nonneg a]⟩
    · simp only [ha, ite_false, add_zero, le_refl]
  have hfinite_tv :
      tv (project g p) (project g q) =
        (|project g p none - project g q none| + ∑ a ∈ Finset.range m, f a)/2 := by
    rw [tv, tsum_fintype, Fintype.sum_option]
    simp only [g, prefix_project_some]
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => |p a-q a|) m]
  rw [tv, hfinite_tv]
  change project g f none + (∑ a ∈ Finset.range m, f a) = _ at hsplit
  change (∑' a, f a)/2 ≤ _
  linarith [le_abs_self (project g p none - project g q none)]

/-- The reference tail cell tends to zero along longer prefixes. -/
theorem tail_mass_tendsto_zero {q : ℕ → ℝ} (hq : Law q) :
    Tendsto (fun m => project (prefixMap m) q none) atTop (𝓝 0) := by
  have he (m : ℕ) : project (prefixMap m) q none = 1 - ∑ a ∈ Finset.range m, q a := by
    have h := prefix_total_split hq.summable hq.nonneg m
    rw [hq.total] at h
    linarith
  simp only [he]
  simpa only [sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hq.hasSumOne.tendsto_sum_nat

/-- Existence of a finite fixed-budget test at an arbitrary positive
strict radius, given finite tests at half the radius for the prefixes.
The comparison radius for the fixed-budget equivalence itself is unchanged. -/
theorem good_test_exists_of_finite_half_radius {q : ℕ → ℝ} (hq : Law q) {e : ℝ}
    (he : 0 < e)
    (hfinite : ∀ m, ∃ n f, CanonneNearOneTesting.GoodTest (project (prefixMap m) q) (e/2) n f) :
    ∃ n f, GoodTest q e n f := by
  have he2 : 0 < e/2 := by positivity
  obtain ⟨m, hsmall⟩ := ((tendsto_order.1 (tail_mass_tendsto_zero hq)).2 _ he2).exists
  obtain ⟨n,v,hv⟩ := hfinite m
  obtain ⟨f,hf⟩ := finite_good_test_iff.mpr ⟨v,hv⟩
  let full (z : Fin n → ℕ) := f (prefixMap m ∘ z)
  refine ⟨n, full, ?_, ?_⟩
  · unfold full
    rw [← expectation_projected_records hq (prefixMap m) n (fun y => (f y : ℝ))]
    exact hf.1
  · intro p hp hfar
    have htv := tv_le_prefix_tv_add_null_tail hp hq m
    have hdist : e/2 < tv (project (prefixMap m) p) (project (prefixMap m) q) := by linarith
    unfold full
    rw [← expectation_projected_records hp (prefixMap m) n (fun y => (f y : ℝ))]
    exact hf.2 _ (project_law hp (prefixMap m)) hdist

end
end CanonneCountable
