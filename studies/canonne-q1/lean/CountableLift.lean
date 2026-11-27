import CountableProjection

namespace CanonneCountable

open scoped BigOperators
noncomputable section

variable {A B : Type*} [Fintype B] [DecidableEq B]

/-- A mixture with finite component index. -/
def mix (r : B → ℝ) (K : B → A → ℝ) (a : A) : ℝ := ∑ b, r b * K b a

omit [Fintype B] in
private theorem summable_finite_sum {f : B → A → ℝ} (s : Finset B)
    (hf : ∀ b ∈ s, Summable (f b)) : Summable (fun a => ∑ b ∈ s, f b a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    simpa only [Finset.sum_insert hb] using (hf b (Finset.mem_insert_self _ _)).add
      (ih (fun c hc => hf c (Finset.mem_insert_of_mem hc)))

theorem finite_mix_law {r : B → ℝ} (hr : Law r) {K : B → A → ℝ}
    (hK : ∀ b, Law (K b)) : Law (mix r K) := by
  refine ⟨fun a => Finset.sum_nonneg fun b _ => mul_nonneg (hr.nonneg b) ((hK b).nonneg a), ?_⟩
  have hs : Summable (mix r K) := summable_finite_sum Finset.univ
    (fun b _ => (hK b).summable.mul_left (r b))
  have he : (∑' a, mix r K a) = 1 := by
    unfold mix
    rw [Summable.tsum_finsetSum (fun b _ => (hK b).summable.mul_left (r b))]
    simp only [tsum_mul_left, (hK _).total, mul_one]
    simpa only [tsum_fintype] using hr.total
  exact he ▸ hs.hasSum

def onFiber (g : A → B) (q : A → ℝ) (b : B) (a : A) : ℝ :=
  if g a = b then q a else 0

theorem conditional_law {q : A → ℝ} (hq : Law q) (g : A → B) (onto : Function.Surjective g) :
    ∃ K : B → A → ℝ,
      (∀ b, Law (K b)) ∧ (∀ a b, g a ≠ b → K b a = 0) ∧
      (mix (project g q) K = q) := by
  classical
  let a₀ (b : B) := Classical.choose (onto b)
  have hpre (b : B) : g (a₀ b) = b := Classical.choose_spec (onto b)
  let K (b : B) (a : A) :=
    if 0 < project g q b then onFiber g q b a / project g q b
    else if a = a₀ b then 1 else 0
  have hzero (a : A) (b : B) (hna : g a ≠ b) : K b a = 0 := by
    have hneq : a ≠ a₀ b := fun h => hna (h ▸ hpre b)
    simp [K, onFiber, hna, hneq]
  refine ⟨K, ?_, hzero, ?_⟩
  · intro b
    by_cases hb : 0 < project g q b
    · refine ⟨?_, ?_⟩
      · intro a
        have hn : 0 ≤ onFiber g q b a := by
          unfold onFiber
          split <;> first | exact hq.nonneg _ | exact le_rfl
        simpa only [K, ite_eq_left hb] using div_nonneg hn hb.le
      · have hs := (fiber_summable hq g b).hasSum
        change HasSum (onFiber g q b) (project g q b) at hs
        simpa only [K, ite_eq_left hb, div_self hb.ne'] using hs.div_const (project g q b)
    · have hs : Summable (fun a : A => if a = a₀ b then (1:ℝ) else 0) :=
        summable_of_ne_finset_zero (s := {a₀ b}) (fun a ha => by simpa using ha)
      refine ⟨fun a => by simp [K,hb]; split <;> norm_num, ?_⟩
      simp only [K, ite_eq_right hb]
      refine hs.hasSum.trans ?_
      rw [tsum_eq_single (a₀ b)]
      · simp
      · intro a ha
        simp [ha]
  · funext a
    unfold mix
    rw [Finset.sum_eq_single (g a)]
    · by_cases hb : 0 < project g q (g a)
      · simp [K, onFiber, hb, mul_div_cancel₀ _ hb.ne']
      · have hp : 0 ≤ project g q (g a) := (project_law hq g).nonneg _
        have hh : project g q (g a) = 0 := le_antisymm (le_of_not_gt hb) hp
        have hle : q a ≤ project g q (g a) := by
          change q a ≤ ∑' a', if g a' = g a then q a' else 0
          simpa using (fiber_summable hq g (g a)).sum_le_tsum ({a} : Finset A)
            (fun a' _ => by split <;> first | exact hq.nonneg _ | exact le_rfl)
        rw [hh, zero_mul]
        exact (le_antisymm (hle.trans hh.le) (hq.nonneg _)).symm
    · intro b _ hb
      rw [hzero a b (Ne.symm hb), mul_zero]
    · simp

omit [DecidableEq B] in
theorem mix_fiber_apply (g : A → B) (K : B → A → ℝ)
    (hzero : ∀ a b, g a ≠ b → K b a = 0) (r : B → ℝ) (a : A) :
    mix r K a = r (g a) * K (g a) a := by
  unfold mix
  rw [Finset.sum_eq_single (g a)]
  · intro b _ hb
    rw [hzero a b (Ne.symm hb), mul_zero]
  · simp

omit [DecidableEq B] in
/-- A fiber-supported kernel preserves the distance between two projected
laws exactly, even on a fiber to which the null assigns probability zero. -/
theorem fiber_lift_preserves_tv (g : A → B) {K : B → A → ℝ}
    (hK : ∀ b, Law (K b)) (hzero : ∀ a b, g a ≠ b → K b a = 0)
    (p q : B → ℝ) :
    tv (mix p K) (mix q K) = tv p q := by
  have hpoint (a : A) :
      |mix p K a - mix q K a| = ∑ b, |p b - q b| * K b a := by
    rw [mix_fiber_apply g K hzero p a, mix_fiber_apply g K hzero q a,
      ← sub_mul, abs_mul, abs_of_nonneg ((hK (g a)).nonneg a)]
    symm
    apply Finset.sum_eq_single (g a)
    · intro b _ hb
      rw [hzero a b (Ne.symm hb), mul_zero]
    · simp
  simp only [tv, hpoint, tsum_fintype]
  rw [Summable.tsum_finsetSum (fun b _ => (hK b).summable.mul_left (|p b-q b|))]
  simp only [tsum_mul_left, (hK _).total, mul_one]

/-- Given a finite record, independently sample each conditional fiber.
The resulting record is a product law with possibly differing marginals. -/
def liftRecord (K : B → A → ℝ) {n : ℕ} (z : Fin n → B) (x : Fin n → A) : ℝ :=
  ∏ i, K (z i) (x i)

omit [Fintype B] [DecidableEq B] in
theorem liftRecord_law {K : B → A → ℝ} (hK : ∀ b, Law (K b))
    {n : ℕ} (z : Fin n → B) : Law (liftRecord K z) := by
  refine ⟨fun x => Finset.prod_nonneg fun i _ => (hK (z i)).nonneg _, ?_⟩
  unfold liftRecord
  simpa only [Finset.prod_const_one] using independent_hasSum n
    (fun i => (hK (z i)).nonneg) (s := fun _ => (1:ℝ)) (fun i => (hK (z i)).hasSumOne)

omit [DecidableEq B] in
theorem iid_mix_expectation {r : B → ℝ} (K : B → A → ℝ) (hK : ∀ b, Law (K b))
    (n : ℕ) (f : TestBox (Fin n → A)) :
    expectation (iid (mix r K) n) (fun x => (f x : ℝ)) =
      expectation (iid r n) (fun y => expectation (liftRecord K y) (fun x => (f x : ℝ))) := by
  have hpoint (x : Fin n → A) :
      iid (mix r K) n x = ∑ y : Fin n → B, iid r n y * liftRecord K y x := by
    unfold iid mix liftRecord
    simp only [← Finset.prod_mul_distrib]
    exact Fintype.prod_sum (fun i b => r b * K b (x i))
  have hfam (y : Fin n → B) :
      Summable (fun x => liftRecord K y x * (f x : ℝ)) := by
    have h := liftRecord_law hK y
    exact h.summable.of_nonneg_of_le
      (fun x => mul_nonneg (h.nonneg x) (f x).2.1) (fun x =>
        mul_le_of_le_one_right (h.nonneg x) (f x).2.2)
  simp only [expectation, hpoint, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun y _ => (hfam y).mul_left (iid r n y)), tsum_fintype]
  simp only [tsum_mul_left]

theorem expectation_in_unit_interval {p : A → ℝ} (hp : Law p) {f : TestBox A} :
    expectation p (fun x => (f x : ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
  have hn (a : A) : 0 ≤ p a * f a := mul_nonneg (hp.nonneg a) (f a).2.1
  have hle (a : A) : p a * f a ≤ p a := mul_le_of_le_one_right (hp.nonneg a) (f a).2.2
  have hf := hp.summable.of_nonneg_of_le hn hle
  refine ⟨tsum_nonneg hn, ?_⟩
  unfold expectation
  exact (hf.tsum_le_tsum hle hp.summable).trans_eq hp.total

/-- Every successful test pulls back to any finite surjective projection
via an independent null-conditional draw on each record position. -/
theorem good_test_projects {q : A → ℝ} (hq : Law q) (g : A → B)
    (onto : Function.Surjective g) {e : ℝ} {n : ℕ}
    (htest : ∃ f, GoodTest q e n f) :
    ∃ f, GoodTest (project g q) e n f := by
  obtain ⟨K, hK, hzero, hqLift⟩ := conditional_law hq g onto
  obtain ⟨f, hnull, halt⟩ := htest
  let f' (y : Fin n → B) : Set.Icc (0:ℝ) 1 :=
    ⟨_, expectation_in_unit_interval (liftRecord_law hK y) (f := f)⟩
  refine ⟨f', ?_, ?_⟩
  · have he := iid_mix_expectation (r := project g q) K hK n f
    rw [hqLift] at he
    exact he.symm ▸ hnull
  · intro p hp hfar
    have hd := fiber_lift_preserves_tv g hK hzero p (project g q)
    rw [hqLift] at hd
    have hpower := halt (mix p K) (finite_mix_law hp hK) (hd.symm ▸ hfar)
    exact (iid_mix_expectation (r := p) K hK n f) ▸ hpower

theorem prefix_surjective (m : ℕ) : Function.Surjective (prefixMap m) := by
  intro b
  cases b with
  | none => exact ⟨m, by simp [prefixMap]⟩
  | some i => exact ⟨i.val, prefix_some_dot.mpr rfl⟩

/-- Finite prefixMap projections and the full countable test have identical
fixed-budget feasibility at the original strict radius. -/
theorem good_test_iff_all_prefix_tests {q : ℕ → ℝ} (hq : Law q) {e : ℝ} {n : ℕ} :
    (∃ f, GoodTest q e n f) ↔
    ∀ m, ∃ f, GoodTest (project (prefixMap m) q) e n f :=
  ⟨fun h m => good_test_projects hq (prefixMap m) (prefix_surjective m) h,
    good_test_of_all_prefix_tests hq⟩

end
end CanonneCountable
