import CountableProduct

namespace CanonneCountable

open Filter
open scoped Topology BigOperators
noncomputable section

section Project

variable {A B : Type*} [Fintype B] [DecidableEq B]

/-- Ordinary discrete pushforward to a finite label space. -/
def project (g : A → B) (p : A → ℝ) (b : B) : ℝ :=
  ∑' a, if g a = b then p a else 0

omit [Fintype B] in
theorem fiber_summable {p : A → ℝ} (hp : Law p) (g : A → B) (b : B) :
    Summable (fun a => if g a = b then p a else 0) := by
  apply hp.summable.of_nonneg_of_le
  · intro a
    split <;> first | exact hp.nonneg _ | exact le_rfl
  · intro a
    split <;> first | exact hp.nonneg _ | exact le_rfl

/-- The pushforward identity for expectation, including zero-mass fibers. -/
theorem expectation_project {p : A → ℝ} (hp : Law p) (g : A → B) (f : B → ℝ) :
    expectation (project g p) f = expectation p (f ∘ g) := by
  unfold expectation project
  rw [tsum_fintype]
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun b _ => (fiber_summable hp g b).mul_right (f b))]
  apply tsum_congr
  intro a
  rw [Finset.sum_eq_single (g a)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem project_law {p : A → ℝ} (hp : Law p) (g : A → B) : Law (project g p) := by
  have hnonneg (b : B) : 0 ≤ project g p b := by
    unfold project
    exact tsum_nonneg (fun a => by split <;> first | exact hp.nonneg _ | exact le_rfl)
  refine ⟨hnonneg, ?_⟩
  have he := expectation_project hp g (fun _ => 1)
  simp only [expectation, mul_one, Function.comp_apply, hp.total] at he
  have hs : HasSum (project g p) (∑ b, project g p b) := hasSum_fintype _
  have hm : ∑ b, project g p b = 1 := by simpa only [tsum_fintype] using he
  rwa [hm] at hs

omit [Fintype B] in
/-- Projecting each coordinate of an ordered IID record gives exactly the
ordered IID law of the projected one-draw PMF. -/
theorem project_iid {p : A → ℝ} (hp : Law p) (g : A → B) (n : ℕ) :
    project (fun z : Fin n → A => g ∘ z) (iid p n) = iid (project g p) n := by
  classical
  funext y
  unfold project
  have hs := independent_hasSum n
    (f := fun i a => if g a = y i then p a else 0)
    (s := fun i => ∑' a, if g a = y i then p a else 0)
    (fun i a => by split <;> first | exact hp.nonneg _ | exact le_rfl)
    (fun i => (fiber_summable hp g (y i)).hasSum)
  have hterm (z : Fin n → A) :
      (if g ∘ z = y then iid p n z else 0) = ∏ i, (if g (z i) = y i then p (z i) else 0) := by
    by_cases he : g ∘ z = y
    · rw [ite_eq_left he]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_left (show g (z i) = y i from congrFun he i)]
    · rw [ite_eq_right he]
      obtain ⟨i, hi⟩ := not_forall.mp (show ¬ ∀ i, g (z i) = y i from fun h => he (funext h))
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm
  calc
    _ = ∑' z : Fin n → A, ∏ i, (if g (z i) = y i then p (z i) else 0) := tsum_congr hterm
    _ = _ := hs.tsum_eq

/-- Rejection by a lifted finite test, expressed either on full records
or on the projected ordered records. -/
theorem expectation_projected_records {p : A → ℝ} (hp : Law p) (g : A → B) (n : ℕ)
    (f : (Fin n → B) → ℝ) :
    expectation (iid (project g p) n) f =
      expectation (iid p n) (fun z => f (g ∘ z)) := by
  rw [← project_iid hp g n]
  exact expectation_project (iid_law hp n) (fun z => g ∘ z) f

end Project

/-- Labels 0 through m−1 stay distinct, and every remaining
declared label maps to one tail cell. -/
def prefixMap (m : ℕ) (a : ℕ) : Option (Fin m) :=
  if h : a < m then some ⟨a,h⟩ else none

theorem prefix_some_dot {m a : ℕ} {i : Fin m} :
    prefixMap m a = some i ↔ a = i.val := by
  unfold prefixMap
  split
  · constructor
    · intro h
      exact congrArg Fin.val (Option.some.inj h)
    · intro h
      exact congrArg some (Fin.ext h)
  · rename_i h
    constructor
    · simp
    · intro he
      exact False.elim (h (he ▸ i.isLt))

theorem prefix_project_some (m : ℕ) (p : ℕ → ℝ) (i : Fin m) :
    project (prefixMap m) p (some i) = p i.val := by
  unfold project
  rw [tsum_eq_single i.val]
  · rw [ite_eq_left (prefix_some_dot.mpr rfl)]
  · intro a ha
    rw [ite_eq_right (fun h => ha (prefix_some_dot.mp h))]

theorem prefix_difference_lower (p q : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, |p i - q i|)/2 ≤ tv (project (prefixMap m) p) (project (prefixMap m) q) := by
  unfold tv
  rw [tsum_fintype, Fintype.sum_option]
  simp only [prefix_project_some]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => |p i-q i|) m]
  linarith [abs_nonneg (project (prefixMap m) p none - project (prefixMap m) q none)]

/-- Every alternative at the original strict radius survives all
sufficiently fine finite prefix projections, at exactly the same radius. -/
theorem eventually_strict_far_on_prefix {p q : ℕ → ℝ} (hp : Law p) (hq : Law q)
    {e : ℝ} (hfar : e < tv p q) :
    ∀ᶠ m in atTop, e < tv (project (prefixMap m) p) (project (prefixMap m) q) := by
  have hlim : Tendsto (fun m => (∑ i ∈ Finset.range m, |p i - q i|)/2)
      atTop (𝓝 (tv p q)) :=
    (sum_diff_abs_summable hp hq).hasSum.tendsto_sum_nat.div_const 2
  have hev : ∀ᶠ m in atTop, e < (∑ i ∈ Finset.range m, |p i - q i|)/2 :=
    (tendsto_order.1 hlim).1 _ hfar
  exact hev.mono fun m h => h.trans_le (prefix_difference_lower p q m)

/-- The forward projection principle at a fixed sample budget, including
zero observations. All projected tests use the same strict radius. -/
theorem good_test_of_all_prefix_tests {q : ℕ → ℝ} (hq : Law q) {e : ℝ} {n : ℕ}
    (hfinite : ∀ m, ∃ f, GoodTest (project (prefixMap m) q) e n f) :
    ∃ f, GoodTest q e n f := by
  classical
  choose tests htests using hfinite
  let f (m : ℕ) (z : Fin n → ℕ) := tests m (prefixMap m ∘ z)
  let P := {p : ℕ → ℝ // Law p ∧ e < tv p q}
  have hn m : expectation (iid q n) (fun x => (f m x : ℝ)) ≤ 1/3 := by
    unfold f
    rw [← expectation_projected_records hq (prefixMap m) n (fun y => (tests m y : ℝ))]
    exact (htests m).1
  have ha (p : P) :
      ∀ᶠ m in atTop, 2/3 ≤ expectation (iid p.val n) (fun x => (f m x : ℝ)) := by
    filter_upwards [eventually_strict_far_on_prefix p.2.1 hq p.2.2] with m hm
    unfold f
    rw [← expectation_projected_records p.2.1 (prefixMap m) n (fun y => (tests m y : ℝ))]
    exact (htests m).2 _ (project_law p.2.1 (prefixMap m)) hm
  obtain ⟨fLimit, hb, hf⟩ := compact_test_limit (iid_law hq n).summable (iid_law hq n).nonneg
    (fun p : P => (iid_law p.2.1 n).summable) (fun p : P => (iid_law p.2.1 n).nonneg) f hn ha
  exact ⟨fLimit, hb, fun p hp hfar => hf ⟨p,hp,hfar⟩⟩

end
end CanonneCountable
