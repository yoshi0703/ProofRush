import Asymptotic
import Mathlib.Topology.Instances.Real.Lemmas

/-! The actual infimum over inputs, with the supremum over greedy ties taken
first. A finite input uses finitely many characters of the countable alphabet. -/
namespace DiamondLimit
open SpellingBPE Filter
open scoped Topology
abbrev Letters := ℕ ⊕ ℕ
abbrev Run := ℕ → Word Letters → Word Letters → Prop

noncomputable def best (run : Run) (w : Word Letters) (k : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun g => ∃ v, run k w v ∧ w.length-v.length=g) w.length

theorem best_attained (run : Run) (w : Word Letters) (k : ℕ) (existsRun : ∃ v, run k w v) :
    ∃ v, run k w v ∧ w.length-v.length = best run w k := by
  classical
  obtain ⟨v,hv⟩ := existsRun
  exact Nat.findGreatest_spec (P := fun g => ∃ u, run k w u ∧ w.length-u.length=g)
    (Nat.sub_le w.length v.length) ⟨v,hv,rfl⟩

theorem le_best (run : Run) (w : Word Letters) (k : ℕ) (v : Word Letters) (h : run k w v) :
    w.length-v.length ≤ best run w k := by
  classical
  exact Nat.le_findGreatest (Nat.sub_le ..) ⟨v,h,rfl⟩

def allowed (w : Word Letters) : Prop := (∀ a ∈ w, a ≠ []) ∧ ¬UniqueDecoding w

noncomputable def ratios (run : Run) (k : ℕ) : Set ℝ :=
  {x | ∃ w : Word Letters, allowed w ∧ 0 < optimum w k ∧ (∃ v, run k w v) ∧
    x = (best run w k : ℝ)/optimum w k}

noncomputable def worst (run : Run) (k : ℕ) : ℝ := sInf (ratios run k)

theorem ratio_nonneg (run : Run) (k : ℕ) {x : ℝ} (hx : x ∈ ratios run k) : 0 ≤ x := by
  obtain ⟨w,_,_,_,rfl⟩ := hx
  positivity

theorem limit_of_construction (run : Run)
    (construction : ∀ ε : ℚ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K,
      ∃ w : Word Letters, allowed w ∧ 0 < optimum w k ∧ (∃ v, run k w v) ∧
        ∀ v, run k w v → ((w.length-v.length : ℕ) : ℚ)/optimum w k < ε) :
    Tendsto (worst run) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_,?_⟩
  · intro a ha
    exact Filter.Eventually.of_forall (fun k => ha.trans_le
      (Real.sInf_nonneg (fun _ h => ratio_nonneg run k h)))
  · intro a ha
    obtain ⟨q,hq,qa⟩ := exists_rat_btwn ha
    obtain ⟨K,large⟩ := construction q (by exact_mod_cast hq)
    apply Filter.eventually_atTop.2
    refine ⟨K,?_⟩
    intro k hk
    obtain ⟨w,good,pos,existsRun,every⟩ := large k hk
    obtain ⟨v,hv,attains⟩ := best_attained run w k existsRun
    have rat := every v hv
    rw [attains] at rat
    have inside : ((best run w k:ℝ)/optimum w k) ∈ ratios run k :=
      ⟨w,good,pos,existsRun,rfl⟩
    have lower : BddBelow (ratios run k) := ⟨0,fun _ hx => ratio_nonneg run k hx⟩
    apply (csInf_le lower inside).trans_lt
    apply lt_trans _ qa
    simpa only [Rat.cast_div,Rat.cast_natCast] using (Rat.cast_lt (K := ℝ)).2 rat

end DiamondLimit
