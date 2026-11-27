import CountableLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace CanonneCountable

open scoped BigOperators
noncomputable section

/-- A discrete law in real PMF coordinates. Its declared labels may have
zero probability. -/
structure Law {A : Type*} (p : A → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  hasSumOne : HasSum p 1

theorem Law.summable {A : Type*} {p : A → ℝ} (hp : Law p) : Summable p := hp.hasSumOne.summable
theorem Law.total {A : Type*} {p : A → ℝ} (hp : Law p) : ∑' a, p a = 1 := hp.hasSumOne.tsum_eq

/-- Sum of a nonnegative product of independent coordinate weights. -/
theorem independent_hasSum {A : Type*} (n : ℕ)
    {f : Fin n → A → ℝ} {s : Fin n → ℝ}
    (hfn : ∀ i a, 0 ≤ f i a) (hf : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun z : Fin n → A => ∏ i, f i (z i)) (∏ i, s i) := by
  induction n with
  | zero =>
    convert (hasSum_fintype (fun _ : Fin 0 → A => (1:ℝ))) using 1 <;> simp
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => A)
    have ht := ih (f := fun i => f i.succ) (s := fun i => s i.succ)
      (fun i => hfn i.succ) (fun i => hf i.succ)
    have hs := (hf 0).summable.mul_of_nonneg ht.summable (hfn 0)
      (fun z => Finset.prod_nonneg (fun i _ => hfn i.succ (z i)))
    have hp := (hf 0).mul ht hs
    apply e.hasSum_iff.mp
    convert hp using 1
    · funext z
      simp [e, Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ]
    · rw [Fin.prod_univ_succ]

/-- The distribution of a fixed number of ordered IID observations. -/
def iid {A : Type*} (p : A → ℝ) (n : ℕ) (z : Fin n → A) : ℝ := ∏ i, p (z i)

theorem iid_law {A : Type*} {p : A → ℝ} (hp : Law p) (n : ℕ) : Law (iid p n) := by
  refine ⟨fun _ => Finset.prod_nonneg fun _ _ => hp.nonneg _, ?_⟩
  unfold iid
  simpa only [Finset.prod_const_one] using independent_hasSum n
    (fun _ => hp.nonneg) (s := fun _ => (1:ℝ)) (fun _ => hp.hasSumOne)

theorem sum_diff_abs_summable {A : Type*} {p q : A → ℝ} (hp : Law p) (hq : Law q) :
    Summable (fun a => |p a-q a|) := by
  have h := hp.summable.add hq.summable
  exact h.of_nonneg_of_le (fun _ => abs_nonneg _) (fun a => by
    apply abs_le.mpr
    constructor <;> linarith [hp.nonneg a, hq.nonneg a])

/-- Half-L1 on the full probability mass functions. -/
def tv {A : Type*} (p q : A → ℝ) : ℝ := (∑' a, |p a-q a|)/2

def GoodTest {A : Type*} (q : A → ℝ) (e : ℝ) (n : ℕ) (f : TestBox (Fin n → A)) : Prop :=
  expectation (iid q n) (fun x => (f x : ℝ)) ≤ 1/3 ∧
    ∀ p : A → ℝ, Law p → e < tv p q →
      2/3 ≤ expectation (iid p n) (fun x => (f x : ℝ))

end
end CanonneCountable
