import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A single unordered four-strip sample from 20 fixed beach strips. The
observer sees the chosen labels and their counts. No selector identifier is
available. The three sampling laws are exchangeable within the two endpoint
and eighteen interior positions, and differ in their endpoint-count laws. -/
namespace Shoreline
open scoped BigOperators
noncomputable section

abbrev Strip := Fin 20
abbrev Survey := Finset Strip
abbrev Counts := Strip → ℕ
abbrev Estimator := Survey → Counts → ℝ

def endpoint (i : Strip) : Prop := i=0 ∨ i=19
instance (i : Strip) : Decidable (endpoint i) := inferInstanceAs (Decidable (i=0 ∨ i=19))

/-- The 96 equiprobable integers rounded to the nearest multiple of five.
The strip label here is the selected start in metres divided by five. -/
theorem rounding_multiplicities : ∀ i : Strip,
    ((Finset.range 96).filter (fun x => (x+2)/5=i.val)).card =
      (if endpoint i then 3 else 5) := by decide

def shell (j : ℕ) : Finset Survey :=
  Finset.univ.filter (fun s => s.card=4 ∧ (s.filter endpoint).card=j)
def observed (s : Survey) (y : Counts) (i : Strip) : ℕ := if i∈s then y i else 0
def conditional (j : ℕ) (T : Estimator) (y : Counts) : ℝ :=
  (∑ s ∈ shell j, T s (observed s y)) / (shell j).card
def populationMean (y : Counts) : ℝ := (∑ i, (y i:ℝ)) / 20

structure Row where
  p0 : ℝ
  p1 : ℝ
  p2 : ℝ

/-- Product of weights, conditioned on all four draws being distinct. -/
def mass (a b j : ℕ) : ℕ :=
  Nat.choose 2 j * Nat.choose 18 (4-j) * a^j * b^(4-j)
def whole (a b : ℕ) : Row :=
  let norm : ℝ := mass a b 0 + mass a b 1 + mass a b 2
  ⟨mass a b 0 / norm,mass a b 1 / norm,mass a b 2 / norm⟩

/-- Probability of a new endpoint, conditional on t distinct selections
including e endpoints; only called with the corresponding state mass. -/
def chooseEnd (t e : ℕ) : ℝ :=
  let a : ℝ := (2-e:ℕ)*3
  let b : ℝ := (18-(t-e):ℕ)*5
  a/(a+b)
def successive : ℕ → Row
  | 0 => ⟨1,0,0⟩
  | t+1 =>
    let p := successive t
    ⟨p.p0*(1-chooseEnd t 0),
     p.p0*chooseEnd t 0 + p.p1*(1-chooseEnd t 1),
     p.p1*chooseEnd t 1 + p.p2⟩

inductive Design | uniform | batch | oneAtATime deriving DecidableEq
def law : Design → Row
  | .uniform => whole 1 1
  | .batch => whole 3 5
  | .oneAtATime => successive 4
def expectation (r : Design) (T : Estimator) (y : Counts) : ℝ :=
  (law r).p0*conditional 0 T y + (law r).p1*conditional 1 T y + (law r).p2*conditional 2 T y

theorem probabilities :
    (law .uniform).p1=32/95 ∧ (law .uniform).p2=3/95 ∧
    (law .batch).p1=160/669 ∧ (law .batch).p2=3/223 ∧
    (law .oneAtATime).p1=17871250/76672827 ∧ (law .oneAtATime).p2=2804903/221499278 := by
  norm_num [law,whole,mass,Nat.choose,successive,chooseEnd]

def blanks : Counts := fun _ => 0
def signal : Counts := fun i => (if i=0 then 1 else 0) + (if i=19 then 1 else 0)

theorem signalMean : populationMean signal=1/10 := by
  norm_num [populationMean,signal,Nat.cast_add,Finset.sum_add_distrib,
    Finset.sum_ite_eq']

theorem indistinguishable (T : Estimator) : conditional 0 T blanks=conditional 0 T signal := by
  unfold conditional
  apply congrArg (fun x : ℝ => x / (shell 0).card)
  apply Finset.sum_congr rfl
  intro s hs
  have empty := Finset.card_eq_zero.mp (Finset.mem_filter.mp hs).2.2
  apply congrArg (T s)
  funext i
  by_cases si : i∈s
  · have notEnd : ¬endpoint i := fun h => by
      have hit := Finset.mem_filter.mpr ⟨si,h⟩
      rw [empty] at hit
      exact Finset.notMem_empty i hit
    change ¬(i=0 ∨ i=19) at notEnd
    have p := not_or.mp notEnd
    simp [observed,si,blanks,signal,p.1,p.2]
  · simp [observed,si]

/-- No estimator of the full-site mean is unbiased for every population
under each of the three stipulated designs from a single visit. The
estimator can depend arbitrarily on the entire unordered observed data. -/
theorem no_common_unbiased : ¬ ∃ T : Estimator, ∀ r y, expectation r T y=populationMean y := by
  rintro ⟨T,exactMean⟩
  have zero : populationMean blanks=0 := by simp [populationMean,blanks]
  let a := conditional 1 T signal - conditional 1 T blanks
  let b := conditional 2 T signal - conditional 2 T blanks
  have same := indistinguishable T
  have constraint (r : Design) : (law r).p1*a + (law r).p2*b=1/10 := by
    have h1 := exactMean r signal
    have h0 := exactMean r blanks
    rw [signalMean,expectation] at h1
    rw [zero,expectation,same] at h0
    dsimp only [a,b]
    linarith
  obtain ⟨u1,u2,w1,w2,s1,s2⟩ := probabilities
  have U := constraint .uniform
  have W := constraint .batch
  have S := constraint .oneAtATime
  rw [u1,u2] at U
  rw [w1,w2] at W
  rw [s1,s2] at S
  linarith

#print axioms no_common_unbiased
end
end Shoreline
