import CFGFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A necessary binary specialization of the limiting-support clause of
He–Rojas–Tao, Proposition 3.3(2). Both normalized jumps are constructed from
the raw class distributions and the exact guidance rates with real strength. -/

namespace CFGLimit2

open CFGFinite Filter
open scoped BigOperators Topology

noncomputable section

abbrev Table := Word 2 → ℚ

def equalPrior (p q : Table) : Table := fun x => (p x + q x) / 2

/-- An unnormalized off-diagonal reveal rate with the common time clock
removed. On a positive target transition Eq. (9) is
`conditionalTarget * (conditionalTarget / conditionalMixture) ^ w`.
An already visible coordinate or a zero-target transition cannot be revealed. -/
def guidedRate (p q : Table) (w : ℝ) (s : State 2) (j : Fin 2) (b : Bool) : ℝ :=
  let target := conditional p s j b
  let mixed := conditional (equalPrior p q) s j b
  if s j = none ∧ 0 < target then (target : ℝ) * ((target / mixed : ℚ) : ℝ) ^ w else 0

def exitRate (p q : Table) (w : ℝ) (s : State 2) : ℝ :=
  ∑ j : Fin 2, ∑ b : Bool, guidedRate p q w s j b

def jumpProbability (p q : Table) (w : ℝ) (s : State 2) (j : Fin 2) (b : Bool) : ℝ :=
  guidedRate p q w s j b / exitRate p q w s

def remainingMass (p q : Table) (w : ℝ) (s : State 2) (x : Word 2) : ℝ :=
  ∑ j : Fin 2, ∑ b : Bool,
    jumpProbability p q w s j b * (if reveal s j b = complete x then 1 else 0)

/-- The probability at the completed word after the two masked reverse
jumps, summing both reveal orders and all feasible intermediate values. -/
def terminalProbability (p q : Table) (w : ℝ) (x : Word 2) : ℝ :=
  ∑ j : Fin 2, ∑ b : Bool,
    jumpProbability p q w (masked 2) j b * remainingMass p q w (reveal (masked 2) j b) x

def ValidClass (p : Table) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1 ∧ ∃ x, p x = 0

def ProjectedOverlap (p q : Table) : Prop :=
  ∃ (j : Fin 2) (b : Bool),
    0 < marginal p (reveal (masked 2) j b) ∧ 0 < marginal q (reveal (masked 2) j b)

def HasPrivateWord (p q : Table) : Prop := ∃ x, 0 < p x ∧ q x = 0

def FullyShared (p q : Table) (x : Word 2) : Prop := 0 < p x ∧ 0 < q x

/-- The limiting-support claim implies this specialization to two equally
weighted classes with rational probabilities on binary words. The additional
private-word premise ensures the asserted limiting support is nonempty. -/
def Proposition33OverlapVanishes : Prop :=
  ∀ (p q : Table) (x : Word 2),
    ValidClass p → ValidClass q → ProjectedOverlap p q → HasPrivateWord p q → FullyShared p q x →
    Tendsto (fun w : ℝ => terminalProbability p q w x) atTop (𝓝 0)

abbrev target : Table := @targetWeight 2
abbrev rival : Table := @otherWeight 2

abbrev privateWord : Word 2 := constant 2 false
abbrev sharedWord : Word 2 := constant 2 true

set_option maxHeartbeats 0
set_option maxRecDepth 8192

theorem validTarget : ValidClass target := by
  unfold ValidClass
  decide +kernel

theorem validRival : ValidClass rival := by
  unfold ValidClass
  decide +kernel

theorem projectsOverlap : ProjectedOverlap target rival := by
  unfold ProjectedOverlap
  decide +kernel

theorem privateExists : HasPrivateWord target rival := by
  unfold HasPrivateWord
  decide +kernel

theorem overlapAtShared : FullyShared target rival sharedWord := by
  unfold FullyShared
  decide +kernel

private theorem firstData : ∀ (j : Fin 2) (b : Bool),
    conditional target (masked 2) j b = (if b then 3 / 4 else 1 / 4) ∧
    conditional (equalPrior target rival) (masked 2) j b = (if b then 17 / 24 else 7 / 24) := by
  decide +kernel

private theorem secondData : ∀ (j k : Fin 2) (b c : Bool), k ≠ j →
    conditional target (reveal (masked 2) j b) k c = (if c = b then 1 else 0) ∧
    conditional (equalPrior target rival) (reveal (masked 2) j b) k c =
      (if b then (if c then 13 / 17 else 4 / 17) else (if c then 4 / 7 else 3 / 7)) := by
  decide +kernel

private theorem revealSame : ∀ (j k : Fin 2) (b : Bool), k ≠ j →
    reveal (reveal (masked 2) j b) k b = complete (constant 2 b) := by
  decide +kernel

private theorem differentTerminal : complete privateWord ≠ complete sharedWord := by
  decide +kernel

private def firstFactor (w : ℝ) (b : Bool) : ℝ :=
  (if b then 3 / 4 else 1 / 4) * (if b then (18 / 17 : ℝ) else (6 / 7 : ℝ)) ^ w

private def secondFactor (w : ℝ) (b : Bool) : ℝ :=
  (if b then (17 / 13 : ℝ) else (7 / 3 : ℝ)) ^ w

private theorem firstFactor_pos (w : ℝ) (b : Bool) : 0 < firstFactor w b := by
  cases b <;> simp only [firstFactor, Bool.false_eq_true, ite_false, ite_true] <;> positivity

private theorem secondFactor_pos (w : ℝ) (b : Bool) : 0 < secondFactor w b := by
  cases b <;> simp only [secondFactor, Bool.false_eq_true, ite_false, ite_true] <;> positivity

theorem witnessFirstRate (w : ℝ) (j : Fin 2) (b : Bool) :
    guidedRate target rival w (masked 2) j b = firstFactor w b := by
  obtain ⟨ht, hm⟩ := firstData j b
  unfold guidedRate firstFactor
  cases b <;> simp [masked, ht, hm] <;> norm_num

theorem witnessSecondRate (w : ℝ) (j k : Fin 2) (b c : Bool) :
    guidedRate target rival w (reveal (masked 2) j b) k c =
      if k = j then 0 else if c = b then secondFactor w b else 0 := by
  by_cases h : k = j
  · simp [guidedRate, reveal, h]
  · obtain ⟨ht, hm⟩ := secondData j k b c h
    unfold guidedRate
    cases b <;> cases c <;> simp [reveal, masked, h, ht, hm, secondFactor]

private theorem firstTotal (w : ℝ) : exitRate target rival w (masked 2) =
    2 * (firstFactor w false + firstFactor w true) := by
  simp only [exitRate, witnessFirstRate, Fin.sum_univ_two, Fintype.sum_bool]
  ring

private theorem secondTotal (w : ℝ) (j : Fin 2) (b : Bool) :
    exitRate target rival w (reveal (masked 2) j b) = secondFactor w b := by
  fin_cases j <;> cases b <;>
    simp [exitRate, witnessSecondRate, Fin.sum_univ_two]

private theorem witnessRemaining (w : ℝ) (j : Fin 2) (b : Bool) :
    remainingMass target rival w (reveal (masked 2) j b) sharedWord = if b then 1 else 0 := by
  have hpos := (secondFactor_pos w b).ne'
  fin_cases j <;> cases b <;>
    simp [remainingMass, jumpProbability, secondTotal, witnessSecondRate, Fin.sum_univ_two,
      hpos, revealSame, differentTerminal]

theorem terminal_from_rates (w : ℝ) : terminalProbability target rival w sharedWord =
    firstFactor w true / (firstFactor w false + firstFactor w true) := by
  have hpos : 0 < firstFactor w false + firstFactor w true :=
    add_pos (firstFactor_pos w false) (firstFactor_pos w true)
  simp only [terminalProbability, witnessRemaining, jumpProbability, firstTotal, witnessFirstRate,
    Fin.sum_univ_two, Fintype.sum_bool]
  simp
  field_simp [hpos.ne']
  ring

theorem terminal_exact (w : ℝ) :
    terminalProbability target rival w sharedWord = 3 / ((17 / 21 : ℝ) ^ w + 3) := by
  rw [terminal_from_rates]
  simp only [firstFactor, Bool.false_eq_true, ite_false, ite_true]
  have hpow : (17 / 21 : ℝ) ^ w = (6 / 7 : ℝ) ^ w / (18 / 17 : ℝ) ^ w := by
    rw [← Real.div_rpow (by norm_num : 0 ≤ (6 / 7 : ℝ)) (by norm_num : 0 ≤ (18 / 17 : ℝ)) w]
    norm_num
  rw [hpow]
  have hbase : 0 < (18 / 17 : ℝ) ^ w := by positivity
  have hden : 0 < (1 / 4 : ℝ) * (6 / 7 : ℝ) ^ w + (3 / 4 : ℝ) * (18 / 17 : ℝ) ^ w := by
    positivity
  have hd : 0 < (6 / 7 : ℝ) ^ w / (18 / 17 : ℝ) ^ w + 3 := by positivity
  field_simp [hbase.ne', hden.ne', hd.ne']

theorem shared_mass_tends_to_one :
    Tendsto (fun w : ℝ => terminalProbability target rival w sharedWord) atTop (𝓝 1) := by
  have h := tendsto_rpow_atTop_of_base_lt_one (17 / 21 : ℝ) (by norm_num) (by norm_num)
  have hd := h.add (tendsto_const_nhds (x := (3 : ℝ)))
  have hn : Tendsto (fun w : ℝ => 3 / ((17 / 21 : ℝ) ^ w + 3)) atTop (𝓝 ((3 : ℝ) / (0 + 3))) :=
    (tendsto_const_nhds (x := (3 : ℝ))).div hd (by norm_num)
  simpa only [terminal_exact, zero_add, div_self (by norm_num : (3 : ℝ) ≠ 0)] using hn

theorem not_proposition33_overlap_vanishes : ¬ Proposition33OverlapVanishes := by
  intro universally
  have h := universally target rival sharedWord validTarget validRival projectsOverlap privateExists
    overlapAtShared
  exact one_ne_zero (tendsto_nhds_unique shared_mass_tends_to_one h)

end

end CFGLimit2
