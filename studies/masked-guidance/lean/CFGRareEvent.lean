import CFGRare
import Mathlib.Tactic.FinCases

/-! A revealed bit is irreversible. Binary words reached after the marker 1
all lie in the support of the competing class. Quantifying over all stochastic
completions consistent with the first reveal covers any choices of later rates. -/
namespace CFGRareEvent
open CFGRare Filter
open scoped BigOperators Topology
noncomputable section
set_option maxRecDepth 8192

structure Completion where
  prob : Fin 3 → Bool → Word → ℝ
  nonneg : ∀ j b x, 0 ≤ prob j b x
  sums : ∀ j b, ∑ x : Word, prob j b x = 1
  consistent : ∀ j b x, event j b x = false → prob j b x = 0

def sharedAfter (k : Completion) (j : Fin 3) (b : Bool) : ℝ :=
  ∑ x : Word, if x = (false,false,false) then 0 else k.prob j b x

theorem support_shared (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (x : Word) :
    (0 < target s x ∧ 0 < other s x) ↔ x ≠ (false,false,false) := by
  rcases x with ⟨b,c,d⟩
  have h0 : 0 < 1-s := by linarith
  have hd : 0 < 1-s/4 := by linarith
  cases b <;> cases c <;> cases d <;> simp [target, other, bitWeight] <;> constructor <;> positivity

theorem sharedAfter_nonneg (k : Completion) (j : Fin 3) (b : Bool) : 0 ≤ sharedAfter k j b := by
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> first | exact le_rfl | apply k.nonneg)

theorem sharedAfter_le_one (k : Completion) (j : Fin 3) (b : Bool) : sharedAfter k j b ≤ 1 := by
  rw [← k.sums j b]
  exact Finset.sum_le_sum (fun x _ => by split_ifs <;> first | apply k.nonneg | exact le_rfl)

theorem sharedAfter_marker (k : Completion) : sharedAfter k 0 true = 1 := by
  rw [← k.sums 0 true]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · subst x
    exact (k.consistent _ _ _ (by decide)).symm
  · rfl

def terminalShare (first : Fin 3 → Bool → ℝ) (k : Completion) : ℝ :=
  ∑ j : Fin 3, ∑ b : Bool, first j b * sharedAfter k j b

theorem terminalShare_bounds (first : Fin 3 → Bool → ℝ) (k : Completion)
    (hn : ∀ j b, 0 ≤ first j b) (ht : ∑ j : Fin 3, ∑ b : Bool, first j b = 1) :
    first 0 true ≤ terminalShare first k ∧ terminalShare first k ≤ 1 := by
  have hp (j b) : 0 ≤ first j b * sharedAfter k j b := mul_nonneg (hn _ _) (sharedAfter_nonneg ..)
  constructor
  · calc
      first 0 true = first 0 true * sharedAfter k 0 true := by rw [sharedAfter_marker, mul_one]
      _ ≤ ∑ b : Bool, first 0 b * sharedAfter k 0 b := Finset.single_le_sum (fun b _ => hp 0 b) (Finset.mem_univ true)
      _ ≤ terminalShare first k := Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun b _ => hp j b)) (Finset.mem_univ 0)
  · rw [← ht]
    exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun b _ =>
      mul_le_of_le_one_right (hn ..) (sharedAfter_le_one ..)))

/-- The mass-one conclusion holds uniformly over all later reveal rules,
even if they vary with guidance strength. -/
theorem promote_limit (first : ℝ → Fin 3 → Bool → ℝ) (k : ℝ → Completion)
    (hn : ∀ w j b, 0 ≤ first w j b) (ht : ∀ w, ∑ j : Fin 3, ∑ b : Bool, first w j b = 1)
    (hm : Tendsto (fun w => first w 0 true) atTop (𝓝 1)) :
    Tendsto (fun w => terminalShare (first w) (k w)) atTop (𝓝 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hm tendsto_const_nhds
    (fun w => (terminalShare_bounds _ _ (hn w) (ht w)).1)
    (fun w => (terminalShare_bounds _ _ (hn w) (ht w)).2)

def firstChoice (s w : ℝ) (j : Fin 3) (b : Bool) : ℝ :=
  realRootRate s j b w / ∑ k : Fin 3, ∑ c : Bool, realRootRate s k c w

theorem rates_nonneg (s w : ℝ) (h0 : 0 < s) (h1 : s < 1) (j : Fin 3) (b : Bool) :
    0 ≤ realRootRate s j b w := by
  apply mul_nonneg _ (Real.rpow_nonneg (root_likelihood_nonnegative _ h0.le h1.le j b) w)
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;>
    first | exact (class_nonnegative _ h0.le h1.le x).1 | exact le_rfl)

theorem total_pos (s w : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    0 < ∑ j : Fin 3, ∑ b : Bool, realRootRate s j b w := by
  have hn := rates_nonneg s w h0 h1
  have hm : 0 < realRootRate s 0 true w := by
    rw [realRootRate, (raw_marginals s).1, marker_likelihood s h0]
    positivity
  exact Finset.sum_pos' (fun j _ => Finset.sum_nonneg (fun b _ => hn j b))
    ⟨0, Finset.mem_univ _, Finset.sum_pos' (fun b _ => hn 0 b) ⟨true, Finset.mem_univ _, hm⟩⟩

theorem choices_nonnegative (s w : ℝ) (h0 : 0 < s) (h1 : s < 1) (j : Fin 3) (b : Bool) :
    0 ≤ firstChoice s w j b :=
  div_nonneg (rates_nonneg _ _ h0 h1 ..) (total_pos _ _ h0 h1).le

theorem choices_sum (s w : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    ∑ j : Fin 3, ∑ b : Bool, firstChoice s w j b = 1 := by
  simp only [firstChoice, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (total_pos s w h0 h1).ne'

theorem nat_choice (s : ℝ) (n : ℕ) : firstChoice s (n : ℝ) 0 true = firstMarker s n := by
  simp only [firstChoice, firstMarker, realRootRate, rootLikelihood, rootRate, Real.rpow_natCast]

theorem rare_terminal_finite (k : Completion) :
    99/100 < terminalShare (firstChoice (1/100) 50) k := by
  have h := (terminalShare_bounds _ k (choices_nonnegative (1/100) 50 (by norm_num) (by norm_num))
    (choices_sum (1/100) 50 (by norm_num) (by norm_num))).1
  calc
    99/100 < firstMarker (1/100) 50 := rare_finite_witness
    _ = firstChoice (1/100) 50 0 true := (nat_choice _ 50).symm
    _ ≤ terminalShare _ k := h

theorem terminal_product_limit (s : ℝ) (h0 : 0 < s) (h1 : s < 1) (k : ℝ → Completion) :
    Tendsto (fun w => terminalShare (firstChoice s w) (k w)) atTop (𝓝 1) :=
  promote_limit _ _ (fun w => choices_nonnegative s w h0 h1) (fun w => choices_sum s w h0 h1)
    (real_first_marker_limit s h0 h1)

/-- Rare-to-certain amplification for an arbitrarily sparse overlap in the raw
product target, simultaneously for every stochastic consistent completion. -/
theorem rare_amplification (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ overlap s < ε ∧ ∀ k : ℝ → Completion,
      Tendsto (fun w => terminalShare (firstChoice s w) (k w)) atTop (𝓝 1) := by
  obtain ⟨s, h0, h1, hsmall⟩ := rare_initial ε hε
  exact ⟨s, h0, h1, hsmall, terminal_product_limit s h0 h1⟩

end
end CFGRareEvent
