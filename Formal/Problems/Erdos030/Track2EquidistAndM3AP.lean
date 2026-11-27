import Problems.Erdos030.Statement
import Mathlib.Tactic

/-!
# Track 2 Formal Theorems: Exact Mod-`q` Equidistribution & Strict `M_3AP(11)` Separation

Formalizes:
1. **Theorem T2-C (`h_11_eq_4`, `strict_separation_h11_lt_m3ap_core`)**:
   Exact evaluation `h(11) = 4` and strict separation `h(11) = 4 < 3√2 ≤ M_3AP(11)` via the
   3-AP-free `B_2[2]` witness `B = {0, 1, 3, 7, 9, 10}`, `μ = (1/√2) 1_B`.
2. **Theorem T2-A (`matrix_mod_q_equidistribution`, `mod_q_support_collapse_of_equidist`)**:
   Purely real exact mod-`q` equidistribution inequality for any symmetric matrix `X` satisfying
   Sidon off-diagonal sums `≤ 1` and window-square domination (covering both `IsFractionalSidon`
   with `E = ∑ μ_y^2` and `IsSDP1Feasible` with `E = ∑ μ_y`), together with the residue-class
   support collapse corollary.
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-! ### Part 1: Theorem T2-C — Exact `h(11) = 4` & Strict Separation `h(11) < M_3AP(11)` -/

/-- A measure `μ : ℕ → ℝ` on `{0, ..., N - 1}` is 3-AP-free (`T_3(μ) = 0` for `μ ≥ 0`) if
every nontrivial 3-term arithmetic progression `a < b < c < N` (`a + c = 2 * b`) has
`μ a * μ b * μ c = 0`. -/
def Is3APFreeMeasure (N : ℕ) (μ : ℕ → ℝ) : Prop :=
  ∀ a b c : ℕ, a < b → b < c → c < N → a + c = 2 * b → μ a * μ b * μ c = 0

/-- Helper: reflecting a Sidon set `A ⊆ Icc 1 11` via `x ↦ 12 - x` preserves `⊆ Icc 1 11`,
cardinality, and `IsSidon`. -/
private lemma sidon_reflect_11 {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 11)
    (hS : IsSidon (A : Set ℕ)) :
    let A' := A.image (fun x => 12 - x)
    A' ⊆ Finset.Icc 1 11 ∧ A'.card = A.card ∧ IsSidon (A' : Set ℕ) := by
  intro A'
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxI := Finset.mem_Icc.mp (hsub hx)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · refine Finset.card_image_of_injOn ?_
    intro x₁ hx₁ x₂ hx₂ heq
    have h1 := Finset.mem_Icc.mp (hsub hx₁)
    have h2 := Finset.mem_Icc.mp (hsub hx₂)
    dsimp only at heq; omega
  · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
    simp only [A', Finset.mem_coe, Finset.mem_image] at ha₁ hb₁ ha₂ hb₂
    rcases ha₁ with ⟨x₁, hx₁, rfl⟩
    rcases hb₁ with ⟨y₁, hy₁, rfl⟩
    rcases ha₂ with ⟨x₂, hx₂, rfl⟩
    rcases hb₂ with ⟨y₂, hy₂, rfl⟩
    have h1 := Finset.mem_Icc.mp (hsub hx₁)
    have h2 := Finset.mem_Icc.mp (hsub hy₁)
    have h3 := Finset.mem_Icc.mp (hsub hx₂)
    have h4 := Finset.mem_Icc.mp (hsub hy₂)
    have hsum : x₁ + y₁ = x₂ + y₂ := by omega
    rcases hS x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩

/-- No Sidon subset of `{1, ..., 11}` has cardinality `≥ 5`. -/
private lemma sidon_Icc11_card_le_4 {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 11)
    (hS : IsSidon (A : Set ℕ)) : A.card ≤ 4 := by
  classical
  -- Step 1: Any Sidon `B ⊆ Icc 1 11` with `B.card ≥ 5` hits ALL 10 positive differences `1..10`
  have hdiff_all : ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 11 → IsSidon (B : Set ℕ) → 5 ≤ B.card →
      ∀ d ∈ Finset.Icc 1 10, ∃ a ∈ B, ∃ b ∈ B, b < a ∧ a - b = d := by
    intro B hBsub hBS hB5
    let P := B.offDiag.filter (fun p => p.2 < p.1)
    let D := P.image (fun p => p.1 - p.2)
    have hDsub : D ⊆ Finset.Icc 1 10 := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      have h1 := Finset.mem_Icc.mp (hBsub hp.1.1)
      have h2 := Finset.mem_Icc.mp (hBsub hp.1.2.1)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) (P : Set (ℕ × ℕ)) := by
      intro p hp q hq heq
      dsimp only at heq
      simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp hq
      have hsum : p.1 + q.2 = q.1 + p.2 := by omega
      rcases hBS p.1 hp.1.1 q.2 hq.1.2.1 q.1 hq.1.1 p.2 hp.1.2.1 hsum with ⟨h1, h2⟩ | ⟨_, _⟩
      · exact Prod.ext h1 h2.symm
      · omega
    have hPcard : 2 * P.card = B.offDiag.card := by
      have hunion : B.offDiag = P ∪ B.offDiag.filter (fun p => p.1 < p.2) := by
        ext p; simp only [P, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
        constructor
        · intro h; rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt
          · left; exact ⟨h, hlt⟩
          · exact False.elim (h.2.2 heq.symm)
          · right; exact ⟨h, hgt⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint P (B.offDiag.filter (fun p => p.1 < p.2)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P, Finset.mem_filter] at h1 h2; omega
      have hswap : (B.offDiag.filter (fun p => p.1 < p.2)).card = P.card := by
        refine Finset.card_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp
          simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
          exact ⟨⟨hp.1.2.1, hp.1.1, Ne.symm hp.1.2.2⟩, hp.2⟩
        · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro p hp
          simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
          refine ⟨(p.2, p.1), ?_, rfl⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag]
          exact ⟨⟨hp.1.2.1, hp.1.1, Ne.symm hp.1.2.2⟩, hp.2⟩
      conv_rhs => rw [hunion]
      rw [Finset.card_union_of_disjoint hdisj, hswap]; ring
    have hoff : B.offDiag.card + B.card = B.card * B.card := by
      have hle : B.card ≤ B.card * B.card := Nat.le_mul_self B.card
      rw [Finset.offDiag_card]; omega
    have hDcard : 10 ≤ D.card := by
      rw [Finset.card_image_of_injOn hinj]
      nlinarith
    have hDeq : D = Finset.Icc 1 10 :=
      Finset.eq_of_subset_of_card_le hDsub (by rw [show (Finset.Icc 1 10).card = 10 by decide]; exact hDcard)
    intro d hd
    rw [← hDeq] at hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    simp only [P, Finset.mem_filter, Finset.mem_offDiag] at hp
    exact ⟨p.1, hp.1.1, p.2, hp.1.2.1, hp.2, rfl⟩
  -- Step 2: Eliminate the `1, 2, 11 ∈ B` case directly
  have hno_1211 : ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 11 → IsSidon (B : Set ℕ) → 5 ≤ B.card →
      1 ∈ B → 2 ∈ B → 11 ∈ B → False := by
    intro B hBsub hBS hB5 h1 h2 h11
    -- Difference 8 must occur -> forces `9 ∈ B`
    obtain ⟨a, ha, b, hb, hba, hdiff8⟩ := hdiff_all B hBsub hBS hB5 8 (by decide)
    have haI := Finset.mem_Icc.mp (hBsub ha)
    have hbI := Finset.mem_Icc.mp (hBsub hb)
    have h9 : 9 ∈ B := by
      have hcases : (a = 9 ∧ b = 1) ∨ (a = 10 ∧ b = 2) ∨ (a = 11 ∧ b = 3) := by omega
      rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨_, rfl⟩
      · exact ha
      · have := hBS 1 h1 11 h11 2 h2 10 ha (by omega); omega
      · have := hBS 1 h1 3 hb 2 h2 2 h2 (by omega); omega
    -- Now `{1, 2, 9, 11} ⊆ B` has card 4, so there exists `x ∈ B \ {1, 2, 9, 11}` with `3 ≤ x ≤ 8`
    have hsub4 : ({1, 2, 9, 11} : Finset ℕ) ⊆ B := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hne : (B \ {1, 2, 9, 11}).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hBsub4 : B ⊆ {1, 2, 9, 11} := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have hle4 : B.card ≤ ({1, 2, 9, 11} : Finset ℕ).card := Finset.card_le_card hBsub4
      have hc4 : ({1, 2, 9, 11} : Finset ℕ).card = 4 := by decide
      omega
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_sdiff] at hx
    have hxI := Finset.mem_Icc.mp (hBsub hx.1)
    have hxnot : x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 9 ∧ x ≠ 11 := by
      have := hx.2; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at this; exact this
    have hxlo : 3 ≤ x := by omega
    have hxhi : x ≤ 10 := by omega
    interval_cases x
    · have := hBS 1 h1 3 hx.1 2 h2 2 h2 (by omega); omega
    · have := hBS 2 h2 11 h11 4 hx.1 9 h9 (by omega); omega
    · have := hBS 1 h1 9 h9 5 hx.1 5 hx.1 (by omega); omega
    · have := hBS 1 h1 11 h11 6 hx.1 6 hx.1 (by omega); omega
    · have := hBS 7 hx.1 11 h11 9 h9 9 h9 (by omega); omega
    · have := hBS 1 h1 9 h9 2 h2 8 hx.1 (by omega); omega
    · exact False.elim (hxnot.2.2.1 rfl)
    · have := hBS 1 h1 11 h11 2 h2 10 hx.1 (by omega); omega
  -- Step 3: Suppose `5 ≤ A.card`; difference 10 forces `1, 11 ∈ A` and difference 9 forces `2 ∈ A ∨ 10 ∈ A`
  by_contra hgt
  push Not at hgt
  obtain ⟨a10, ha10, b10, hb10, hba10, hd10⟩ := hdiff_all A hsub hS hgt 10 (by decide)
  have ha10I := Finset.mem_Icc.mp (hsub ha10)
  have hb10I := Finset.mem_Icc.mp (hsub hb10)
  have h1A : 1 ∈ A := by
    have hb1 : b10 = 1 := by omega
    rwa [← hb1]
  have h11A : 11 ∈ A := by
    have ha11 : a10 = 11 := by omega
    rwa [← ha11]
  obtain ⟨a9, ha9, b9, hb9, hba9, hd9⟩ := hdiff_all A hsub hS hgt 9 (by decide)
  have ha9I := Finset.mem_Icc.mp (hsub ha9)
  have hb9I := Finset.mem_Icc.mp (hsub hb9)
  have h2or10 : 2 ∈ A ∨ 10 ∈ A := by
    have hcases : (a9 = 10 ∧ b9 = 1) ∨ (a9 = 11 ∧ b9 = 2) := by omega
    rcases hcases with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · right; exact ha9
    · left; exact hb9
  rcases h2or10 with h2A | h10A
  · exact hno_1211 A hsub hS hgt h1A h2A h11A
  · obtain ⟨hsub', hcard', hS'⟩ := sidon_reflect_11 hsub hS
    have h1' : 1 ∈ A.image (fun x => 12 - x) := Finset.mem_image.mpr ⟨11, h11A, by decide⟩
    have h2' : 2 ∈ A.image (fun x => 12 - x) := Finset.mem_image.mpr ⟨10, h10A, by decide⟩
    have h11' : 11 ∈ A.image (fun x => 12 - x) := Finset.mem_image.mpr ⟨1, h1A, by decide⟩
    exact hno_1211 _ hsub' hS' (by omega) h1' h2' h11'

/-- Exact evaluation `h(11) = 4` (attained by `{1, 2, 5, 11}`). -/
theorem h_11_eq_4 : h 11 = 4 := by
  classical
  have hle : h 11 ≤ 4 := by
    unfold h maxSidonSubsetCard
    refine Finset.sup_le fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    exact sidon_Icc11_card_le_4 hA.1 hA.2
  have hge : 4 ≤ h 11 := by
    let A : Finset ℕ := {1, 2, 5, 11}
    have hsub : A ⊆ Finset.Icc 1 11 := by decide
    have hS : IsSidon (A : Set ℕ) := by
      intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
      simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha₁ hb₁ ha₂ hb₂
      rcases ha₁ with rfl | rfl | rfl | rfl <;>
        rcases hb₁ with rfl | rfl | rfl | rfl <;>
        rcases ha₂ with rfl | rfl | rfl | rfl <;>
        rcases hb₂ with rfl | rfl | rfl | rfl <;> omega
    have hmem : A ∈ (Finset.Icc 1 11).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hS⟩
    have hc : A.card = 4 := by decide
    rw [← hc]
    exact Finset.le_sup (f := Finset.card) hmem
  omega

/-- Theorem T2-C (Core): Strict Nonlinear `M_3AP` Separation at `N = 11`:
`h(11) = 4 < 3√2`, while `μ = (1/√2) 1_{0, 1, 3, 7, 9, 10}` is a feasible fractional Sidon
measure on `{0, ..., 10}` that is strictly 3-AP-free (`Is3APFreeMeasure 11 μ`) with
`∑_{x < 11} μ x = 3√2`. -/
theorem strict_separation_h11_lt_m3ap_core :
    h 11 = 4 ∧ (h 11 : ℝ) < 3 * Real.sqrt 2 ∧
    ∃ μ : ℕ → ℝ,
      (∀ x, x < 11 → 0 ≤ μ x ∧ μ x ≤ 1) ∧
      (∀ d, 1 ≤ d → d < 11 → ∑ x ∈ Finset.range (11 - d), μ x * μ (x + d) ≤ 1) ∧
      Is3APFreeMeasure 11 μ ∧
      ∑ x ∈ Finset.range 11, μ x = 3 * Real.sqrt 2 := by
  have hh11 : h 11 = 4 := h_11_eq_4
  have hlt : (h 11 : ℝ) < 3 * Real.sqrt 2 := by
    rw [hh11]
    push_cast
    have hsq : (4 : ℝ) ^ 2 < (3 * Real.sqrt 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  refine ⟨hh11, hlt, ?_⟩
  let B : Finset ℕ := {0, 1, 3, 7, 9, 10}
  let μ : ℕ → ℝ := fun x => if x ∈ B then 1 / Real.sqrt 2 else 0
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_le1 : 1 / Real.sqrt 2 ≤ 1 := (div_le_one hs2_pos).mpr hs2_ge1
  have hmul_half : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 : ℝ) / 2 := by
    rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
  refine ⟨μ, ?_, ?_, ?_, ?_⟩
  · intro x _
    dsimp only [μ]
    split_ifs
    · exact ⟨by positivity, hinv_le1⟩
    · exact ⟨le_refl 0, by norm_num⟩
  · intro d hd1 hd11
    have hcount : ∀ d, 1 ≤ d → d < 11 →
        ((Finset.range (11 - d)).filter (fun x => x ∈ B ∧ x + d ∈ B)).card ≤ 2 := by
      intro d' h1 h11
      interval_cases d' <;> decide
    have hsum_eq : ∑ x ∈ Finset.range (11 - d), μ x * μ (x + d) =
        (((Finset.range (11 - d)).filter (fun x => x ∈ B ∧ x + d ∈ B)).card : ℝ) * ((1 : ℝ) / 2) := by
      have hterm : ∀ x ∈ Finset.range (11 - d),
          μ x * μ (x + d) = if x ∈ B ∧ x + d ∈ B then (1 : ℝ) / 2 else 0 := by
        intro x _
        dsimp only [μ]
        by_cases hx : x ∈ B <;> by_cases hxd : x + d ∈ B
        · simp only [hx, hxd, and_self, ↓reduceIte, hmul_half]
        · simp [hx, hxd]
        · simp [hx, hxd]
        · simp [hx, hxd]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_eq]
    have hcR : (((Finset.range (11 - d)).filter (fun x => x ∈ B ∧ x + d ∈ B)).card : ℝ) ≤ 2 := by
      exact_mod_cast hcount d hd1 hd11
    linarith
  · intro a b c hab hbc _ hap
    by_cases ha : a ∈ B
    · by_cases hb : b ∈ B
      · by_cases hc : c ∈ B
        · exfalso
          simp only [B, Finset.mem_insert, Finset.mem_singleton] at ha hb hc
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
        · simp [μ, hc]
      · simp [μ, hb]
    · simp [μ, ha]
  · have hsum_eq : ∑ x ∈ Finset.range 11, μ x = (B.card : ℝ) * (1 / Real.sqrt 2) := by
      have hsubB : B ⊆ Finset.range 11 := by decide
      rw [← Finset.sum_subset hsubB]
      · have : ∀ x ∈ B, μ x = 1 / Real.sqrt 2 := fun x hx => by simp [μ, hx]
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      · intro x _ hx; simp [μ, hx]
    rw [hsum_eq, show (B.card : ℝ) = 6 by norm_num [B]]
    have h6 : (6 : ℝ) * (1 / Real.sqrt 2) = 3 * Real.sqrt 2 := by
      field_simp [hs2_pos.ne']
      rw [Real.sq_sqrt (by norm_num)]; ring
    exact h6

/-! ### Part 2: Theorem T2-A — Exact Mod-`q` Equidistribution & Residue-Class Collapse -/

/-- Elementary triangle sum identity:
`2 * ∑_{1 ≤ k < m} (m * q - k * q) = q * m * (m - 1)`. -/
private lemma two_mul_sum_mod_lags (q m : ℕ) (hm : 1 ≤ m) :
    2 * ∑ k ∈ Finset.Ico 1 m, ((m * q - k * q : ℕ) : ℝ) =
      (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1) := by
  induction m with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; simp
    · have hn1 : 1 ≤ n := by omega
      have hih := ih hn1
      rw [Finset.sum_Ico_succ_top hn1]
      have hlast : ((n + 1) * q - n * q : ℕ) = q := by
        have : (n + 1) * q = n * q + q := by ring
        omega
      have hshift : ∑ k ∈ Finset.Ico 1 n, (((n + 1) * q - k * q : ℕ) : ℝ) =
          (∑ k ∈ Finset.Ico 1 n, ((n * q - k * q : ℕ) : ℝ)) + ((n - 1 : ℕ) : ℝ) * (q : ℝ) := by
        have hstep : ∀ k ∈ Finset.Ico 1 n,
            (((n + 1) * q - k * q : ℕ) : ℝ) = ((n * q - k * q : ℕ) : ℝ) + (q : ℝ) := by
          intro k hk
          rw [Finset.mem_Ico] at hk
          have h1 : (n + 1) * q - k * q = (n * q - k * q) + q := by
            have hle : k * q ≤ n * q := Nat.mul_le_mul_right q hk.2.le
            have hmul : (n + 1) * q = n * q + q := by ring
            omega
          rw [h1, Nat.cast_add]
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
          nsmul_eq_mul]
      rw [hlast, hshift]
      have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn1, Nat.cast_one]
      rw [hn1_cast, Nat.cast_succ]
      linarith

/-- Unified Exact Mod-`q` Equidistribution Theorem (purely real, zero complex numbers):
For ALL `N, q, m ≥ 1` (`H = m * q`), any measure `μ : ℕ → ℝ`, and any symmetric matrix
`X : ℕ → ℕ → ℝ` with diagonal sum `≤ E`, exact pointwise Sidon off-diagonal sums `≤ 1`,
and window-square domination on residue-`r` intervals of length `H`, setting
`S_r = ∑_{y < N, y % q = r} μ y`:
`q * ∑_{r < q} S_r^2 ≤ (N + m * q - 1) * (1 + (E - 1) / m)`.

Covers BOTH `IsFractionalSidon N μ` (with `X y z = μ y * μ z`, `E = ∑ μ_y^2`) AND
`IsSDP1Feasible N μ X` (with `E = ∑ μ_y`). -/
theorem matrix_mod_q_equidistribution {N q m : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hm : 1 ≤ m)
    {μ : ℕ → ℝ} {X : ℕ → ℕ → ℝ} {E : ℝ}
    (hX_symm : ∀ i, i < N → ∀ j, j < N → X i j = X j i)
    (hX_diag : ∑ i ∈ Finset.range N, X i i ≤ E)
    (hX_off : ∀ d, 1 ≤ d → d < N → ∑ i ∈ Finset.range (N - d), X i (i + d) ≤ 1)
    (hdom : ∀ r < q, ∀ x < N + m * q - 1,
      (∑ y ∈ (Finset.range N).filter (fun y => y % q = r ∧ y ≤ x ∧ x < y + m * q), μ y) ^ 2 ≤
      ∑ y ∈ (Finset.range N).filter (fun y => y % q = r ∧ y ≤ x ∧ x < y + m * q),
        ∑ z ∈ (Finset.range N).filter (fun z => z % q = r ∧ z ≤ x ∧ x < z + m * q), X y z) :
    (q : ℝ) * ∑ r ∈ Finset.range q,
        (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 ≤
      ((N + m * q - 1 : ℕ) : ℝ) * (1 + (E - 1) / (m : ℝ)) := by
  classical
  set H : ℕ := m * q
  have hH_pos : 1 ≤ H := Nat.mul_pos hm hq
  have hH_posR : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH_pos
  have hq_posR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hm_posR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  let W : ℕ → ℕ → Finset ℕ := fun r x =>
    (Finset.range N).filter (fun y => y % q = r ∧ y ≤ x ∧ x < y + H)
  let S : ℕ → ℝ := fun r => ∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y
  -- Step 1: For each `r < q`, `∑_{x < N+H-1} C_r(x) = H * S_r`
  have hsum_C : ∀ r < q, ∑ x ∈ Finset.range (N + H - 1), (∑ y ∈ W r x, μ y) = (H : ℝ) * S r := by
    intro r _
    have hrew : ∑ x ∈ Finset.range (N + H - 1), (∑ y ∈ W r x, μ y) =
        ∑ x ∈ Finset.range (N + H - 1),
          ∑ y ∈ (Finset.range N).filter (fun y => y % q = r),
            if y ≤ x ∧ x < y + H then μ y else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_filter]
      congr 1; ext y; simp only [W, Finset.mem_filter]; tauto
    rw [hrew, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hy
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hfil : (Finset.range (N + H - 1)).filter (fun x => y ≤ x ∧ x < y + H) =
        Finset.Ico y (y + H) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfil, Nat.card_Ico, show y + H - y = H by omega]
  -- Step 2: Cauchy-Schwarz on each residue class `r < q`, then sum over `r < q`
  have hcs_all :
      (H : ℝ) ^ 2 * ∑ r ∈ Finset.range q, (S r) ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) *
        ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1),
          ∑ y ∈ W r x, ∑ z ∈ W r x, X y z := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun r hr => ?_
    have hrq := Finset.mem_range.mp hr
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
      (fun _ => (1 : ℝ)) (fun x => ∑ y ∈ W r x, μ y)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    rw [hsum_C r hrq, mul_pow] at hcs
    have hdom_sum : ∑ x ∈ Finset.range (N + H - 1), (∑ y ∈ W r x, μ y) ^ 2 ≤
        ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z :=
      Finset.sum_le_sum fun x hx => hdom r hrq x (Finset.mem_range.mp hx)
    exact hcs.trans (mul_le_mul_of_nonneg_left hdom_sum (Nat.cast_nonneg _))
  -- Step 3: Swap sums and count exact appearances of each pair `(y, z) ∈ range N ×ˢ range N`
  have hquad_eval :
      ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z =
      (H : ℝ) * (∑ y ∈ Finset.range N, X y y) +
      2 * ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N),
        ((H - k * q : ℕ) : ℝ) * ∑ y ∈ Finset.range (N - k * q), X y (y + k * q) := by
    -- Express inner double sum via indicator over `range N ×ˢ range N`
    have hstep1 :
        ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z =
        ∑ p ∈ Finset.range N ×ˢ Finset.range N,
          if p.1 % q = p.2 % q then
            ((min (p.1 + H) (p.2 + H) - max p.1 p.2 : ℕ) : ℝ) * X p.1 p.2
          else 0 := by
      have hinner : ∀ r ∈ Finset.range q, ∀ x ∈ Finset.range (N + H - 1),
          ∑ y ∈ W r x, ∑ z ∈ W r x, X y z =
          ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            if p.1 % q = r ∧ p.2 % q = r ∧ p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H
            then X p.1 p.2 else 0 := by
        intro r _ x _
        rw [← Finset.sum_product']
        rw [← Finset.sum_filter]
        congr 1; ext ⟨y, z⟩
        simp only [W, Finset.mem_product, Finset.mem_filter, Finset.mem_range]; tauto
      have h1 :
          ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z =
          ∑ p ∈ Finset.range N ×ˢ Finset.range N,
            ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1),
              if p.1 % q = r ∧ p.2 % q = r ∧ p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H
              then X p.1 p.2 else 0 := by
        calc ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z
            = ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1),
                ∑ p ∈ Finset.range N ×ˢ Finset.range N,
                  if p.1 % q = r ∧ p.2 % q = r ∧ p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H
                  then X p.1 p.2 else 0 :=
              Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun x hx => hinner r hr x hx
          _ = ∑ p ∈ Finset.range N ×ˢ Finset.range N,
                ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1),
                  if p.1 % q = r ∧ p.2 % q = r ∧ p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H
                  then X p.1 p.2 else 0 := by
              rw [Finset.sum_comm]
              conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
      rw [h1]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rcases hp with ⟨hp1, hp2⟩
      by_cases hmod : p.1 % q = p.2 % q
      · simp only [hmod, ↓reduceIte]
        rw [Finset.sum_eq_single (p.2 % q)]
        · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 2
          have hfil :
              (Finset.range (N + H - 1)).filter
                (fun x => p.2 % q = p.2 % q ∧ p.2 % q = p.2 % q ∧
                  p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H) =
              Finset.Ico (max p.1 p.2) (min (p.1 + H) (p.2 + H)) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, max_le_iff, lt_min_iff,
              true_and]
            have hbound1 : p.1 + H ≤ N + H - 1 := by omega
            have hbound2 : p.2 + H ≤ N + H - 1 := by omega
            omega
          rw [hfil, Nat.card_Ico]
        · intro r _ hrne
          refine Finset.sum_eq_zero fun x _ => ?_
          simp [hrne.symm]
        · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.mod_lt p.2 hq)))
      · simp only [hmod, ↓reduceIte]
        refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun x _ => ?_
        have hfalse : ¬ (p.1 % q = r ∧ p.2 % q = r ∧ p.1 ≤ x ∧ x < p.1 + H ∧ p.2 ≤ x ∧ x < p.2 + H) :=
          fun h => hmod (h.1.trans h.2.1.symm)
        simp [hfalse]
    rw [hstep1]
    -- Partition `range N ×ˢ range N` into `P0 (y = z)`, `Ppos (y < z)`, `Pneg (z < y)`
    let P := Finset.range N ×ˢ Finset.range N
    let P0 := P.filter (fun p => p.1 = p.2)
    let Ppos := P.filter (fun p => p.1 < p.2)
    let Pneg := P.filter (fun p => p.2 < p.1)
    let F : ℕ × ℕ → ℝ := fun p =>
      if p.1 % q = p.2 % q then ((min (p.1 + H) (p.2 + H) - max p.1 p.2 : ℕ) : ℝ) * X p.1 p.2 else 0
    have hpart : ∑ p ∈ P, F p = (∑ p ∈ P0, F p) + (∑ p ∈ Ppos, F p) + (∑ p ∈ Pneg, F p) := by
      have hunion : P = P0 ∪ Ppos ∪ Pneg := by
        ext ⟨i, j⟩
        simp only [P, P0, Ppos, Pneg, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_range]
        constructor
        · intro h; rcases lt_trichotomy i j with hlt | heq | hgt
          · left; right; exact ⟨h, hlt⟩
          · left; left; exact ⟨h, heq⟩
          · right; exact ⟨h, hgt⟩
        · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      have hd1 : Disjoint P0 Ppos := by
        rw [Finset.disjoint_left]; intro p h1 h2; simp only [P0, Ppos, Finset.mem_filter] at h1 h2; omega
      have hd2 : Disjoint (P0 ∪ Ppos) Pneg := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P0, Ppos, Pneg, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
      rw [hunion, Finset.sum_union hd2, Finset.sum_union hd1]
    have hP0 : ∑ p ∈ P0, F p = (H : ℝ) * ∑ y ∈ Finset.range N, X y y := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij (fun p => p.1) ?_ ?_ ?_ ?_
      · intro p hp; simp only [P0, P, Finset.mem_filter, Finset.mem_product] at hp ⊢; exact hp.1.1
      · intro p hp q' hq' heq
        dsimp only at heq; simp only [P0, Finset.mem_coe, Finset.mem_filter] at hp hq'
        exact Prod.ext heq (by omega)
      · intro y hy
        refine ⟨(y, y), ?_, rfl⟩
        simp only [P0, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hy ⊢
        exact ⟨⟨hy, hy⟩, trivial⟩
      · intro p hp
        simp only [P0, Finset.mem_filter] at hp
        dsimp only [F]
        rw [hp.2]
        simp [show p.2 + H - p.2 = H by omega]
    have hPneg : ∑ p ∈ Pneg, F p = ∑ p ∈ Ppos, F p := by
      refine Finset.sum_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Pneg, Ppos, P, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p _ q' _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp
        simp only [Pneg, Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
        refine ⟨(p.2, p.1), ?_, rfl⟩
        simp only [Pneg, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p hp
        simp only [Pneg, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        dsimp only [F]
        rw [hX_symm p.1 hp.1.1 p.2 hp.1.2, min_comm, max_comm]
        by_cases hm' : p.1 % q = p.2 % q
        · rw [if_pos hm', if_pos hm'.symm]
        · rw [if_neg hm', if_neg (Ne.symm hm')]
    have hPpos : ∑ p ∈ Ppos, F p =
        ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N),
          ((H - k * q : ℕ) : ℝ) * ∑ y ∈ Finset.range (N - k * q), X y (y + k * q) := by
      let Pgood := Ppos.filter (fun p => p.1 % q = p.2 % q ∧ p.2 - p.1 < H)
      have hfil : ∑ p ∈ Ppos, F p = ∑ p ∈ Pgood, ((H - (p.2 - p.1) : ℕ) : ℝ) * X p.1 p.2 := by
        rw [← Finset.sum_subset (Finset.filter_subset (fun p : ℕ × ℕ => p.1 % q = p.2 % q ∧ p.2 - p.1 < H) Ppos)]
        · refine Finset.sum_congr rfl fun p hp => ?_
          simp only [Pgood, Ppos, Finset.mem_filter] at hp
          dsimp only [F]
          simp only [hp.2.1, ↓reduceIte]
          congr 2
          omega
        · intro p hp hnot
          have hp_lt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
          simp only [Pgood, Finset.mem_filter] at hnot
          dsimp only [F]
          by_cases hmod : p.1 % q = p.2 % q
          · have hge : H ≤ p.2 - p.1 := by
              by_contra hlt; push Not at hlt; exact hnot ⟨hp, hmod, hlt⟩
            simp only [hmod, ↓reduceIte]
            have h0 : min (p.1 + H) (p.2 + H) - max p.1 p.2 = 0 := by omega
            rw [h0, Nat.cast_zero, zero_mul]
          · simp [hmod]
      rw [hfil]
      have hsig :
          ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N),
            ((H - k * q : ℕ) : ℝ) * ∑ y ∈ Finset.range (N - k * q), X y (y + k * q) =
          ∑ x ∈ ((Finset.Ico 1 m).filter (fun k => k * q < N)).sigma
              (fun k => Finset.range (N - k * q)),
            ((H - x.1 * q : ℕ) : ℝ) * X x.2 (x.2 + x.1 * q) := by
        symm
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl fun k _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
      rw [hsig]
      refine Finset.sum_nbij (fun p => ⟨(p.2 - p.1) / q, p.1⟩) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Pgood, Ppos, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_sigma, Finset.mem_Ico] at hp ⊢
        rcases hp with ⟨⟨⟨h1, h2⟩, hlt⟩, hmod, hdiff⟩
        have hdvd : q ∣ (p.2 - p.1) := by
          have hsub : p.2 - p.1 + p.1 = p.2 := by omega
          have h1' := Nat.div_add_mod p.1 q
          have h2' := Nat.div_add_mod p.2 q
          refine ⟨p.2 / q - p.1 / q, ?_⟩
          have hle_div : p.1 / q ≤ p.2 / q := Nat.div_le_div_right hlt.le
          have hmul : q * (p.2 / q - p.1 / q) = q * (p.2 / q) - q * (p.1 / q) :=
            Nat.mul_sub_left_distrib q (p.2 / q) (p.1 / q)
          omega
        have hk_mul : (p.2 - p.1) / q * q = p.2 - p.1 := Nat.div_mul_cancel hdvd
        have hk1 : 1 ≤ (p.2 - p.1) / q := by
          by_contra h0; push Not at h0
          have hz : (p.2 - p.1) / q = 0 := Nat.lt_one_iff.mp h0
          rw [hz, zero_mul] at hk_mul; omega
        have hkm : (p.2 - p.1) / q < m := by
          have : (p.2 - p.1) / q * q < m * q := by dsimp only [H] at hdiff; omega
          exact Nat.lt_of_mul_lt_mul_right this
        exact ⟨⟨⟨hk1, hkm⟩, by omega⟩, by omega⟩
      · intro p hp q' hq' heq
        simp only [Pgood, Ppos, Finset.mem_coe, Finset.mem_filter] at hp hq'
        have h1 : (p.2 - p.1) / q = (q'.2 - q'.1) / q := congrArg Sigma.fst heq
        have h2 : p.1 = q'.1 := congrArg Sigma.snd heq
        have hdvd1 : q ∣ (p.2 - p.1) := by
          have := Nat.div_add_mod p.1 q; have := Nat.div_add_mod p.2 q
          refine ⟨p.2 / q - p.1 / q, ?_⟩
          have := Nat.mul_sub_left_distrib q (p.2 / q) (p.1 / q); omega
        have hdvd2 : q ∣ (q'.2 - q'.1) := by
          have := Nat.div_add_mod q'.1 q; have := Nat.div_add_mod q'.2 q
          refine ⟨q'.2 / q - q'.1 / q, ?_⟩
          have := Nat.mul_sub_left_distrib q (q'.2 / q) (q'.1 / q); omega
        have hm1 : (p.2 - p.1) / q * q = p.2 - p.1 := Nat.div_mul_cancel hdvd1
        have hm2 : (q'.2 - q'.1) / q * q = q'.2 - q'.1 := Nat.div_mul_cancel hdvd2
        rw [h1] at hm1
        exact Prod.ext h2 (by omega)
      · intro ⟨k, y⟩ hky
        simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ico,
          Finset.mem_range] at hky
        rcases hky with ⟨⟨⟨hk1, hkm⟩, hkN⟩, hy⟩
        refine ⟨(y, y + k * q), ?_, ?_⟩
        · simp only [Pgood, Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range]
          have hkq_pos : 0 < k * q := Nat.mul_pos hk1 hq
          have hkq_ltH : k * q < H := Nat.mul_lt_mul_of_pos_right hkm hq
          refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, ?_, by omega⟩
          rw [Nat.add_mul_mod_self_right]
        · simp only [Sigma.mk.inj_iff, heq_eq_eq, and_true]
          rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel k hq]
      · intro p hp
        simp only [Pgood, Ppos, Finset.mem_filter] at hp
        have hdvd : q ∣ (p.2 - p.1) := by
          have := Nat.div_add_mod p.1 q; have := Nat.div_add_mod p.2 q
          refine ⟨p.2 / q - p.1 / q, ?_⟩
          have := Nat.mul_sub_left_distrib q (p.2 / q) (p.1 / q); omega
        have hk_mul : (p.2 - p.1) / q * q = p.2 - p.1 := Nat.div_mul_cancel hdvd
        dsimp only
        rw [hk_mul, show p.1 + (p.2 - p.1) = p.2 by omega]
    change ∑ p ∈ P, F p = _
    rw [hpart, hP0, hPneg, hPpos]
    ring
  -- Step 4: Bound diagonal by `H * E` and off-diagonal by `q * m * (m - 1)`
  have hquad_le :
      ∑ r ∈ Finset.range q, ∑ x ∈ Finset.range (N + H - 1), ∑ y ∈ W r x, ∑ z ∈ W r x, X y z ≤
      (H : ℝ) * E + (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1) := by
    rw [hquad_eval]
    have hdiag : (H : ℝ) * ∑ y ∈ Finset.range N, X y y ≤ (H : ℝ) * E :=
      mul_le_mul_of_nonneg_left hX_diag hH_posR.le
    have hoff1 :
        ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N),
          ((H - k * q : ℕ) : ℝ) * ∑ y ∈ Finset.range (N - k * q), X y (y + k * q) ≤
        ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N), ((H - k * q : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_filter, Finset.mem_Ico] at hk
      have hkq1 : 1 ≤ k * q := Nat.mul_pos hk.1.1 hq
      have h1 := hX_off (k * q) hkq1 hk.2
      calc ((H - k * q : ℕ) : ℝ) * ∑ y ∈ Finset.range (N - k * q), X y (y + k * q)
          ≤ ((H - k * q : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = ((H - k * q : ℕ) : ℝ) := mul_one _
    have hoff2 :
        ∑ k ∈ (Finset.Ico 1 m).filter (fun k => k * q < N), ((H - k * q : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.Ico 1 m, ((H - k * q : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
    have hoff_eq := two_mul_sum_mod_lags q m hm
    linarith
  -- Step 5: Multiply by `q / H^2`
  have hcomb :
      (H : ℝ) ^ 2 * ∑ r ∈ Finset.range q, (S r) ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * E + (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1)) :=
    hcs_all.trans (mul_le_mul_of_nonneg_left hquad_le (Nat.cast_nonneg _))
  have hH_cast : (H : ℝ) = (m : ℝ) * (q : ℝ) := by dsimp only [H]; push_cast; rfl
  have hscale :
      (q : ℝ) * ((H : ℝ) * E + (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1)) =
      (H : ℝ) ^ 2 * (1 + (E - 1) / (m : ℝ)) := by
    rw [hH_cast]; field_simp [hm_posR.ne']; ring
  have hmul_q :
      (H : ℝ) ^ 2 * ((q : ℝ) * ∑ r ∈ Finset.range q, (S r) ^ 2) ≤
      (H : ℝ) ^ 2 * (((N + H - 1 : ℕ) : ℝ) * (1 + (E - 1) / (m : ℝ))) := by
    have h1 := mul_le_mul_of_nonneg_left hcomb hq_posR.le
    calc (H : ℝ) ^ 2 * ((q : ℝ) * ∑ r ∈ Finset.range q, (S r) ^ 2)
        = (q : ℝ) * ((H : ℝ) ^ 2 * ∑ r ∈ Finset.range q, (S r) ^ 2) := by ring
      _ ≤ (q : ℝ) * (((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) * E + (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1))) := h1
      _ = ((N + H - 1 : ℕ) : ℝ) * ((q : ℝ) * ((H : ℝ) * E + (q : ℝ) * (m : ℝ) * ((m : ℝ) - 1))) := by ring
      _ = ((N + H - 1 : ℕ) : ℝ) * ((H : ℝ) ^ 2 * (1 + (E - 1) / (m : ℝ))) := by rw [hscale]
      _ = (H : ℝ) ^ 2 * (((N + H - 1 : ℕ) : ℝ) * (1 + (E - 1) / (m : ℝ))) := by ring
  exact le_of_mul_le_mul_left hmul_q (sq_pos_of_pos hH_posR)

/-- Residue-class support collapse corollary:
If `supp(μ)` hits at most `k` residue classes mod `q` (contained in `R ⊆ range q` with `R.card ≤ k`),
then `(∑_{y < N} μ y)^2 ≤ k * ∑_{r < q} S_r^2`. -/
theorem mod_q_support_collapse_of_equidist {N q k : ℕ} (hq : 1 ≤ q)
    {μ : ℕ → ℝ} {R : Finset ℕ} (hR_sub : R ⊆ Finset.range q) (hR_card : R.card ≤ k)
    (hsupp : ∀ y, y < N → y % q ∉ R → μ y = 0) :
    (∑ y ∈ Finset.range N, μ y) ^ 2 ≤
      (k : ℝ) * ∑ r ∈ Finset.range q,
        (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 := by
  classical
  let S : ℕ → ℝ := fun r => ∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y
  have hsum_part : ∑ y ∈ Finset.range N, μ y = ∑ r ∈ R, S r := by
    have hfull : ∑ y ∈ Finset.range N, μ y = ∑ r ∈ Finset.range q, S r := by
      have hbi : ∑ r ∈ Finset.range q, S r =
          ∑ y ∈ Finset.range N, ∑ r ∈ Finset.range q, if y % q = r then μ y else 0 := by
        calc ∑ r ∈ Finset.range q, S r
            = ∑ r ∈ Finset.range q, ∑ y ∈ Finset.range N, if y % q = r then μ y else 0 :=
              Finset.sum_congr rfl fun r _ => Finset.sum_filter _ _
          _ = ∑ y ∈ Finset.range N, ∑ r ∈ Finset.range q, if y % q = r then μ y else 0 :=
              Finset.sum_comm
      rw [hbi]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single (y % q)]
      · simp
      · intro r _ hrne; simp [hrne.symm]
      · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.mod_lt y hq)))
    rw [hfull]
    symm
    refine Finset.sum_subset hR_sub fun r _ hrnot => ?_
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hy
    exact hsupp y hy.1 (by rwa [hy.2])
  rw [hsum_part]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq R (fun _ => (1 : ℝ)) S
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsub_le : ∑ r ∈ R, (S r) ^ 2 ≤ ∑ r ∈ Finset.range q, (S r) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hR_sub fun _ _ _ => sq_nonneg _
  have hcardR : (R.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hR_card
  have hsum_nn : 0 ≤ ∑ r ∈ Finset.range q, (S r) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (∑ r ∈ R, S r) ^ 2
      ≤ (R.card : ℝ) * ∑ r ∈ R, (S r) ^ 2 := hcs
    _ ≤ (R.card : ℝ) * ∑ r ∈ Finset.range q, (S r) ^ 2 :=
        mul_le_mul_of_nonneg_left hsub_le (Nat.cast_nonneg _)
    _ ≤ (k : ℝ) * ∑ r ∈ Finset.range q, (S r) ^ 2 :=
        mul_le_mul_of_nonneg_right hcardR hsum_nn

end Erdos030
