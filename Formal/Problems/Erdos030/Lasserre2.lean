import Problems.Erdos030.Statement
import Mathlib.Tactic

/-!
# Degree-2 Lasserre (SoS) Hierarchy for Erdős Problem #30 (Sidon Sets)

Formalizes the exact Degree-2 Lasserre moment relaxation `IsLasserre2Feasible` for Sidon sets
in `{0, ..., N - 1}` modulo the Boolean ideal (`x_i^2 = x_i`) and the degree-≤4 Sidon ideal
(`x_u = 0` for every non-Sidon subset `u` with `|u| ≤ 4`), together with:
1. Exact soundness for all Sidon sets (`sidon_indicator_lasserre2_feasible`,
   `exists_lasserre2_achieving_h`, `h_le_of_lasserre2_bound`).
2. General conflict-family clique cut (`lasserre2_conflict_family_le_one`), implying all
   exact pointwise Sidon off-diagonal constraints, all 3-AP cuts, and all 4-Sidon cuts.
3. Exact projection of Degree-2 Lasserre onto all Degree-1 Lasserre / Shor + RLT + McCormick
   conditions (`lasserre2_psd1`, `lasserre2_mccormick`, `lasserre2_sidon_offdiag`).
4. General Degree-2 Sum-of-Squares dual soundness certificate theorem (`lasserre2_dual_sos_bound`).
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-- Monomial basis of degree `≤ 2` for Boolean variables indexed by `Finset.range N`. -/
def monomBasis2 (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.range N).powerset.filter (fun I => I.card ≤ 2)

/-- All monomials of degree `≤ 4` on `Finset.range N`. -/
def monomBasis4 (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.range N).powerset.filter (fun u => u.card ≤ 4)

/-- Exact Degree-2 Lasserre feasibility predicate for Sidon sets in `{0, ..., N - 1}`:
a pseudo-expectation functional `y : Finset ℕ → ℝ` (defining the moment matrix
`M_2(I, J) = y (I ∪ J)` on `monomBasis2 N`) satisfying:
1. Normalization `y ∅ = 1`;
2. Degree-`≤ 4` Sidon ideal `y u = 0` for every non-Sidon subset `u ⊆ range N` with `|u| ≤ 4`;
3. Moment matrix positive semidefiniteness `M_2 ≽ 0`. -/
def IsLasserre2Feasible (N : ℕ) (y : Finset ℕ → ℝ) : Prop :=
  y ∅ = 1 ∧
  (∀ u : Finset ℕ, u ⊆ Finset.range N → u.card ≤ 4 → ¬ IsSidon (u : Set ℕ) → y u = 0) ∧
  (∀ c : Finset ℕ → ℝ,
    0 ≤ ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c I * c J * y (I ∪ J))

lemma empty_mem_monomBasis2 (N : ℕ) : (∅ : Finset ℕ) ∈ monomBasis2 N := by
  simp [monomBasis2]

lemma singleton_mem_monomBasis2 {N i : ℕ} (hi : i < N) : ({i} : Finset ℕ) ∈ monomBasis2 N := by
  simp [monomBasis2, hi]

lemma pair_mem_monomBasis2 {N i j : ℕ} (hi : i < N) (hj : j < N) :
    ({i, j} : Finset ℕ) ∈ monomBasis2 N := by
  rw [monomBasis2, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, Finset.card_le_two⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)

lemma union_mem_monomBasis4 {N : ℕ} {I J : Finset ℕ}
    (hI : I ∈ monomBasis2 N) (hJ : J ∈ monomBasis2 N) :
    I ∪ J ∈ monomBasis4 N := by
  rw [monomBasis2, Finset.mem_filter, Finset.mem_powerset] at hI hJ
  rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.union_subset hI.1 hJ.1, ?_⟩
  exact (Finset.card_union_le I J).trans (by omega)

/-- Any subset of a Sidon set is a Sidon set. -/
lemma isSidon_subset {A B : Finset ℕ} (hsub : B ⊆ A) (hA : IsSidon (A : Set ℕ)) :
    IsSidon (B : Set ℕ) := by
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
  exact hA a₁ (hsub ha₁) b₁ (hsub hb₁) a₂ (hsub ha₂) b₂ (hsub hb₂) heq

/-- Every Sidon set `A ⊆ range N` defines a rank-1 Degree-2 Lasserre feasible moment functional
`y u = if u ⊆ A then 1 else 0` with objective `∑_{i < N} y {i} = A.card`. -/
theorem sidon_indicator_lasserre2_feasible {N : ℕ} {A : Finset ℕ}
    (hA_sub : A ⊆ Finset.range N) (hA_sidon : IsSidon (A : Set ℕ)) :
    let y : Finset ℕ → ℝ := fun u => if u ⊆ A then (1 : ℝ) else 0
    IsLasserre2Feasible N y ∧ ∑ i ∈ Finset.range N, y {i} = (A.card : ℝ) := by
  classical
  intro y
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [y]
  · intro u _ _ hnot
    dsimp only [y]
    rw [if_neg]
    intro hsub
    exact hnot (isSidon_subset hsub hA_sidon)
  · intro c
    have hfactor :
        ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c I * c J * y (I ∪ J) =
        (∑ I ∈ monomBasis2 N, if I ⊆ A then c I else 0) ^ 2 := by
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun J _ => ?_
      dsimp only [y]
      by_cases hI : I ⊆ A <;> by_cases hJ : J ⊆ A
      · rw [if_pos (Finset.union_subset hI hJ), if_pos hI, if_pos hJ, mul_one]
      · have hnot : ¬ (I ∪ J ⊆ A) := fun h => hJ (Finset.subset_union_right.trans h)
        rw [if_neg hnot, if_pos hI, if_neg hJ, mul_zero, mul_zero]
      · have hnot : ¬ (I ∪ J ⊆ A) := fun h => hI (Finset.subset_union_left.trans h)
        rw [if_neg hnot, if_neg hI, if_pos hJ, mul_zero, zero_mul]
      · have hnot : ¬ (I ∪ J ⊆ A) := fun h => hI (Finset.subset_union_left.trans h)
        rw [if_neg hnot, if_neg hI, if_neg hJ, mul_zero, zero_mul]
    rw [hfactor]
    exact sq_nonneg _
  · have hsum : ∑ i ∈ Finset.range N, y {i} = ∑ i ∈ Finset.range N, if i ∈ A then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [y]
    rw [hsum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfil : (Finset.range N).filter (fun i => i ∈ A) = A := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hi => ⟨hA_sub hi, hi⟩⟩
    rw [hfil]

/-- For every `N`, there exists a Degree-2 Lasserre feasible functional achieving objective `h N`. -/
theorem exists_lasserre2_achieving_h (N : ℕ) :
    ∃ y : Finset ℕ → ℝ, IsLasserre2Feasible N y ∧ ∑ i ∈ Finset.range N, y {i} = (h N : ℝ) := by
  classical
  let F := (Finset.Icc 1 N).powerset.filter (fun A : Finset ℕ => IsSidon (A : Set ℕ))
  have hne : F.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro a₁ ha₁; simp at ha₁
  obtain ⟨A, hAF, hAmax⟩ := Finset.exists_mem_eq_sup F hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hAF
  rcases hAF with ⟨hA_sub, hA_sidon⟩
  have hA_card : A.card = h N := by
    unfold h maxSidonSubsetCard
    simpa [F] using hAmax.symm
  let A' : Finset ℕ := A.image (fun x => x - 1)
  have hA'_sub : A' ⊆ Finset.range N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxI := Finset.mem_Icc.mp (hA_sub hx)
    exact Finset.mem_range.mpr (by omega)
  have hA'_card : A'.card = A.card := by
    refine Finset.card_image_of_injOn ?_
    intro x₁ hx₁ x₂ hx₂ heq
    have h1 := Finset.mem_Icc.mp (hA_sub hx₁)
    have h2 := Finset.mem_Icc.mp (hA_sub hx₂)
    dsimp only at heq
    omega
  have hA'_sidon : IsSidon (A' : Set ℕ) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
    simp only [A', Finset.mem_coe, Finset.mem_image] at ha₁ hb₁ ha₂ hb₂
    rcases ha₁ with ⟨x₁, hx₁, rfl⟩
    rcases hb₁ with ⟨y₁, hy₁, rfl⟩
    rcases ha₂ with ⟨x₂, hx₂, rfl⟩
    rcases hb₂ with ⟨y₂, hy₂, rfl⟩
    have h1 := Finset.mem_Icc.mp (hA_sub hx₁)
    have h2 := Finset.mem_Icc.mp (hA_sub hy₁)
    have h3 := Finset.mem_Icc.mp (hA_sub hx₂)
    have h4 := Finset.mem_Icc.mp (hA_sub hy₂)
    have hsum : x₁ + y₁ = x₂ + y₂ := by omega
    rcases hA_sidon x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  obtain ⟨hfeas, hobj⟩ := sidon_indicator_lasserre2_feasible hA'_sub hA'_sidon
  refine ⟨fun u => if u ⊆ A' then (1 : ℝ) else 0, hfeas, ?_⟩
  rw [hobj, hA'_card, hA_card]

/-- Any uniform upper bound on Degree-2 Lasserre immediately upper-bounds `h N`. -/
theorem h_le_of_lasserre2_bound {N : ℕ} {C : ℝ}
    (hbound : ∀ y : Finset ℕ → ℝ, IsLasserre2Feasible N y → ∑ i ∈ Finset.range N, y {i} ≤ C) :
    (h N : ℝ) ≤ C := by
  obtain ⟨y, hy, hobj⟩ := exists_lasserre2_achieving_h N
  rw [← hobj]
  exact hbound y hy

/-- Restricting the Degree-2 PSD quadratic form to any subset `S ⊆ monomBasis2 N`. -/
lemma lasserre2_quad_nonneg_of_support {N : ℕ} {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) {S : Finset (Finset ℕ)} (hS : S ⊆ monomBasis2 N)
    (c : Finset ℕ → ℝ) :
    0 ≤ ∑ I ∈ S, ∑ J ∈ S, c I * c J * y (I ∪ J) := by
  classical
  let c' : Finset ℕ → ℝ := fun I => if I ∈ S then c I else 0
  have hpsd := hy.2.2 c'
  have heq :
      ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c' I * c' J * y (I ∪ J) =
      ∑ I ∈ S, ∑ J ∈ S, c I * c J * y (I ∪ J) := by
    rw [← Finset.sum_subset hS]
    · refine Finset.sum_congr rfl fun I hI => ?_
      rw [← Finset.sum_subset hS]
      · refine Finset.sum_congr rfl fun J hJ => ?_
        simp only [c', if_pos hI, if_pos hJ]
      · intro J _ hJn
        simp only [c', if_neg hJn, mul_zero, zero_mul]
    · intro I _ hIn
      refine Finset.sum_eq_zero fun J _ => ?_
      simp only [c', if_neg hIn, zero_mul]
  rwa [heq] at hpsd

/-- Every degree-`≤ 2` monomial has nonnegative pseudo-expectation `y I ≥ 0`. -/
lemma lasserre2_nonneg_monom {N : ℕ} {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) {I : Finset ℕ} (hI : I ∈ monomBasis2 N) :
    0 ≤ y I := by
  have hS : ({I} : Finset (Finset ℕ)) ⊆ monomBasis2 N := Finset.singleton_subset_iff.mpr hI
  have hq := lasserre2_quad_nonneg_of_support hy hS (fun _ => 1)
  simpa using hq

/-- General Conflict-Family Clique Cut for Degree-2 Lasserre:
for ANY family `F ⊆ monomBasis2 N` not containing `∅` whose pairwise distinct unions are all
non-Sidon, `∑ I ∈ F, y I ≤ 1`.
This single lemma implies all exact pairwise Sidon constraints, all 3-AP cuts, and all 4-Sidon cuts. -/
theorem lasserre2_conflict_family_le_one {N : ℕ} {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) {F : Finset (Finset ℕ)}
    (hF_sub : F ⊆ monomBasis2 N) (hF_ne : (∅ : Finset ℕ) ∉ F)
    (hconflict : ∀ I ∈ F, ∀ J ∈ F, I ≠ J → ¬ IsSidon ((I ∪ J : Finset ℕ) : Set ℕ)) :
    ∑ I ∈ F, y I ≤ 1 := by
  classical
  let S : Finset (Finset ℕ) := insert ∅ F
  have hS : S ⊆ monomBasis2 N := Finset.insert_subset (empty_mem_monomBasis2 N) hF_sub
  let c : Finset ℕ → ℝ := fun I => if I = ∅ then 1 else -1
  have hq := lasserre2_quad_nonneg_of_support hy hS c
  have hexpand :
      ∑ I ∈ S, ∑ J ∈ S, c I * c J * y (I ∪ J) = 1 - ∑ I ∈ F, y I := by
    rw [Finset.sum_insert hF_ne]
    have hrow0 : ∑ J ∈ S, c ∅ * c J * y (∅ ∪ J) = 1 - ∑ J ∈ F, y J := by
      rw [Finset.sum_insert hF_ne]
      have h00 : c ∅ * c ∅ * y (∅ ∪ ∅) = 1 := by simp [c, hy.1]
      have h0F : ∑ J ∈ F, c ∅ * c J * y (∅ ∪ J) = - ∑ J ∈ F, y J := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun J hJ => ?_
        have hJne : J ≠ ∅ := fun h => hF_ne (h ▸ hJ)
        simp [c, hJne]
      rw [h00, h0F]; ring
    have hrowsF : ∑ I ∈ F, ∑ J ∈ S, c I * c J * y (I ∪ J) = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      have hIne : I ≠ ∅ := fun h => hF_ne (h ▸ hI)
      rw [Finset.sum_insert hF_ne]
      have hI0 : c I * c ∅ * y (I ∪ ∅) = - y I := by simp [c, hIne]
      have hIF : ∑ J ∈ F, c I * c J * y (I ∪ J) = y I := by
        rw [Finset.sum_eq_single I]
        · simp [c, hIne]
        · intro J hJ hJI
          have hIJ : I ≠ J := Ne.symm hJI
          have hu4 := union_mem_monomBasis4 (hF_sub hI) (hF_sub hJ)
          rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset] at hu4
          have hy0 : y (I ∪ J) = 0 := hy.2.1 (I ∪ J) hu4.1 hu4.2 (hconflict I hI J hJ hIJ)
          rw [hy0, mul_zero]
        · intro hIn; exact False.elim (hIn hI)
      rw [hI0, hIF]; ring
    rw [hrow0, hrowsF, add_zero]
  linarith

/-- Degree-2 Lasserre implies PSD of the Degree-1 lifted moment matrix `[1, x^T; x, X]`. -/
lemma lasserre2_psd1 {N : ℕ} {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible N y) :
    ∀ (c₀ : ℝ) (v : ℕ → ℝ),
      0 ≤ c₀ ^ 2 + 2 * c₀ * (∑ i ∈ Finset.range N, v i * y {i}) +
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * y {i, j} * v j := by
  classical
  intro c₀ v
  let Sing : Finset (Finset ℕ) := (Finset.range N).image (fun i => ({i} : Finset ℕ))
  let S : Finset (Finset ℕ) := insert ∅ Sing
  have hS : S ⊆ monomBasis2 N := by
    refine Finset.insert_subset (empty_mem_monomBasis2 N) ?_
    intro I hI
    rcases Finset.mem_image.mp hI with ⟨i, hi, rfl⟩
    exact singleton_mem_monomBasis2 (Finset.mem_range.mp hi)
  have h0not : (∅ : Finset ℕ) ∉ Sing := by
    intro h
    rcases Finset.mem_image.mp h with ⟨i, _, hi⟩
    exact Finset.singleton_ne_empty i hi
  let c : Finset ℕ → ℝ := fun I =>
    (if I = ∅ then c₀ else 0) + ∑ i ∈ Finset.range N, if I = {i} then v i else 0
  have hc0 : c ∅ = c₀ := by
    simp only [c, ↓reduceIte]
    have : ∑ i ∈ Finset.range N, (if (∅ : Finset ℕ) = {i} then v i else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (Ne.symm (Finset.singleton_ne_empty i))]
    rw [this, add_zero]
  have hcsing : ∀ i ∈ Finset.range N, c {i} = v i := by
    intro i hi
    simp only [c, if_neg (Finset.singleton_ne_empty i), zero_add]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [if_neg]
      intro heq
      exact hji ((Finset.singleton_injective heq).symm)
    · intro hin; exact False.elim (hin hi)
  have hq := lasserre2_quad_nonneg_of_support hy hS c
  have hexpand :
      ∑ I ∈ S, ∑ J ∈ S, c I * c J * y (I ∪ J) =
      c₀ ^ 2 + 2 * c₀ * (∑ i ∈ Finset.range N, v i * y {i}) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * y {i, j} * v j := by
    rw [Finset.sum_insert h0not]
    have hrow0 : ∑ J ∈ S, c ∅ * c J * y (∅ ∪ J) =
        c₀ ^ 2 + c₀ * ∑ j ∈ Finset.range N, v j * y {j} := by
      rw [Finset.sum_insert h0not, hc0, Finset.empty_union, hy.1, mul_one, ← sq]
      congr 1
      rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hcsing j hj, Finset.empty_union]; ring
    have hrowsS : ∑ I ∈ Sing, ∑ J ∈ S, c I * c J * y (I ∪ J) =
        c₀ * (∑ i ∈ Finset.range N, v i * y {i}) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * y {i, j} * v j := by
      rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
      have hterm : ∀ i ∈ Finset.range N,
          ∑ J ∈ S, c {i} * c J * y ({i} ∪ J) =
          c₀ * (v i * y {i}) + ∑ j ∈ Finset.range N, v i * y {i, j} * v j := by
        intro i hi
        rw [Finset.sum_insert h0not, hcsing i hi, hc0, Finset.union_empty]
        congr 1
        · ring
        · rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [hcsing j hj]
          have hunion : ({i} : Finset ℕ) ∪ {j} = {i, j} := rfl
          rw [hunion]; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hrow0, hrowsS]; ring
  linarith

/-- Degree-2 Lasserre implies all nonnegativity and McCormick / RLT inequalities on `y {i, j}`. -/
lemma lasserre2_mccormick {N : ℕ} {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible N y)
    {i j : ℕ} (hi : i < N) (hj : j < N) :
    0 ≤ y {i, j} ∧ y {i, j} ≤ y {i} ∧ y {i, j} ≤ y {j} ∧ y {i} + y {j} - 1 ≤ y {i, j} := by
  classical
  have hnn : 0 ≤ y {i, j} := lasserre2_nonneg_monom hy (pair_mem_monomBasis2 hi hj)
  have hle_left : ∀ a b : ℕ, a < N → b < N → y {a, b} ≤ y {a} := by
    intro a b ha hb
    by_cases hab : a = b
    · subst hab; rw [Finset.pair_eq_singleton]
    · have hne : ({a} : Finset ℕ) ≠ {a, b} := by
        intro h
        have hmem : b ∈ ({a} : Finset ℕ) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
        exact hab (Finset.mem_singleton.mp hmem).symm
      let S : Finset (Finset ℕ) := {{a}, {a, b}}
      have hS : S ⊆ monomBasis2 N := by
        intro I hI
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hI
        rcases hI with rfl | rfl
        · exact singleton_mem_monomBasis2 ha
        · exact pair_mem_monomBasis2 ha hb
      let c : Finset ℕ → ℝ := fun I => if I = {a} then 1 else -1
      have hq := lasserre2_quad_nonneg_of_support hy hS c
      have hu1 : ({a} : Finset ℕ) ∪ {a, b} = {a, b} := by ext x; simp
      have hu2 : ({a, b} : Finset ℕ) ∪ {a} = {a, b} := by ext x; simp
      simp only [S, Finset.sum_pair hne, c, ↓reduceIte, if_neg hne.symm, Finset.union_self,
        hu1, hu2] at hq
      linarith
  have hlower : y {i} + y {j} - 1 ≤ y {i, j} := by
    by_cases hij : i = j
    · subst hij
      rw [Finset.pair_eq_singleton]
      have h1 : y {i} ≤ 1 := by
        have hS : ({∅, {i}} : Finset (Finset ℕ)) ⊆ monomBasis2 N := by
          intro I hI; simp only [Finset.mem_insert, Finset.mem_singleton] at hI
          rcases hI with rfl | rfl
          · exact empty_mem_monomBasis2 N
          · exact singleton_mem_monomBasis2 hi
        have hne : (∅ : Finset ℕ) ≠ {i} := Ne.symm (Finset.singleton_ne_empty i)
        let c : Finset ℕ → ℝ := fun I => if I = ∅ then 1 else -1
        have hq := lasserre2_quad_nonneg_of_support hy hS c
        simp only [Finset.sum_pair hne, c, ↓reduceIte, if_neg hne.symm, Finset.empty_union,
          Finset.union_empty, Finset.union_self, hy.1] at hq
        linarith
      linarith
    · -- 4-element support `{∅, {i}, {j}, {i, j}}` with `c = (1, -1, -1, 1)`
      have h0i : (∅ : Finset ℕ) ≠ {i} := Ne.symm (Finset.singleton_ne_empty i)
      have h0j : (∅ : Finset ℕ) ≠ {j} := Ne.symm (Finset.singleton_ne_empty j)
      have h0ij : (∅ : Finset ℕ) ≠ {i, j} := by intro h; exact Finset.insert_ne_empty i {j} h.symm
      have hi_j : ({i} : Finset ℕ) ≠ {j} := fun h => hij (Finset.singleton_injective h)
      have hi_ij : ({i} : Finset ℕ) ≠ {i, j} := by
        intro h
        have hmem : j ∈ ({i} : Finset ℕ) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
        exact hij (Finset.mem_singleton.mp hmem).symm
      have hj_ij : ({j} : Finset ℕ) ≠ {i, j} := by
        intro h
        have hmem : i ∈ ({j} : Finset ℕ) := h ▸ Finset.mem_insert_self i {j}
        exact hij (Finset.mem_singleton.mp hmem)
      let S : Finset (Finset ℕ) := {∅, {i}, {j}, {i, j}}
      have hS : S ⊆ monomBasis2 N := by
        intro I hI
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hI
        rcases hI with rfl | rfl | rfl | rfl
        · exact empty_mem_monomBasis2 N
        · exact singleton_mem_monomBasis2 hi
        · exact singleton_mem_monomBasis2 hj
        · exact pair_mem_monomBasis2 hi hj
      let c : Finset ℕ → ℝ := fun I => if I = ∅ ∨ I = {i, j} then 1 else -1
      have hq := lasserre2_quad_nonneg_of_support hy hS c
      have hu_ij : ({i} : Finset ℕ) ∪ {j} = {i, j} := rfl
      have hu_ji : ({j} : Finset ℕ) ∪ {i} = {i, j} := by ext x; simp; tauto
      have hu_i_ij : ({i} : Finset ℕ) ∪ {i, j} = {i, j} := by ext x; simp
      have hu_ij_i : ({i, j} : Finset ℕ) ∪ {i} = {i, j} := by ext x; simp
      have hu_j_ij : ({j} : Finset ℕ) ∪ {i, j} = {i, j} := by ext x; simp
      have hu_ij_j : ({i, j} : Finset ℕ) ∪ {j} = {i, j} := by ext x; simp
      have hnot1 : (∅ : Finset ℕ) ∉ ({({i} : Finset ℕ), {j}, {i, j}} : Finset (Finset ℕ)) := by
        simp [h0i, h0j, h0ij]
      have hnot2 : ({i} : Finset ℕ) ∉ ({({j} : Finset ℕ), {i, j}} : Finset (Finset ℕ)) := by
        simp [hi_j, hi_ij]
      have hnot3 : ({j} : Finset ℕ) ∉ ({({i, j} : Finset ℕ)} : Finset (Finset ℕ)) := by
        simp [hj_ij]
      have hsum4 : ∀ f : Finset ℕ → ℝ,
          ∑ I ∈ S, f I = f ∅ + f {i} + f {j} + f {i, j} := by
        intro f
        dsimp only [S]
        rw [Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_insert hnot3,
          Finset.sum_singleton]
        ring
      have hc_0 : c ∅ = 1 := by simp [c]
      have hc_i : c {i} = -1 := by simp [c, h0i.symm, hi_ij]
      have hc_j : c {j} = -1 := by simp [c, h0j.symm, hj_ij]
      have hc_ij : c {i, j} = 1 := by simp [c]
      rw [hsum4] at hq
      simp only [hsum4, hc_0, hc_i, hc_j, hc_ij, Finset.empty_union, Finset.union_empty,
        Finset.union_idempotent, hu_ij, hu_ji, hu_i_ij, hu_ij_i, hu_j_ij, hu_ij_j, hy.1] at hq
      linarith
  exact ⟨hnn, hle_left i j hi hj, by rw [Finset.pair_comm]; exact hle_left j i hj hi, hlower⟩

/-- Degree-2 Lasserre implies all `N - 1` exact pointwise Sidon constraints
`∑_{i < N - d} y {i, i + d} ≤ 1`. -/
theorem lasserre2_sidon_offdiag {N : ℕ} {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible N y)
    {d : ℕ} (hd1 : 1 ≤ d) (hdN : d < N) :
    ∑ i ∈ Finset.range (N - d), y {i, i + d} ≤ 1 := by
  classical
  let F : Finset (Finset ℕ) := (Finset.range (N - d)).image (fun i => ({i, i + d} : Finset ℕ))
  have hinj : Set.InjOn (fun i => ({i, i + d} : Finset ℕ)) ((Finset.range (N - d)) : Set ℕ) := by
    intro i _ j _ heq
    dsimp only at heq
    have hmem1 : i ∈ ({j, j + d} : Finset ℕ) := heq ▸ Finset.mem_insert_self i _
    have hmem2 : j ∈ ({i, i + d} : Finset ℕ) := heq.symm ▸ Finset.mem_insert_self j _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
    omega
  have hsum : ∑ I ∈ F, y I = ∑ i ∈ Finset.range (N - d), y {i, i + d} :=
    Finset.sum_image (fun a ha b hb h => hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h)
  rw [← hsum]
  refine lasserre2_conflict_family_le_one hy ?_ ?_ ?_
  · intro I hI
    rcases Finset.mem_image.mp hI with ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    exact pair_mem_monomBasis2 (by omega) (by omega)
  · intro h0
    rcases Finset.mem_image.mp h0 with ⟨i, _, hi⟩
    exact Finset.insert_ne_empty i {i + d} hi
  · intro I hI J hJ hIJ hsid
    rcases Finset.mem_image.mp hI with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hJ with ⟨j, _, rfl⟩
    have hij : i ≠ j := fun h => hIJ (by rw [h])
    have hi1 : i ∈ (({i, i + d} ∪ {j, j + d} : Finset ℕ) : Set ℕ) := by simp
    have hi2 : i + d ∈ (({i, i + d} ∪ {j, j + d} : Finset ℕ) : Set ℕ) := by simp
    have hj1 : j ∈ (({i, i + d} ∪ {j, j + d} : Finset ℕ) : Set ℕ) := by simp
    have hj2 : j + d ∈ (({i, i + d} ∪ {j, j + d} : Finset ℕ) : Set ℕ) := by simp
    have hres := hsid i hi1 (j + d) hj2 (i + d) hi2 j hj1 (by omega)
    omega

/-- Degree-2 Lasserre implies all `Θ(N^2)` exact 3-AP linear cuts
`y {a, b} + y {b, c} + y {a, c} ≤ 1`. -/
theorem lasserre2_3ap_cut {N : ℕ} {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible N y)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hcN : c < N) (hap : a + c = 2 * b) :
    y {a, b} + y {b, c} + y {a, c} ≤ 1 := by
  classical
  have hab_bc : ({a, b} : Finset ℕ) ≠ {b, c} := by
    intro h
    have hm : a ∈ ({b, c} : Finset ℕ) := h ▸ Finset.mem_insert_self a _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  have hab_ac : ({a, b} : Finset ℕ) ≠ {a, c} := by
    intro h
    have hm : b ∈ ({a, c} : Finset ℕ) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  have hbc_ac : ({b, c} : Finset ℕ) ≠ {a, c} := by
    intro h
    have hm : b ∈ ({a, c} : Finset ℕ) := h ▸ Finset.mem_insert_self b _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
  let F : Finset (Finset ℕ) := {{a, b}, {b, c}, {a, c}}
  have hsum : ∑ I ∈ F, y I = y {a, b} + y {b, c} + y {a, c} := by
    dsimp only [F]
    rw [Finset.sum_insert (by simp [hab_bc, hab_ac]), Finset.sum_pair hbc_ac]
    ring
  rw [← hsum]
  refine lasserre2_conflict_family_le_one hy ?_ ?_ ?_
  · intro I hI
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hI
    rcases hI with rfl | rfl | rfl
    · exact pair_mem_monomBasis2 (by omega) (by omega)
    · exact pair_mem_monomBasis2 (by omega) hcN
    · exact pair_mem_monomBasis2 (by omega) hcN
  · simp only [F, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm (Finset.insert_ne_empty _ _), Ne.symm (Finset.insert_ne_empty _ _),
      Ne.symm (Finset.insert_ne_empty _ _)⟩
  · intro I hI J hJ hIJ hsid
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hI hJ
    have ha : a ∈ ((I ∪ J : Finset ℕ) : Set ℕ) := by
      rcases hI with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl <;> simp_all
    have hb : b ∈ ((I ∪ J : Finset ℕ) : Set ℕ) := by
      rcases hI with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl <;> simp_all
    have hc : c ∈ ((I ∪ J : Finset ℕ) : Set ℕ) := by
      rcases hI with rfl | rfl | rfl <;> rcases hJ with rfl | rfl | rfl <;> simp_all
    have hres := hsid a ha c hc b hb b hb (by omega)
    omega

/-- Degree-2 Lasserre implies all `Θ(N^3)` pairwise 4-Sidon cuts (`≤ 1` each) and hence the full
6-edge 4-Sidon linear cut (`≤ 3`). -/
theorem lasserre2_4sidon_cuts {N : ℕ} {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible N y)
    {a b c e : ℕ} (hab : a < b) (hbc : b < c) (hce : c < e) (heN : e < N)
    (hsid4 : a + e = b + c) :
    y {a, b} + y {c, e} ≤ 1 ∧
    y {a, c} + y {b, e} ≤ 1 ∧
    y {a, e} + y {b, c} ≤ 1 ∧
    y {a, b} + y {a, c} + y {a, e} + y {b, c} + y {b, e} + y {c, e} ≤ 3 := by
  classical
  have hpair_cut : ∀ p q r s : ℕ,
      p < N → q < N → r < N → s < N →
      ({p, q} : Finset ℕ) ≠ {r, s} →
      ({p, q} : Finset ℕ) ∪ {r, s} = {a, b, c, e} →
      y {p, q} + y {r, s} ≤ 1 := by
    intro p q r s hp hq hr hs hne hunion
    let F : Finset (Finset ℕ) := {{p, q}, {r, s}}
    have hsum : ∑ I ∈ F, y I = y {p, q} + y {r, s} := Finset.sum_pair hne
    rw [← hsum]
    refine lasserre2_conflict_family_le_one hy ?_ ?_ ?_
    · intro I hI
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hI
      rcases hI with rfl | rfl
      · exact pair_mem_monomBasis2 hp hq
      · exact pair_mem_monomBasis2 hr hs
    · simp only [F, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm (Finset.insert_ne_empty _ _), Ne.symm (Finset.insert_ne_empty _ _)⟩
    · intro I hI J hJ hIJ hsid
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hI hJ
      have hu : I ∪ J = {a, b, c, e} := by
        rcases hI with rfl | rfl <;> rcases hJ with rfl | rfl
        · exact False.elim (hIJ rfl)
        · exact hunion
        · rw [Finset.union_comm]; exact hunion
        · exact False.elim (hIJ rfl)
      rw [hu] at hsid
      have hres := hsid a (by simp) e (by simp) b (by simp) c (by simp) hsid4
      omega
  have h1 : y {a, b} + y {c, e} ≤ 1 := by
    refine hpair_cut a b c e (by omega) (by omega) (by omega) heN ?_ ?_
    · intro h; have hm : a ∈ ({c, e} : Finset ℕ) := h ▸ Finset.mem_insert_self a _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
    · ext x; simp; tauto
  have h2 : y {a, c} + y {b, e} ≤ 1 := by
    refine hpair_cut a c b e (by omega) (by omega) (by omega) heN ?_ ?_
    · intro h; have hm : a ∈ ({b, e} : Finset ℕ) := h ▸ Finset.mem_insert_self a _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
    · ext x; simp; tauto
  have h3 : y {a, e} + y {b, c} ≤ 1 := by
    refine hpair_cut a e b c (by omega) heN (by omega) (by omega) ?_ ?_
    · intro h; have hm : a ∈ ({b, c} : Finset ℕ) := h ▸ Finset.mem_insert_self a _
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm; omega
    · ext x; simp; tauto
  exact ⟨h1, h2, h3, by linarith⟩

/-- General Degree-2 Sum-of-Squares Dual Certificate Soundness Theorem:
If `C - ∑_{i < N} x_i` is dominated (on degree `≤ 2` monomials, where `y u ≥ 0`) and matched
(on Sidon degree-3 and degree-4 monomials, where `y u` is free) by a Sum of Squares of `K`
degree-`≤ 2` polynomials `g k` modulo the Boolean and degree-`≤ 4` Sidon ideals, then EVERY
Degree-2 Lasserre feasible functional satisfies `∑_{i < N} y {i} ≤ C` (and hence `h N ≤ C`). -/
theorem lasserre2_dual_sos_bound {N K : ℕ} {C : ℝ} (g : Fin K → Finset ℕ → ℝ)
    (hdeg_le2 : ∀ u ∈ monomBasis2 N,
      ∑ k : Fin K, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
        (if I ∪ J = u then g k I * g k J else 0) ≤
      (if u = ∅ then C else 0) - (if u.card = 1 then (1 : ℝ) else 0))
    (hdeg_34 : ∀ u ∈ monomBasis4 N, 2 < u.card → IsSidon (u : Set ℕ) →
      ∑ k : Fin K, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
        (if I ∪ J = u then g k I * g k J else 0) = 0) :
    (∀ y : Finset ℕ → ℝ, IsLasserre2Feasible N y → ∑ i ∈ Finset.range N, y {i} ≤ C) ∧
    (h N : ℝ) ≤ C := by
  classical
  have hmain : ∀ y : Finset ℕ → ℝ, IsLasserre2Feasible N y → ∑ i ∈ Finset.range N, y {i} ≤ C := by
    intro y hy
    -- Nonnegativity of the total SoS pseudo-expectation
    have hsos_nn : 0 ≤ ∑ k : Fin K,
        ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, g k I * g k J * y (I ∪ J) :=
      Finset.sum_nonneg fun k _ => hy.2.2 (g k)
    -- Re-group by `u = I ∪ J ∈ monomBasis4 N`
    have hregroup :
        ∑ k : Fin K, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, g k I * g k J * y (I ∪ J) =
        ∑ u ∈ monomBasis4 N,
          (∑ k : Fin K, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
            if I ∪ J = u then g k I * g k J else 0) * y u := by
      have hinner : ∀ k : Fin K,
          ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, g k I * g k J * y (I ∪ J) =
          ∑ u ∈ monomBasis4 N,
            (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
              if I ∪ J = u then g k I * g k J else 0) * y u := by
        intro k
        have hstep : ∀ I ∈ monomBasis2 N, ∀ J ∈ monomBasis2 N,
            g k I * g k J * y (I ∪ J) =
            ∑ u ∈ monomBasis4 N, (if I ∪ J = u then g k I * g k J else 0) * y u := by
          intro I hI J hJ
          rw [Finset.sum_eq_single (I ∪ J)]
          · simp
          · intro u _ hu; rw [if_neg (Ne.symm hu), zero_mul]
          · intro hnot; exact False.elim (hnot (union_mem_monomBasis4 hI hJ))
        calc ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, g k I * g k J * y (I ∪ J)
            = ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
                ∑ u ∈ monomBasis4 N, (if I ∪ J = u then g k I * g k J else 0) * y u := by
              refine Finset.sum_congr rfl fun I hI =>
                Finset.sum_congr rfl fun J hJ => hstep I hI J hJ
          _ = ∑ u ∈ monomBasis4 N, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
                (if I ∪ J = u then g k I * g k J else 0) * y u := by
              rw [Finset.sum_comm]
              conv_lhs =>
                arg 2; ext I; rw [Finset.sum_comm]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
          _ = ∑ u ∈ monomBasis4 N,
                (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
                  if I ∪ J = u then g k I * g k J else 0) * y u := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun I _ => (Finset.sum_mul ..).symm
      rw [Finset.sum_congr rfl fun k _ => hinner k, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => (Finset.sum_mul ..).symm
    -- Upper-bound each `u ∈ monomBasis4 N` term
    have hterm_le :
        ∑ u ∈ monomBasis4 N,
          (∑ k : Fin K, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
            if I ∪ J = u then g k I * g k J else 0) * y u ≤
        ∑ u ∈ monomBasis4 N,
          ((if u = ∅ then C else 0) - (if u.card = 1 then (1 : ℝ) else 0)) * y u := by
      refine Finset.sum_le_sum fun u hu => ?_
      by_cases hle2 : u.card ≤ 2
      · have hu2 : u ∈ monomBasis2 N := by
          rw [monomBasis4, Finset.mem_filter] at hu
          exact Finset.mem_filter.mpr ⟨hu.1, hle2⟩
        exact mul_le_mul_of_nonneg_right (hdeg_le2 u hu2) (lasserre2_nonneg_monom hy hu2)
      · have hgt2 : 2 < u.card := by omega
        have hne0 : u ≠ ∅ := by intro h; subst h; simp at hgt2
        have hne1 : u.card ≠ 1 := by omega
        rw [if_neg hne0, if_neg hne1, sub_self, zero_mul]
        by_cases hsid : IsSidon (u : Set ℕ)
        · rw [hdeg_34 u hu hgt2 hsid, zero_mul]
        · rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset] at hu
          rw [hy.2.1 u hu.1 hu.2 hsid, mul_zero]
    -- Evaluate RHS `= C - ∑_{i < N} y {i}`
    have hrhs_eq :
        ∑ u ∈ monomBasis4 N,
          ((if u = ∅ then C else 0) - (if u.card = 1 then (1 : ℝ) else 0)) * y u =
        C - ∑ i ∈ Finset.range N, y {i} := by
      have hsplit :
          ∑ u ∈ monomBasis4 N,
            ((if u = ∅ then C else 0) - (if u.card = 1 then (1 : ℝ) else 0)) * y u =
          (∑ u ∈ monomBasis4 N, (if u = ∅ then C else 0) * y u) -
          (∑ u ∈ monomBasis4 N, (if u.card = 1 then (1 : ℝ) else 0) * y u) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun u _ => sub_mul _ _ _
      rw [hsplit]
      have h0 : ∑ u ∈ monomBasis4 N, (if u = ∅ then C else 0) * y u = C := by
        rw [Finset.sum_eq_single ∅]
        · simp [hy.1]
        · intro u _ hu; rw [if_neg hu, zero_mul]
        · intro hnot; exact False.elim (hnot (by simp [monomBasis4]))
      have h1 : ∑ u ∈ monomBasis4 N, (if u.card = 1 then (1 : ℝ) else 0) * y u =
          ∑ i ∈ Finset.range N, y {i} := by
        let Sing : Finset (Finset ℕ) := (Finset.range N).image (fun i => ({i} : Finset ℕ))
        have hsub : Sing ⊆ monomBasis4 N := by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
          rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.singleton_subset_iff.mpr hi, by simp⟩
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h)]
          refine Finset.sum_congr rfl fun i _ => by simp
        · intro u hu hnot
          rw [if_neg, zero_mul]
          intro hcard1
          rcases Finset.card_eq_one.mp hcard1 with ⟨i, rfl⟩
          apply hnot
          rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset] at hu
          exact Finset.mem_image.mpr ⟨i, hu.1 (Finset.mem_singleton_self i), rfl⟩
      rw [h0, h1]
    linarith
  exact ⟨hmain, h_le_of_lasserre2_bound hmain⟩

end Erdos030
