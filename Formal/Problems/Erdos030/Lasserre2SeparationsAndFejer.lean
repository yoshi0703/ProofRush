import Problems.Erdos030.Statement
import Problems.Erdos030.Lasserre2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Degree-2 Lasserre Strict Separation at `N = 6` (L2-A1) & All-`N` Smooth Fejér `SDP_1+` Barrier (L2-B)

Formalizes two compact, self-contained theorems audited in Milestone 3:
1. **Theorem L2-A1 (`h_6_eq_3`, `lasserre2_bound_3_plus_4_P4`, `lasserre2_le_3_of_h_le_3`,
   `lasserre2_6_le_3`)**:
   Using the exact 2-square Boolean identity
   `3 - S + 4 * C(S, 4) = (1/3) * (3 - S)^2 + (2/3) * (S - C(S, 2))^2`,
   proves for EVERY `N` and EVERY `IsLasserre2Feasible N y`:
   `∑_{i < N} y {i} ≤ 3 + 4 * ∑_{|u| = 4} y u`.
   Since `h 6 = 3` (zero Sidon 4-tuples in `range 6`), this immediately yields
   `Lasserre_2(6) = h(6) = 3 < 7/2 ≤ M(6) ≤ SDP_1(6)`.
2. **Theorem L2-B (`fejer_toeplitz_quadratic_le`, `smooth_fejer_sdp1_core`)**:
   Elementary all-`N` (`N ≥ 81`, zero primes, zero Bose sets, zero Fourier) Smooth Fejér
   `SDP_1+` barrier with `L = Nat.sqrt (Nat.sqrt (N^3)) = ⌊N^(3/4)⌋`,
   `μ_i = √(N + L) / N`, `X_ii = μ_i`, `X_ij = (N + min(|i - j|, L)) / N^2` (`i ≠ j`):
   satisfies symmetry, PSD of `[1, μ^T; μ, X]`, diagonal integrality, all McCormick/RLT,
   all `N - 1` pointwise Sidon constraints, all BQP triangle inequalities, all 3-AP cuts,
   and all 4-Sidon cuts, with objective `∑_{i < N} μ_i = √(N + L) > √N + (2/5) N^(1/4)`
   (and asymptotically `≥ √N + (1/2 - ε) N^(1/4)` for every `ε > 0`).
-/

namespace Erdos030

open Finset
open scoped BigOperators

/-! ### Part 1: Theorem L2-A1 — Exact 2-Square Degree-2 Lasserre Bound & `N = 6` Separation -/

/-- Exact evaluation `h(6) = 3` (attained by `{1, 2, 4}`). -/
theorem h_6_eq_3 : h 6 = 3 := by
  classical
  have hle : h 6 ≤ 3 := by
    unfold h maxSidonSubsetCard
    refine Finset.sup_le fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    by_contra hgt; push Not at hgt
    let P := A.offDiag.filter (fun p => p.2 < p.1)
    let D := P.image (fun p => p.1 - p.2)
    have hDsub : D ⊆ Finset.Icc 1 5 := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
      rw [Finset.mem_filter, Finset.mem_offDiag] at hp
      have h1 := Finset.mem_Icc.mp (hA.1 hp.1.1)
      have h2 := Finset.mem_Icc.mp (hA.1 hp.1.2.1)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) (P : Set (ℕ × ℕ)) := by
      intro p hp q hq heq
      dsimp only at heq
      simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp hq
      have hsum : p.1 + q.2 = q.1 + p.2 := by omega
      rcases hA.2 p.1 hp.1.1 q.2 hq.1.2.1 q.1 hq.1.1 p.2 hp.1.2.1 hsum with ⟨h1, h2⟩ | ⟨_, _⟩
      · exact Prod.ext h1 h2.symm
      · omega
    have hPcard : 2 * P.card = A.offDiag.card := by
      have hunion : A.offDiag = P ∪ A.offDiag.filter (fun p => p.1 < p.2) := by
        ext p; simp only [P, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
        constructor
        · intro h; rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt'
          · left; exact ⟨h, hlt⟩
          · exact False.elim (h.2.2 heq.symm)
          · right; exact ⟨h, hgt'⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint P (A.offDiag.filter (fun p => p.1 < p.2)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P, Finset.mem_filter] at h1 h2; omega
      have hswap : (A.offDiag.filter (fun p => p.1 < p.2)).card = P.card := by
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
    have hoff : A.offDiag.card + A.card = A.card * A.card := by
      have hle' : A.card ≤ A.card * A.card := Nat.le_mul_self A.card
      rw [Finset.offDiag_card]; omega
    have hDle5 : D.card ≤ 5 :=
      (Finset.card_le_card hDsub).trans (by rw [show (Finset.Icc 1 5).card = 5 by decide])
    rw [Finset.card_image_of_injOn hinj] at hDle5
    nlinarith
  have hge : 3 ≤ h 6 := by
    let A : Finset ℕ := {1, 2, 4}
    have hsub : A ⊆ Finset.Icc 1 6 := by decide
    have hS : IsSidon (A : Set ℕ) := by
      intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
      simp only [A, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha₁ hb₁ ha₂ hb₂
      rcases ha₁ with rfl | rfl | rfl <;> rcases hb₁ with rfl | rfl | rfl <;>
        rcases ha₂ with rfl | rfl | rfl <;> rcases hb₂ with rfl | rfl | rfl <;> omega
    have hmem : A ∈ (Finset.Icc 1 6).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hS⟩
    have hc : A.card = 3 := by decide
    rw [← hc]; exact Finset.le_sup (f := Finset.card) hmem
  omega

/-- Integer coefficient of the first Boolean SoS polynomial `3 - S`. -/
private def sosPoly1Z {α : Type*} (I : Finset α) : ℤ :=
  if I.card = 0 then 3 else if I.card = 1 then -1 else 0

/-- Integer coefficient of the second Boolean SoS polynomial `S - C(S, 2)`. -/
private def sosPoly2Z {α : Type*} (I : Finset α) : ℤ :=
  if I.card = 1 then 1 else if I.card = 2 then -1 else 0

/-- Integer monomial coefficient of `(3 - S)^2 + 2 * (S - C(S, 2))^2` on a finite set `u`. -/
private def twoSqCoeffZ {α : Type*} [DecidableEq α] (u : Finset α) : ℤ :=
  ∑ I ∈ u.powerset.filter (fun I => I.card ≤ 2),
    ∑ J ∈ u.powerset.filter (fun J => J.card ≤ 2),
      if I ∪ J = u then
        sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J
      else 0

/-- `twoSqCoeffZ` is invariant under embeddings `e : α ↪ β`. -/
private lemma twoSqCoeffZ_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (e : α ↪ β) :
    twoSqCoeffZ (s.map e) = twoSqCoeffZ s := by
  unfold twoSqCoeffZ
  have hbij : ∀ (P : Finset (Finset α)),
      P = s.powerset.filter (fun I => I.card ≤ 2) →
      (s.map e).powerset.filter (fun I => I.card ≤ 2) = P.image (fun I => I.map e) := by
    intro P hP
    subst hP
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hAsub, hAcard⟩
      refine ⟨s.filter (fun x => e x ∈ A), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
      · have hmap : (s.filter (fun x => e x ∈ A)).map e = A := by
          ext y
          simp only [Finset.mem_map, Finset.mem_filter]
          constructor
          · rintro ⟨x, ⟨_, hxA⟩, rfl⟩; exact hxA
          · intro hyA
            rcases Finset.mem_map.mp (hAsub hyA) with ⟨x, hxs, rfl⟩
            exact ⟨x, ⟨hxs, hyA⟩, rfl⟩
        rw [← Finset.card_map e, hmap]
        exact hAcard
      · ext y
        simp only [Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨x, ⟨_, hxA⟩, rfl⟩; exact hxA
        · intro hyA
          rcases Finset.mem_map.mp (hAsub hyA) with ⟨x, hxs, rfl⟩
          exact ⟨x, ⟨hxs, hyA⟩, rfl⟩
    · rintro ⟨I, ⟨hIs, hIcard⟩, rfl⟩
      exact ⟨Finset.map_subset_map.mpr hIs, by simpa using hIcard⟩
  have hinj : ∀ I₁ I₂ : Finset α, I₁.map e = I₂.map e → I₁ = I₂ := by
    intro I₁ I₂ h
    ext x
    have := Finset.ext_iff.mp h (e x)
    simpa only [Finset.mem_map_equiv, Finset.mem_map, e.injective.eq_iff, exists_eq_right] using this
  rw [hbij _ rfl, Finset.sum_image (fun a _ b _ h => hinj a b h)]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => hinj a b h)]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hunion : I.map e ∪ J.map e = s.map e ↔ I ∪ J = s := by
    rw [← Finset.map_union]
    exact ⟨fun h => hinj _ _ h, fun h => congrArg (Finset.map e) h⟩
  simp only [hunion, sosPoly1Z, sosPoly2Z, Finset.card_map]

/-- Exact evaluation of `twoSqCoeffZ u` for every `u : Finset ℕ` with `u.card ≤ 4`:
`9` for `|u| = 0`, `-3` for `|u| = 1`, `0` for `|u| = 2, 3`, and `12` for `|u| = 4`. -/
private lemma twoSqCoeffZ_eval (u : Finset ℕ) (hu : u.card ≤ 4) :
    twoSqCoeffZ u =
      if u.card = 0 then (9 : ℤ)
      else if u.card = 1 then -3
      else if u.card = 4 then 12
      else 0 := by
  have hmap : u = (Finset.univ : Finset (Fin u.card)).map (u.orderEmbOfFin rfl).toEmbedding := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · intro hx
      have hmem : x ∈ Set.range (u.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      exact hmem
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem u rfl i
  conv_lhs => rw [hmap]
  rw [twoSqCoeffZ_map]
  generalize hk : u.card = k at hu ⊢
  interval_cases k <;> decide

/-- Universal 2-Square Degree-2 Lasserre Bound (Theorem L2-A1 general core):
For EVERY `N : ℕ` and EVERY `IsLasserre2Feasible N y`,
`∑_{i < N} y {i} ≤ 3 + 4 * ∑_{u ∈ (range N).powersetCard 4} y u`. -/
theorem lasserre2_bound_3_plus_4_P4 {N : ℕ} {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) :
    ∑ i ∈ Finset.range N, y {i} ≤
      3 + 4 * ∑ u ∈ (Finset.range N).powersetCard 4, y u := by
  classical
  let c₁ : Finset ℕ → ℝ := fun I => (sosPoly1Z I : ℝ)
  let c₂ : Finset ℕ → ℝ := fun I => (sosPoly2Z I : ℝ)
  have hQ₁ : 0 ≤ ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₁ I * c₁ J * y (I ∪ J) := hy.2.2 c₁
  have hQ₂ : 0 ≤ ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₂ I * c₂ J * y (I ∪ J) := hy.2.2 c₂
  have hcomb_nn :
      0 ≤ (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₁ I * c₁ J * y (I ∪ J)) +
          2 * (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₂ I * c₂ J * y (I ∪ J)) := by
    linarith only [hQ₁, hQ₂]
  -- Group `(I, J) ∈ monomBasis2 N × monomBasis2 N` by `u = I ∪ J ∈ monomBasis4 N`
  have hgroup :
      (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₁ I * c₁ J * y (I ∪ J)) +
      2 * (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₂ I * c₂ J * y (I ∪ J)) =
      ∑ u ∈ monomBasis4 N, ((twoSqCoeffZ u : ℤ) : ℝ) * y u := by
    have hmerge :
        (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₁ I * c₁ J * y (I ∪ J)) +
        2 * (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, c₂ I * c₂ J * y (I ∪ J)) =
        ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
          ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ) * y (I ∪ J) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => ?_
      dsimp only [c₁, c₂]; push_cast; ring
    rw [hmerge]
    have hbyu :
        ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
          ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ) * y (I ∪ J) =
        ∑ u ∈ monomBasis4 N,
          (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
            if I ∪ J = u then
              ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ)
            else 0) * y u := by
      have hstep : ∀ I ∈ monomBasis2 N, ∀ J ∈ monomBasis2 N,
          ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ) * y (I ∪ J) =
          ∑ u ∈ monomBasis4 N,
            (if I ∪ J = u then
              ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ)
            else 0) * y u := by
        intro I hI J hJ
        rw [Finset.sum_eq_single (I ∪ J)]
        · simp
        · intro u _ hne; rw [if_neg (Ne.symm hne), zero_mul]
        · intro hnot; exact False.elim (hnot (union_mem_monomBasis4 hI hJ))
      calc ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
            ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ) * y (I ∪ J)
          = ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N, ∑ u ∈ monomBasis4 N,
              (if I ∪ J = u then
                ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ)
              else 0) * y u :=
            Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => hstep I hI J hJ
        _ = ∑ u ∈ monomBasis4 N, ∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
              (if I ∪ J = u then
                ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ)
              else 0) * y u := by
            rw [Finset.sum_comm]
            conv_lhs => arg 2; ext I; rw [Finset.sum_comm]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
        _ = ∑ u ∈ monomBasis4 N,
              (∑ I ∈ monomBasis2 N, ∑ J ∈ monomBasis2 N,
                if I ∪ J = u then
                  ((sosPoly1Z I * sosPoly1Z J + 2 * sosPoly2Z I * sosPoly2Z J : ℤ) : ℝ)
                else 0) * y u := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun I _ => (Finset.sum_mul ..).symm
    rw [hbyu]
    refine Finset.sum_congr rfl fun u hu => ?_
    congr 1
    rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset] at hu
    have hsub : u.powerset.filter (fun I => I.card ≤ 2) ⊆ monomBasis2 N := by
      intro I hI
      rw [Finset.mem_filter, Finset.mem_powerset] at hI
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hI.1.trans hu.1), hI.2⟩
    unfold twoSqCoeffZ
    push_cast
    symm
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun I _ => ?_
      rw [← Finset.sum_subset hsub]
      intro J hJ hJnot
      rw [if_neg]
      intro hun
      apply hJnot
      rw [Finset.mem_filter, Finset.mem_powerset]
      have hJ2 : J.card ≤ 2 := (Finset.mem_filter.mp hJ).2
      exact ⟨Finset.subset_union_right.trans (le_of_eq hun), hJ2⟩
    · intro I hI hInot
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [if_neg]
      intro hun
      apply hInot
      rw [Finset.mem_filter, Finset.mem_powerset]
      have hI2 : I.card ≤ 2 := (Finset.mem_filter.mp hI).2
      exact ⟨Finset.subset_union_left.trans (le_of_eq hun), hI2⟩
  -- Evaluate `∑ u ∈ monomBasis4 N, (twoSqCoeffZ u : ℝ) * y u = 9 - 3 * ∑ y {i} + 12 * ∑_{|u|=4} y u`
  have heval_sum :
      ∑ u ∈ monomBasis4 N, ((twoSqCoeffZ u : ℤ) : ℝ) * y u =
      9 - 3 * (∑ i ∈ Finset.range N, y {i}) + 12 * ∑ u ∈ (Finset.range N).powersetCard 4, y u := by
    have hpoint : ∀ u ∈ monomBasis4 N,
        ((twoSqCoeffZ u : ℤ) : ℝ) * y u =
        (if u.card = 0 then (9 : ℝ) * y u else 0) -
        (if u.card = 1 then (3 : ℝ) * y u else 0) +
        (if u.card = 4 then (12 : ℝ) * y u else 0) := by
      intro u hu
      have hucard : u.card ≤ 4 := (Finset.mem_filter.mp hu).2
      rw [twoSqCoeffZ_eval u hucard]
      by_cases h0 : u.card = 0
      · simp [h0]
      · by_cases h1 : u.card = 1
        · simp [h1]
        · by_cases h4 : u.card = 4
          · simp [h4]
          · simp [h0, h1, h4]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h0 : ∑ u ∈ monomBasis4 N, (if u.card = 0 then (9 : ℝ) * y u else 0) = 9 := by
      rw [Finset.sum_eq_single ∅]
      · simp [hy.1]
      · intro u _ hne
        have : u.card ≠ 0 := fun h => hne (Finset.card_eq_zero.mp h)
        rw [if_neg this]
      · intro hnot; exact False.elim (hnot (by simp [monomBasis4]))
    have h1 : ∑ u ∈ monomBasis4 N, (if u.card = 1 then (3 : ℝ) * y u else 0) =
        3 * ∑ i ∈ Finset.range N, y {i} := by
      let Sing : Finset (Finset ℕ) := (Finset.range N).image (fun i => ({i} : Finset ℕ))
      have hsub : Sing ⊆ monomBasis4 N := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi), by simp⟩
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h), Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by simp
      · intro u hu hnot
        rw [if_neg]
        intro hc1
        rcases Finset.card_eq_one.mp hc1 with ⟨i, rfl⟩
        apply hnot
        rw [monomBasis4, Finset.mem_filter, Finset.mem_powerset] at hu
        exact Finset.mem_image.mpr ⟨i, hu.1 (Finset.mem_singleton_self i), rfl⟩
    have h4 : ∑ u ∈ monomBasis4 N, (if u.card = 4 then (12 : ℝ) * y u else 0) =
        12 * ∑ u ∈ (Finset.range N).powersetCard 4, y u := by
      rw [Finset.mul_sum, ← Finset.sum_filter]
      congr 1
      ext u
      simp only [monomBasis4, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, _⟩, hc4⟩; exact ⟨hsub, hc4⟩
      · rintro ⟨hsub, hc4⟩; exact ⟨⟨hsub, by omega⟩, hc4⟩
    rw [h0, h1, h4]
  linarith only [hcomb_nn, hgroup, heval_sum]

/-- Bonus Corollary of Theorem L2-A1: for EVERY `N` with `h N ≤ 3`, every `IsLasserre2Feasible N y`
satisfies `∑_{i < N} y {i} ≤ 3`. -/
theorem lasserre2_le_3_of_h_le_3 {N : ℕ} (hN : h N ≤ 3) {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) :
    ∑ i ∈ Finset.range N, y {i} ≤ 3 := by
  classical
  have hbound := lasserre2_bound_3_plus_4_P4 hy
  have hzero : ∑ u ∈ (Finset.range N).powersetCard 4, y u = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [Finset.mem_powersetCard] at hu
    refine hy.2.1 u hu.1 (by omega) ?_
    intro hSid
    -- Shift `u ⊆ range N` by `+1` to get a Sidon subset of `Icc 1 N` of cardinality 4
    let u1 : Finset ℕ := u.image (· + 1)
    have hu1_sub : u1 ⊆ Finset.Icc 1 N := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      have hxN := Finset.mem_range.mp (hu.1 hx)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hu1_card : u1.card = 4 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), hu.2]
    have hu1_sid : IsSidon (u1 : Set ℕ) := by
      intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
      simp only [u1, Finset.mem_coe, Finset.mem_image] at ha₁ hb₁ ha₂ hb₂
      rcases ha₁ with ⟨x₁, hx₁, rfl⟩; rcases hb₁ with ⟨y₁, hy₁, rfl⟩
      rcases ha₂ with ⟨x₂, hx₂, rfl⟩; rcases hb₂ with ⟨y₂, hy₂, rfl⟩
      rcases hSid x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ (by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    have hmem : u1 ∈ (Finset.Icc 1 N).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hu1_sub, hu1_sid⟩
    have h4le : 4 ≤ h N := by
      rw [← hu1_card]
      exact Finset.le_sup (f := Finset.card) hmem
    omega
  linarith only [hbound, hzero]

/-- Theorem L2-A1 at `N = 6`: every `IsLasserre2Feasible 6 y` satisfies `∑_{i < 6} y {i} ≤ 3`. -/
theorem lasserre2_6_le_3 {y : Finset ℕ → ℝ} (hy : IsLasserre2Feasible 6 y) :
    ∑ i ∈ Finset.range 6, y {i} ≤ 3 :=
  lasserre2_le_3_of_h_le_3 (le_of_eq h_6_eq_3) hy

/-! ### Part 2: Theorem L2-B — Elementary All-`N` Smooth Fejér `SDP_1+` Barrier -/

/-- Exact overlap count of length-`L` windows in `range (N + L - 1)` containing both `i` and `j`:
equals `L - |i - j|` (using truncated natural subtraction, which equals `max(0, L - |i - j|)`). -/
private lemma card_fejer_window_overlap {N L i j : ℕ} (hL : 1 ≤ L) (hi : i < N) (hj : j < N) :
    ((Finset.range (N + L - 1)).filter (fun s => (i ≤ s ∧ s < i + L) ∧ (j ≤ s ∧ s < j + L))).card =
      L - (if i ≤ j then j - i else i - j) := by
  have heq : (Finset.range (N + L - 1)).filter
      (fun s => (i ≤ s ∧ s < i + L) ∧ (j ≤ s ∧ s < j + L)) =
      Finset.Ico (max i j) (min (i + L) (j + L)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, max_le_iff, lt_min_iff]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩; exact ⟨by omega, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  rw [heq, Nat.card_Ico]
  by_cases hij : i ≤ j
  · rw [if_pos hij, max_eq_right hij, min_eq_left (by omega)]; omega
  · rw [if_neg hij, max_eq_left (by omega), min_eq_right (by omega)]; omega

/-- Key 4-Line Window Cauchy-Schwarz Lemma for the Fejér Toeplitz Kernel:
For all `N, L ≥ 1` and all `v : ℕ → ℝ`,
`∑_{i, j < N} max(0, L - |i - j|) v_i v_j ≤ L^2 ∑_{i < N} v_i^2`. -/
lemma fejer_toeplitz_quadratic_le {N L : ℕ} (hL : 1 ≤ L) (v : ℕ → ℝ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j ≤
    (L : ℝ) ^ 2 * ∑ i ∈ Finset.range N, (v i) ^ 2 := by
  let W : ℕ → Finset ℕ := fun s => (Finset.range N).filter (fun i => i ≤ s ∧ s < i + L)
  -- Step 1: LHS equals `∑_{s < N + L - 1} (∑_{i ∈ W s} v i)^2`
  have hLHS :
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j =
      ∑ s ∈ Finset.range (N + L - 1), (∑ i ∈ W s, v i) ^ 2 := by
    have hsq :
        ∑ s ∈ Finset.range (N + L - 1), (∑ i ∈ W s, v i) ^ 2 =
        ∑ s ∈ Finset.range (N + L - 1), ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          if (i ≤ s ∧ s < i + L) ∧ (j ≤ s ∧ s < j + L) then v i * v j else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      have hW : ∑ i ∈ W s, v i = ∑ i ∈ Finset.range N, if i ≤ s ∧ s < i + L then v i else 0 :=
        Finset.sum_filter _ _
      rw [hW, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hi : i ≤ s ∧ s < i + L <;> by_cases hj : j ≤ s ∧ s < j + L <;> simp [hi, hj]
    rw [hsq]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      card_fejer_window_overlap hL (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
    ring
  -- Step 2: Cauchy-Schwarz on each window `W s` with `|W s| ≤ L`
  have hCS :
      ∑ s ∈ Finset.range (N + L - 1), (∑ i ∈ W s, v i) ^ 2 ≤
      (L : ℝ) * ∑ s ∈ Finset.range (N + L - 1), ∑ i ∈ W s, (v i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (W s) (fun _ => (1 : ℝ)) v
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hWcard : (W s).card ≤ L := by
      have hsub : W s ⊆ Finset.Ico (s + 1 - L) (s + 1) := by
        intro i hi; simp only [W, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hi ⊢; omega
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hc; omega
    have hWcardR : ((W s).card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hWcard
    exact hcs.trans (mul_le_mul_of_nonneg_right hWcardR (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  -- Step 3: Exact count of windows containing `i < N` is `L`
  have hRHS :
      ∑ s ∈ Finset.range (N + L - 1), ∑ i ∈ W s, (v i) ^ 2 =
      (L : ℝ) * ∑ i ∈ Finset.range N, (v i) ^ 2 := by
    have hrew : ∑ s ∈ Finset.range (N + L - 1), ∑ i ∈ W s, (v i) ^ 2 =
        ∑ s ∈ Finset.range (N + L - 1), ∑ i ∈ Finset.range N,
          if i ≤ s ∧ s < i + L then (v i) ^ 2 else 0 :=
      Finset.sum_congr rfl fun s _ => Finset.sum_filter _ _
    rw [hrew, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hfil : (Finset.range (N + L - 1)).filter (fun s => i ≤ s ∧ s < i + L) =
        Finset.Ico i (i + L) := by
      ext s; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfil, Nat.card_Ico]; simp
  rw [hLHS, show (L : ℝ) ^ 2 * ∑ i ∈ Finset.range N, (v i) ^ 2 =
    (L : ℝ) * ((L : ℝ) * ∑ i ∈ Finset.range N, (v i) ^ 2) by ring, ← hRHS]
  exact hCS

/-- Core of Theorem L2-B (Elementary All-`N` Smooth Fejér `SDP_1+` Barrier):
For EVERY `N ≥ 81`, with `L = Nat.sqrt (Nat.sqrt (N^3)) = ⌊N^(3/4)⌋`,
`μ_i = √(N + L) / N`, `X_ii = μ_i`, and `X_ij = (N + min(|i - j|, L)) / N^2` (`i ≠ j`):
1. Symmetry, PSD of `[1, μ^T; μ, X]`, diagonal `X_ii = μ_i`, McCormick/RLT, and all `N - 1`
   exact pointwise Sidon constraints `∑_{i < N - d} X i (i + d) ≤ 1`;
2. All BQP triangle inequalities `X i j + X i k - X j k ≤ μ i`;
3. All 3-AP cuts (`X a b + X b c + X a c ≤ 1`) and all 4-Sidon cuts
   (`X a b + X a c + X a e + X b c + X b e + X c e ≤ 1 ≤ 3`);
4. Exact objective `∑_{i < N} μ i = √(N + L) > √N + (2 / 5) * N^(1/4)`. -/
theorem smooth_fejer_sdp1_core {N : ℕ} (hN81 : 81 ≤ N) :
    let L : ℕ := Nat.sqrt (Nat.sqrt (N ^ 3))
    let p : ℝ := Real.sqrt ((N : ℝ) + (L : ℝ)) / (N : ℝ)
    let μ : ℕ → ℝ := fun _ => p
    let X : ℕ → ℕ → ℝ := fun i j =>
      if i = j then p
      else ((N + min (if i ≤ j then j - i else i - j) L : ℕ) : ℝ) / (N : ℝ) ^ 2
    (∀ i, i < N → ∀ j, j < N → X i j = X j i) ∧
    (∀ (c₀ : ℝ) (v : ℕ → ℝ),
      0 ≤ c₀ ^ 2 + 2 * c₀ * (∑ i ∈ Finset.range N, v i * μ i) +
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j) ∧
    (∀ i, i < N → X i i = μ i) ∧
    (∀ i, i < N → ∀ j, j < N →
      0 ≤ X i j ∧ X i j ≤ μ i ∧ X i j ≤ μ j ∧ μ i + μ j - 1 ≤ X i j) ∧
    (∀ d, 1 ≤ d → d < N → ∑ i ∈ Finset.range (N - d), X i (i + d) ≤ 1) ∧
    (∀ i, i < N → ∀ j, j < N → ∀ k, k < N → i ≠ j → i ≠ k → j ≠ k →
      X i j + X i k - X j k ≤ μ i) ∧
    (∀ a b c, a < b → b < c → c < N → a + c = 2 * b →
      X a b + X b c + X a c ≤ 1) ∧
    (∀ a b c e, a < b → b < c → c < e → e < N → a + e = b + c →
      X a b + X a c + X a e + X b c + X b e + X c e ≤ 3) ∧
    ∑ i ∈ Finset.range N, μ i = Real.sqrt ((N : ℝ) + (L : ℝ)) ∧
    Real.sqrt (N : ℝ) + (2 / 5 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) < ∑ i ∈ Finset.range N, μ i := by
  intro L p μ X
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  -- Introduce `t = N^(1/4) ≥ 3`
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hNposR _
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNposR.le]
    norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    dsimp only [t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNposR.le]
    norm_num
  have ht3 : 3 ≤ t := by
    have h81 : (3 : ℝ) ^ 4 ≤ t ^ 4 := by rw [ht4]; exact_mod_cast hN81
    by_contra hlt; push Not at hlt
    have : t ^ 4 < (3 : ℝ) ^ 4 := pow_lt_pow_left₀ hlt ht_pos.le (by norm_num)
    linarith only [h81, this]
  -- Exact bounds `L^4 ≤ N^3 < (L + 1)^4`, hence `t^3 - 1 < L ≤ t^3`
  have hL4_le : L ^ 4 ≤ N ^ 3 := by
    have h1 : L * L ≤ Nat.sqrt (N ^ 3) := Nat.sqrt_le (Nat.sqrt (N ^ 3))
    have h2 : Nat.sqrt (N ^ 3) * Nat.sqrt (N ^ 3) ≤ N ^ 3 := Nat.sqrt_le (N ^ 3)
    have h3 : (L * L) * (L * L) ≤ Nat.sqrt (N ^ 3) * Nat.sqrt (N ^ 3) := Nat.mul_le_mul h1 h1
    nlinarith only [h2, h3]
  have hN3_lt : N ^ 3 < (L + 1) ^ 4 := by
    have h1 : Nat.sqrt (N ^ 3) < (L + 1) * (L + 1) := Nat.lt_succ_sqrt (Nat.sqrt (N ^ 3))
    have h2 : N ^ 3 < (Nat.sqrt (N ^ 3) + 1) * (Nat.sqrt (N ^ 3) + 1) := Nat.lt_succ_sqrt (N ^ 3)
    have h3 : Nat.sqrt (N ^ 3) + 1 ≤ (L + 1) * (L + 1) := h1
    have h4 : (Nat.sqrt (N ^ 3) + 1) * (Nat.sqrt (N ^ 3) + 1) ≤
        ((L + 1) * (L + 1)) * ((L + 1) * (L + 1)) := Nat.mul_le_mul h3 h3
    nlinarith only [h2, h4]
  have hL_le_t3 : (L : ℝ) ≤ t ^ 3 := by
    have hpow : (L : ℝ) ^ 4 ≤ (t ^ 3) ^ 4 := by
      have : (t ^ 3) ^ 4 = (t ^ 4) ^ 3 := by ring
      rw [this, ht4]; exact_mod_cast hL4_le
    by_contra hlt; push Not at hlt
    have : (t ^ 3) ^ 4 < (L : ℝ) ^ 4 := pow_lt_pow_left₀ hlt (pow_nonneg ht_pos.le 3) (by norm_num)
    linarith only [hpow, this]
  have ht3_lt_L1 : t ^ 3 < (L : ℝ) + 1 := by
    have hpow : (t ^ 3) ^ 4 < ((L : ℝ) + 1) ^ 4 := by
      have : (t ^ 3) ^ 4 = (t ^ 4) ^ 3 := by ring
      rw [this, ht4]; exact_mod_cast hN3_lt
    by_contra hle; push Not at hle
    have : ((L : ℝ) + 1) ^ 4 ≤ (t ^ 3) ^ 4 := pow_le_pow_left₀ (by positivity) hle 4
    linarith only [hpow, this]
  have hL1 : 1 ≤ L := by
    by_contra h0
    have : L = 0 := by omega
    rw [this, Nat.cast_zero, zero_add] at ht3_lt_L1
    have : (3 : ℝ) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht3 3
    linarith only [ht3_lt_L1, this]
  -- Key algebraic bounds for `t ≥ 3`:
  -- (a) `6 * (N + L) ≤ N^2`  (giving `p^2 ≤ 1/6`, `p ≤ 1/2`)
  have h6NL : 6 * ((N : ℝ) + (L : ℝ)) ≤ (N : ℝ) ^ 2 := by
    rw [← ht4]
    have ht3_le_t4 : t ^ 3 ≤ t ^ 4 := by nlinarith only [ht3, pow_pos ht_pos 3]
    have ht4_ge81 : 81 ≤ t ^ 4 := by
      have : (3 : ℝ) ^ 4 ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) ht3 4
      linarith only [this]
    nlinarith only [hL_le_t3, ht3_le_t4, ht4_ge81]
  have hp_nn : 0 ≤ p := by dsimp only [p]; positivity
  have hp_sq : p ^ 2 = ((N : ℝ) + (L : ℝ)) / (N : ℝ) ^ 2 := by
    dsimp only [p]
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hp_sq_le : p ^ 2 ≤ 1 / 6 := by
    rw [hp_sq, div_le_div_iff₀ (sq_pos_of_pos hNposR) (by norm_num)]
    linarith only [h6NL]
  have hp_le_half : p ≤ 1 / 2 := by nlinarith only [hp_nn, hp_sq_le]
  -- (b) `2 * L^2 + N ≤ N * L`, giving `(L^2 + N)^2 ≤ N^2 * (N + L)`, hence `0 ≤ p - 1/N - L^2/N^2`
  have hPSD_coeff : 0 ≤ p - 1 / (N : ℝ) - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    have h2L2N : 2 * (L : ℝ) ^ 2 + (N : ℝ) ≤ (N : ℝ) * (L : ℝ) := by
      rw [← ht4]
      have hL2 : (L : ℝ) ^ 2 ≤ t ^ 6 := by
        have := pow_le_pow_left₀ (Nat.cast_nonneg L) hL_le_t3 2
        linarith only [this]
      have ht2_ge9 : 9 ≤ t ^ 2 := by nlinarith only [ht3]
      have hpoly : 0 ≤ t ^ 4 * (t ^ 2 * (t - 2) - 2) := by
        have : 0 ≤ t ^ 2 * (t - 2) - 2 := by nlinarith only [ht3, ht2_ge9]
        exact mul_nonneg (pow_nonneg ht_pos.le 4) this
      have hstep : t ^ 4 * (t ^ 3 - 1) ≤ t ^ 4 * (L : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith only [ht3_lt_L1]) (pow_nonneg ht_pos.le 4)
      nlinarith only [hL2, hpoly, hstep]
    have hL4R : (L : ℝ) ^ 4 ≤ (N : ℝ) ^ 3 := by exact_mod_cast hL4_le
    have hsq_ineq : ((L : ℝ) ^ 2 + (N : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 * ((N : ℝ) + (L : ℝ)) := by
      nlinarith only [hL4R, h2L2N, hNposR]
    have hle_sqrt : (L : ℝ) ^ 2 + (N : ℝ) ≤ (N : ℝ) * Real.sqrt ((N : ℝ) + (L : ℝ)) := by
      have h1 : ((L : ℝ) ^ 2 + (N : ℝ)) ^ 2 ≤ ((N : ℝ) * Real.sqrt ((N : ℝ) + (L : ℝ))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; exact hsq_ineq
      have h2 : 0 ≤ (N : ℝ) * Real.sqrt ((N : ℝ) + (L : ℝ)) := by positivity
      nlinarith only [h1, h2]
    have hrew : p - 1 / (N : ℝ) - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 =
        ((N : ℝ) * Real.sqrt ((N : ℝ) + (L : ℝ)) - ((L : ℝ) ^ 2 + (N : ℝ))) / (N : ℝ) ^ 2 := by
      dsimp only [p]; field_simp [hNposR.ne']; ring
    rw [hrew]
    exact div_nonneg (by linarith only [hle_sqrt]) (sq_nonneg _)
  -- Helper: off-diagonal `0 ≤ X i j ≤ p^2`
  have hX_off_bounds : ∀ i j, i ≠ j → 0 ≤ X i j ∧ X i j ≤ p ^ 2 := by
    intro i j hij
    dsimp only [X]
    rw [if_neg hij, hp_sq]
    constructor
    · positivity
    · refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      have hmin : min (if i ≤ j then j - i else i - j) L ≤ L := min_le_right _ _
      exact_mod_cast Nat.add_le_add_left hmin N
  -- Assemble all 10 properties
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Symmetry
    intro i _ j _
    dsimp only [X]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      have hdist : (if i ≤ j then j - i else i - j) = (if j ≤ i then i - j else j - i) := by
        split_ifs <;> omega
      rw [hdist]
  · -- 2. PSD of `[1, μ^T; μ, X]`
    intro c₀ v
    have hX_id : ∀ i j, X i j = p ^ 2 + (if i = j then p - 1 / (N : ℝ) else 0) -
        ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
      intro i j
      dsimp only [X]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl, if_pos (le_refl i), Nat.sub_self, Nat.sub_zero, hp_sq]
        field_simp [hNposR.ne']; ring
      · rw [if_neg hij, if_neg hij, add_zero, hp_sq]
        set d := if i ≤ j then j - i else i - j
        have hadd : N + min d L + (L - d) = N + L := by omega
        have hcast : ((N + min d L : ℕ) : ℝ) = (N : ℝ) + (L : ℝ) - ((L - d : ℕ) : ℝ) := by
          have : ((N + min d L : ℕ) : ℝ) + ((L - d : ℕ) : ℝ) = (N : ℝ) + (L : ℝ) := by
            exact_mod_cast hadd
          linarith only [this]
        rw [hcast]; ring
    have hquad_exp :
        c₀ ^ 2 + 2 * c₀ * (∑ i ∈ Finset.range N, v i * μ i) +
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j =
        (c₀ + p * ∑ i ∈ Finset.range N, v i) ^ 2 +
        (p - 1 / (N : ℝ) - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) * (∑ i ∈ Finset.range N, (v i) ^ 2) +
        (1 / (N : ℝ) ^ 2) *
          ((L : ℝ) ^ 2 * (∑ i ∈ Finset.range N, (v i) ^ 2) -
            ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j) := by
      have h1 : ∑ i ∈ Finset.range N, v i * μ i = p * ∑ i ∈ Finset.range N, v i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by dsimp only [μ]; ring
      have h2 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j =
          p ^ 2 * (∑ i ∈ Finset.range N, v i) ^ 2 +
          (p - 1 / (N : ℝ)) * (∑ i ∈ Finset.range N, (v i) ^ 2) -
          (1 / (N : ℝ) ^ 2) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j := by
        have hterm : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
            v i * X i j * v j =
            (p ^ 2 * (v i * v j)) +
            (if i = j then (p - 1 / (N : ℝ)) * (v i) ^ 2 else 0) -
            (1 / (N : ℝ) ^ 2) * (((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j) := by
          intro i _ j _
          rw [hX_id i j]
          by_cases hij : i = j
          · subst hij; simp only [↓reduceIte]; ring
          · simp only [hij, ↓reduceIte]; ring
        have hsplit : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j =
            (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, p ^ 2 * (v i * v j)) +
            (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              if i = j then (p - 1 / (N : ℝ)) * (v i) ^ 2 else 0) -
            (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              (1 / (N : ℝ) ^ 2) * (((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j hj => hterm i hi j hj
        rw [hsplit]
        have hA : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, p ^ 2 * (v i * v j) =
            p ^ 2 * (∑ i ∈ Finset.range N, v i) ^ 2 := by
          simp_rw [← Finset.mul_sum, sq, Finset.sum_mul]
        have hB : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (if i = j then (p - 1 / (N : ℝ)) * (v i) ^ 2 else 0) =
            (p - 1 / (N : ℝ)) * ∑ i ∈ Finset.range N, (v i) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_ite_eq, if_pos hi]
        have hC : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (1 / (N : ℝ) ^ 2) * (((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j) =
            (1 / (N : ℝ) ^ 2) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
              ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j := by
          simp_rw [← Finset.mul_sum]
        rw [hA, hB, hC]
      rw [h1, h2]; ring
    rw [hquad_exp]
    have ht1 : 0 ≤ (c₀ + p * ∑ i ∈ Finset.range N, v i) ^ 2 := sq_nonneg _
    have ht2' : 0 ≤ (p - 1 / (N : ℝ) - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) *
        ∑ i ∈ Finset.range N, (v i) ^ 2 :=
      mul_nonneg hPSD_coeff (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have ht3' : 0 ≤ (1 / (N : ℝ) ^ 2) *
        ((L : ℝ) ^ 2 * (∑ i ∈ Finset.range N, (v i) ^ 2) -
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ((L - (if i ≤ j then j - i else i - j) : ℕ) : ℝ) * v i * v j) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (fejer_toeplitz_quadratic_le hL1 v))
    linarith only [ht1, ht2', ht3']
  · -- 3. Diagonal integrality `X i i = μ i`
    intro i _; simp [X, μ]
  · -- 4. McCormick / RLT bounds
    intro i _ j _
    by_cases hij : i = j
    · subst hij
      simp only [X, μ, ↓reduceIte]
      exact ⟨hp_nn, le_refl p, le_refl p, by linarith only [hp_le_half]⟩
    · rcases hX_off_bounds i j hij with ⟨h0, hle⟩
      have hp2_le_p : p ^ 2 ≤ p := by nlinarith only [hp_nn, hp_le_half]
      exact ⟨h0, hle.trans hp2_le_p, hle.trans hp2_le_p, by dsimp only [μ]; linarith only [h0, hp_le_half]⟩
  · -- 5. All `N - 1` pointwise Sidon autocorrelation constraints `≤ 1`
    intro d hd1 hdN
    have hconst : ∀ i ∈ Finset.range (N - d),
        X i (i + d) = ((N + min d L : ℕ) : ℝ) / (N : ℝ) ^ 2 := by
      intro i _
      dsimp only [X]
      rw [if_neg (by omega), if_pos (by omega), show i + d - i = d by omega]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnum : ((N - d : ℕ) : ℝ) * ((N + min d L : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have hnat : (N - d) * (N + min d L) ≤ N ^ 2 := by
        have h1 : (N - d) * (N + min d L) ≤ (N - d) * (N + d) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left (min_le_left d L) N)
        have h2 : (N - d) * (N + d) + d * d = N * N := by
          zify [hdN.le]; ring
        nlinarith only [h1, h2]
      exact_mod_cast hnat
    have hrew : ((N - d : ℕ) : ℝ) * (((N + min d L : ℕ) : ℝ) / (N : ℝ) ^ 2) =
        ((N - d : ℕ) : ℝ) * ((N + min d L : ℕ) : ℝ) / (N : ℝ) ^ 2 := by ring
    rw [hrew, div_le_one (sq_pos_of_pos hNposR)]
    exact hnum
  · -- 6. All BQP triangle inequalities `X i j + X i k - X j k ≤ μ i`
    intro i _ j _ k _ hij hik hjk
    have h1 := (hX_off_bounds i j hij).2
    have h2 := (hX_off_bounds i k hik).2
    have h3 := (hX_off_bounds j k hjk).1
    have h2p2 : 2 * p ^ 2 ≤ p := by nlinarith only [hp_nn, hp_le_half]
    dsimp only [μ]
    linarith only [h1, h2, h3, h2p2]
  · -- 7. All 3-AP linear cuts `X a b + X b c + X a c ≤ 1`
    intro a b c hab hbc _ _
    have h1 := (hX_off_bounds a b hab.ne).2
    have h2 := (hX_off_bounds b c hbc.ne).2
    have h3 := (hX_off_bounds a c (lt_trans hab hbc).ne).2
    linarith only [h1, h2, h3, hp_sq_le]
  · -- 8. All 4-Sidon linear cuts `X a b + ... + X c e ≤ 3` (in fact `≤ 1`)
    intro a b c e hab hbc hce _ _
    have h1 := (hX_off_bounds a b hab.ne).2
    have h2 := (hX_off_bounds a c (lt_trans hab hbc).ne).2
    have h3 := (hX_off_bounds a e (lt_trans (lt_trans hab hbc) hce).ne).2
    have h4 := (hX_off_bounds b c hbc.ne).2
    have h5 := (hX_off_bounds b e (lt_trans hbc hce).ne).2
    have h6 := (hX_off_bounds c e hce.ne).2
    linarith only [h1, h2, h3, h4, h5, h6, hp_sq_le]
  · -- 9. Exact objective `∑ μ i = √(N + L)`
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hNposR.ne']
  · -- 10. Explicit lower bound `√N + (2/5) N^(1/4) < ∑ μ i`
    have hsum_eq : ∑ i ∈ Finset.range N, μ i = Real.sqrt ((N : ℝ) + (L : ℝ)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hNposR.ne']
    rw [hsum_eq, ← ht2]
    have hsq : (t ^ 2 + (2 / 5 : ℝ) * t) ^ 2 < (N : ℝ) + (L : ℝ) := by
      rw [← ht4]
      have hpoly : 0 < 5 * t ^ 3 - 4 * t ^ 2 - 25 := by
        have ht2_ge9 : 9 ≤ t ^ 2 := by nlinarith only [ht3]
        nlinarith only [ht3, ht2_ge9]
      linarith only [ht3_lt_L1, hpoly]
    have hsqrt_lt := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    rwa [Real.sqrt_sq (by positivity)] at hsqrt_lt

end Erdos030
