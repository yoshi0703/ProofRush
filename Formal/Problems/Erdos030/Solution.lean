import Problems.Erdos030.Statement
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic

/-!
# Erdős Problem #30 — Formally Verified Milestone Solutions

This file proves the following theorems for `Erdos030.h` without modifying `Statement.lean`,
using only standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. `lindstrom_theorem` (`LindstromStatement`):
   $\forall N \in \mathbb{N},\; h(N) \le \sqrt{N} + N^{1/4} + 1$.
2. `erdos_turan_theorem` (`ErdosTuranStatement`):
   $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + C N^{1/4}$.
3. `kernel_transfer_single`:
   General discrete symmetric kernel–boundary smoothing transfer theorem.
4. `sidon_sub_0949`:
   $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.949 N^{1/4}$ via an exact 16-bin rational certificate
   ($\sqrt{ab} = 0.9486568\ldots < 0.949$).
5. `balogh_furedi_roy_theorem` (`BaloghFurediRoyStatement`),
   `obryant_theorem` (`OBryantStatement`), and
   `carter_hunter_obryant_theorem` (`CarterHunterOBryantStatement`).
6. `bose_lower_bound_theorem` (`BoseLowerBoundStatement`):
   $\forall p$ prime, $p \le h(p^2 - 1)$ via Bose's finite-field construction in $\mathbb{F}_{p^2}^\times$.
-/

namespace Erdos030

open Filter Finset
open scoped BigOperators

/-! ### Section 1: Basic Sidon Set Infrastructure -/

lemma card_le_h {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Finset.Icc 1 N)
    (hS : IsSidon (A : Set ℕ)) : A.card ≤ h N := by
  classical
  unfold h maxSidonSubsetCard
  have hmem : A ∈ (Finset.Icc 1 N).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ)) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hsub, hS⟩
  exact Finset.le_sup (f := Finset.card) hmem

lemma h_zero : h 0 = 0 := by
  unfold h maxSidonSubsetCard
  simp

lemma exists_max_sidon (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ A.card = h N := by
  classical
  let S := (Finset.Icc 1 N).powerset.filter (fun B : Finset ℕ => IsSidon (B : Set ℕ))
  have hne : S.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, ?_⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA_mem, hA_max⟩ := Finset.exists_mem_eq_sup S hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA_mem
  refine ⟨A, hA_mem.1, hA_mem.2, ?_⟩
  unfold h maxSidonSubsetCard
  exact hA_max.symm

lemma exists_max_sidon_range (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.range N ∧ IsSidon (A : Set ℕ) ∧ A.card = h N := by
  obtain ⟨B, hBsub, hBS, hBcard⟩ := exists_max_sidon N
  refine ⟨B.image (· - 1), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
    have hbIcc := Finset.mem_Icc.mp (hBsub hb)
    rw [Finset.mem_range]
    omega
  · intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ heq
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha₁ hb₁ ha₂ hb₂
    rcases ha₁ with ⟨x₁, hx₁, rfl⟩
    rcases hb₁ with ⟨y₁, hy₁, rfl⟩
    rcases ha₂ with ⟨x₂, hx₂, rfl⟩
    rcases hb₂ with ⟨y₂, hy₂, rfl⟩
    have hx₁' := (Finset.mem_Icc.mp (hBsub hx₁)).1
    have hy₁' := (Finset.mem_Icc.mp (hBsub hy₁)).1
    have hx₂' := (Finset.mem_Icc.mp (hBsub hx₂)).1
    have hy₂' := (Finset.mem_Icc.mp (hBsub hy₂)).1
    have hsum : x₁ + y₁ = x₂ + y₂ := by omega
    rcases hBS x₁ hx₁ y₁ hy₁ x₂ hx₂ y₂ hy₂ hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
  · rw [Finset.card_image_of_injOn, hBcard]
    intro x hx y hy hxy
    dsimp only at hxy
    have hx' := (Finset.mem_Icc.mp (hBsub hx)).1
    have hy' := (Finset.mem_Icc.mp (hBsub hy)).1
    omega

lemma sidon_sub_injOn_offDiag {A : Finset ℕ} (hS : IsSidon (A : Set ℕ)) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)) (A.offDiag : Set (ℕ × ℕ)) := by
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  dsimp only at heq
  simp only [Finset.mem_coe, Finset.mem_offDiag] at h₁ h₂
  have hsum : a₁ + b₂ = a₂ + b₁ := by omega
  rcases hS a₁ h₁.1 b₂ h₂.2.1 a₂ h₂.1 b₁ h₁.2.1 hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd rfl h₁.2.2

/-! ### Section 2: Discrete Autocorrelation & Weighted Energy Upper Bound -/

/-- Discrete autocorrelation of a finitely supported kernel `K : ℤ → ℝ` supported on `[0, H)`. -/
def autocorr (H : ℕ) (K : ℤ → ℝ) (d : ℤ) : ℝ :=
  ∑ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + d)

lemma autocorr_nonneg (H : ℕ) {K : ℤ → ℝ} (hK_nonneg : ∀ z, 0 ≤ K z) (d : ℤ) :
    0 ≤ autocorr H K d :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hK_nonneg _) (hK_nonneg _)

lemma sum_autocorr_eq_one {H : ℕ} (hH : 1 ≤ H) {K : ℤ → ℝ}
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0)
    (hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1) :
    ∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), autocorr H K d = 1 := by
  unfold autocorr
  rw [Finset.sum_comm]
  have hinner : ∀ s ∈ Finset.range H,
      ∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), K (s : ℤ) * K ((s : ℤ) + d) = K (s : ℤ) := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [← Finset.mul_sum]
    have hshift :
        ∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), K ((s : ℤ) + d) =
        ∑ t ∈ Finset.range H, K (t : ℤ) := by
      -- Reindex via t = s + d; outside [0, H) kernel vanishes
      have h1 :
          ∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), K ((s : ℤ) + d) =
          ∑ u ∈ Finset.Icc ((s : ℤ) - (H : ℤ) + 1) ((s : ℤ) + (H : ℤ) - 1), K u := by
        refine Finset.sum_nbij (fun d => (s : ℤ) + d) ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_Icc] at hd ⊢
          omega
        · intro d₁ _ d₂ _ h; dsimp only at h; omega
        · intro u hu
          simp only [Finset.mem_coe, Finset.mem_Icc] at hu
          exact ⟨u - s, by simp only [Finset.mem_coe, Finset.mem_Icc]; omega, by ring⟩
        · intro _ _; rfl
      rw [h1]
      have hsub :
          (Finset.range H).image (fun t : ℕ => (t : ℤ)) ⊆
            Finset.Icc ((s : ℤ) - (H : ℤ) + 1) ((s : ℤ) + (H : ℤ) - 1) := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨t, ht, rfl⟩
        rw [Finset.mem_range] at ht
        rw [Finset.mem_Icc]
        omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (by intro x _ y _ h; exact Int.ofNat.inj h)]
      · intro u _ hu
        apply hK_supp
        intro ⟨h0, hlt⟩
        apply hu
        refine Finset.mem_image.mpr ⟨u.toNat, Finset.mem_range.mpr (by omega), by omega⟩
    rw [hshift, hK_sum, mul_one]
  rw [Finset.sum_congr rfl hinner, hK_sum]

lemma energy_upper_bound {A : Finset ℕ} {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hA : A ⊆ Finset.range N) (hS : IsSidon (A : Set ℕ))
    {K : ℤ → ℝ} (hK_nonneg : ∀ z, 0 ≤ K z)
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0)
    (hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1) :
    ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) ^ 2 ≤
      1 + ((A.card : ℝ) - 1) * autocorr H K 0 := by
  -- Expand square and interchange sums
  have hexpand :
      ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) ^ 2 =
      ∑ a ∈ A, ∑ b ∈ A, autocorr H K ((a : ℤ) - (b : ℤ)) := by
    calc
      ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) ^ 2
        = ∑ n ∈ Finset.range (N + H - 1),
            ∑ a ∈ A, ∑ b ∈ A, K ((n : ℤ) - (a : ℤ)) * K ((n : ℤ) - (b : ℤ)) := by
              refine Finset.sum_congr rfl fun n _ => ?_
              rw [sq, Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ a ∈ A, ∑ b ∈ A,
            ∑ n ∈ Finset.range (N + H - 1), K ((n : ℤ) - (a : ℤ)) * K ((n : ℤ) - (b : ℤ)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.sum_comm]
      _ = ∑ a ∈ A, ∑ b ∈ A, autocorr H K ((a : ℤ) - (b : ℤ)) := by
              refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
              unfold autocorr
              have haN := Finset.mem_range.mp (hA ha)
              -- Reindex s = n - a; terms outside a ≤ n < a + H vanish
              have hsub : (Finset.range H).image (fun s => a + s) ⊆ Finset.range (N + H - 1) := by
                intro n hn
                rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
                rw [Finset.mem_range] at hs ⊢
                omega
              rw [← Finset.sum_subset hsub]
              · rw [Finset.sum_image (by intro x _ y _ h; dsimp only at h; omega)]
                refine Finset.sum_congr rfl fun s _ => ?_
                have h1 : ((a + s : ℕ) : ℤ) - (a : ℤ) = (s : ℤ) := by omega
                have h2 : ((a + s : ℕ) : ℤ) - (b : ℤ) = (s : ℤ) + ((a : ℤ) - (b : ℤ)) := by omega
                rw [h1, h2]
              · intro n _ hn
                have hzero : K ((n : ℤ) - (a : ℤ)) = 0 := by
                  apply hK_supp
                  intro ⟨h0, hlt⟩
                  apply hn
                  refine Finset.mem_image.mpr ⟨n - a, Finset.mem_range.mpr (by omega), by omega⟩
                rw [hzero, zero_mul]
  rw [hexpand]
  -- Split into diagonal (a = b) and off-diagonal (a ≠ b)
  have hsplit :
      ∑ a ∈ A, ∑ b ∈ A, autocorr H K ((a : ℤ) - (b : ℤ)) =
      (A.card : ℝ) * autocorr H K 0 +
      ∑ p ∈ A.offDiag, autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) := by
    rw [← Finset.sum_product']
    have hunion : A ×ˢ A = A.diag ∪ A.offDiag := (Finset.diag_union_offDiag A).symm
    have hdisj : Disjoint A.diag A.offDiag := Finset.disjoint_diag_offDiag A
    rw [hunion, Finset.sum_union hdisj]
    congr 1
    rw [Finset.diag_eq_filter]
    have : ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ _p ∈ (A ×ˢ A).filter (fun p => p.1 = p.2), autocorr H K 0 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      rw [hp.2, sub_self]
    rw [this, Finset.sum_const, ← Finset.diag_eq_filter, Finset.diag_card, nsmul_eq_mul]
  rw [hsplit]
  -- Bound the off-diagonal sum by ∑_{d ∈ [-(H-1), H-1] \ {0}} autocorr H K d
  have hoff :
      ∑ p ∈ A.offDiag, autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) ≤
      (∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), autocorr H K d) - autocorr H K 0 := by
    let I := (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)).erase 0
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1) := by
      rw [Finset.mem_Icc]; omega
    have hIeq :
        ∑ d ∈ I, autocorr H K d =
        (∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), autocorr H K d) - autocorr H K 0 := by
      have := Finset.add_sum_erase (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)) (autocorr H K) h0mem
      linarith
    rw [← hIeq]
    -- Restrict offDiag to pairs whose difference lies in I (outside I, autocorr = 0)
    let D := A.offDiag.filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) ∈ I)
    have hD_eq :
        ∑ p ∈ A.offDiag, autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ p ∈ D, autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpD => ?_
      rw [Finset.mem_filter] at hpD
      have hnotI : (p.1 : ℤ) - (p.2 : ℤ) ∉ I := fun h => hpD ⟨hp, h⟩
      rw [Finset.mem_offDiag] at hp
      have hne0 : (p.1 : ℤ) - (p.2 : ℤ) ≠ 0 := by omega
      have hout : ¬(-(H : ℤ) + 1 ≤ (p.1 : ℤ) - (p.2 : ℤ) ∧
          (p.1 : ℤ) - (p.2 : ℤ) ≤ (H : ℤ) - 1) := by
        intro hmem
        apply hnotI
        exact Finset.mem_erase.mpr ⟨hne0, Finset.mem_Icc.mpr hmem⟩
      unfold autocorr
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_range] at hs
      have hzero : K ((s : ℤ) + ((p.1 : ℤ) - (p.2 : ℤ))) = 0 := by
        apply hK_supp
        omega
      rw [hzero, mul_zero]
    rw [hD_eq]
    -- Image of D under (p.1 - p.2) is a subset of I, and map is injective on D ⊆ offDiag
    have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ)) (D : Set (ℕ × ℕ)) :=
      (sidon_sub_injOn_offDiag hS).mono (by exact Finset.filter_subset _ _)
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => autocorr_nonneg H hK_nonneg d)
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.mp hp).2
  have hsum1 := sum_autocorr_eq_one hH hK_supp hK_sum
  linarith

/-! ### Section 3: Lindström's Theorem (1969) & Erdős–Turán's Bound (1941) -/

/-- Classical uniform-window master inequality (Erdős–Turán / Lindström):
for any Sidon set `A ⊆ range N` of size `k` and any `H ≥ 1`,
`k^2 * H ≤ (N + H - 1) * (H + k - 1)`. -/
lemma uniform_master_ineq {A : Finset ℕ} {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hA : A ⊆ Finset.range N) (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ^ 2 * (H : ℝ) ≤
      ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + (A.card : ℝ) - 1) := by
  let K : ℤ → ℝ := fun z => if 0 ≤ z ∧ z < H then (1 : ℝ) / (H : ℝ) else 0
  have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr (by omega)
  have hK_nonneg : ∀ z, 0 ≤ K z := by
    intro z; dsimp only [K]; split_ifs <;> positivity
  have hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0 := by
    intro z hz; dsimp only [K]; rw [if_neg hz]
  have hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1 := by
    have : ∀ s ∈ Finset.range H, K (s : ℤ) = (1 : ℝ) / (H : ℝ) := by
      intro s hs
      rw [Finset.mem_range] at hs
      dsimp only [K]
      rw [if_pos ⟨by omega, by omega⟩]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hC0 : autocorr H K 0 = 1 / (H : ℝ) := by
    unfold autocorr
    have : ∀ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + 0) = (1 / (H : ℝ)) ^ 2 := by
      intro s hs
      rw [Finset.mem_range] at hs
      dsimp only [K]
      rw [add_zero, if_pos ⟨by omega, by omega⟩, sq]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  -- Sum of u(n) over J = range (N + H - 1) equals A.card
  have hsum_u :
      ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) = (A.card : ℝ) := by
    rw [Finset.sum_comm]
    have hinner : ∀ x ∈ A,
        ∑ n ∈ Finset.range (N + H - 1), K ((n : ℤ) - (x : ℤ)) = 1 := by
      intro x hx
      have hxN := Finset.mem_range.mp (hA hx)
      have hsub : (Finset.range H).image (fun s => x + s) ⊆ Finset.range (N + H - 1) := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
        rw [Finset.mem_range] at hs ⊢
        omega
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (by intro a _ b _ h; dsimp only at h; omega)]
        convert hK_sum using 2 with s
        congr 1; omega
      · intro n _ hn
        apply hK_supp
        intro ⟨h0, hlt⟩
        apply hn
        exact Finset.mem_image.mpr ⟨n - x, Finset.mem_range.mpr (by omega), by omega⟩
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Cauchy–Schwarz on J
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
    (fun _ => (1 : ℝ)) (fun n => ∑ x ∈ A, K ((n : ℤ) - (x : ℤ)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  rw [hsum_u] at hcs
  have hcardJ : ((N + H - 1 : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) - 1 := by
    have : 1 ≤ N + H := by omega
    rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_one]
  rw [hcardJ] at hcs
  have henergy := energy_upper_bound hN hH hA hS hK_nonneg hK_supp hK_sum
  rw [hC0] at henergy
  have hJnonneg : (0 : ℝ) ≤ (N : ℝ) + (H : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hcomb : (A.card : ℝ) ^ 2 ≤ ((N : ℝ) + (H : ℝ) - 1) * (1 + ((A.card : ℝ) - 1) * (1 / (H : ℝ))) :=
    hcs.trans (mul_le_mul_of_nonneg_left henergy hJnonneg)
  have hmul := mul_le_mul_of_nonneg_right hcomb hHpos.le
  have hident :
      ((N : ℝ) + (H : ℝ) - 1) * (1 + ((A.card : ℝ) - 1) * (1 / (H : ℝ))) * (H : ℝ) =
      ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + (A.card : ℝ) - 1) := by
    field_simp
    ring
  linarith

/-- Lindström's Theorem (1969) / Erdős–Turán (1941):
for every $N \in \mathbb{N}$, $h(N) \le \sqrt{N} + N^{1/4} + 1$. -/
theorem lindstrom_theorem : LindstromStatement := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp [h_zero]
  obtain ⟨A, hAsub, hAS, hAcard⟩ := exists_max_sidon_range N
  rw [← hAcard]
  -- Let t = N^(1/4) ≥ 1, so t^2 = √N and t^4 = N
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  have ht1 : (1 : ℝ) ≤ t := Real.one_le_rpow hN1 (by norm_num)
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  -- Choose H = ⌊t^3⌋ + 1, so H = t^3 + d with 0 < d ≤ 1
  let H : ℕ := Nat.floor (t ^ 3) + 1
  have hHpos : 1 ≤ H := Nat.succ_pos _
  have hmaster := uniform_master_ineq hNpos hHpos hAsub hAS
  set d : ℝ := (H : ℝ) - t ^ 3
  have hd_pos : 0 < d := by
    dsimp only [d, H]
    rw [Nat.cast_add, Nat.cast_one]
    have := Nat.lt_floor_add_one (t ^ 3)
    linarith
  have hd_le : d ≤ 1 := by
    dsimp only [d, H]
    rw [Nat.cast_add, Nat.cast_one]
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ t ^ 3)
    linarith
  have hH_eq : (H : ℝ) = t ^ 3 + d := by ring
  -- Proof by contradiction: if k > t^2 + t + 1, then (N + H - 1)(H + k - 1) < k^2 * H
  by_contra hgt
  push_neg at hgt
  set k : ℝ := (A.card : ℝ)
  have hk_gt : t ^ 2 + t + 1 < k := by linarith [ht2]
  have hN_eq : (N : ℝ) = t ^ 4 := ht4.symm
  rw [hN_eq, hH_eq] at hmaster
  -- Let δ = k - (t^2 + t + 1) > 0; expand k^2 H - (t^4 + t^3 + d - 1)(t^3 + d + k - 1) > 0
  set δ : ℝ := k - (t ^ 2 + t + 1)
  have hδ : 0 < δ := by linarith
  have hk_eq : k = t ^ 2 + t + 1 + δ := by ring
  rw [hk_eq] at hmaster
  have hpoly :
      (t ^ 2 + t + 1 + δ) ^ 2 * (t ^ 3 + d) -
        (t ^ 4 + (t ^ 3 + d) - 1) * (t ^ 3 + d + (t ^ 2 + t + 1 + δ) - 1) =
      (t ^ 5 + t ^ 4 + 2 * t ^ 3 + (2 * d + 1) * t ^ 2 + (d + 1) * t + d * (2 - d)) +
      δ * (2 * t ^ 5 + t ^ 4 + t ^ 3 + 2 * d * t ^ 2 + 2 * d * t + d + 1) +
      δ ^ 2 * (t ^ 3 + d) := by ring
  have hpos :
      0 < (t ^ 5 + t ^ 4 + 2 * t ^ 3 + (2 * d + 1) * t ^ 2 + (d + 1) * t + d * (2 - d)) +
          δ * (2 * t ^ 5 + t ^ 4 + t ^ 3 + 2 * d * t ^ 2 + 2 * d * t + d + 1) +
          δ ^ 2 * (t ^ 3 + d) := by
    have h1 : 0 < t ^ 5 + t ^ 4 + 2 * t ^ 3 + (2 * d + 1) * t ^ 2 + (d + 1) * t + d * (2 - d) := by
      nlinarith
    have h2 : 0 < δ * (2 * t ^ 5 + t ^ 4 + t ^ 3 + 2 * d * t ^ 2 + 2 * d * t + d + 1) := by
      have : 0 < 2 * t ^ 5 + t ^ 4 + t ^ 3 + 2 * d * t ^ 2 + 2 * d * t + d + 1 := by nlinarith
      exact mul_pos hδ this
    have h3 : 0 ≤ δ ^ 2 * (t ^ 3 + d) := by positivity
    linarith
  linarith

/-- Erdős–Turán's Upper Bound (1941): $h(N) \le \sqrt{N} + O(N^{1/4})$. -/
theorem erdos_turan_theorem : ErdosTuranStatement := by
  refine ⟨2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hl := lindstrom_theorem N
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  linarith

/-! ### Section 4: General Discrete Kernel–Boundary Smoothing Transfer Theorem -/

lemma add_mul_div_self_right_lt {q hh r : ℕ} (hhh : 0 < hh) (hr : r < hh) :
    (q * hh + r) / hh = q := by
  rw [mul_comm q hh, Nat.mul_add_div hhh, Nat.div_eq_of_lt hr, add_zero]

/-- Reindexing helper: summing over `range (m * hh)` splits into blocks `i ∈ range m`
and offsets `r ∈ range hh`. -/
lemma sum_range_mul_blocks (m hh : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range (m * hh), f s =
      ∑ i ∈ Finset.range m, ∑ r ∈ Finset.range hh, f (i * hh + r) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij (fun p : ℕ × ℕ => p.1 * hh + p.2) ?_ ?_ ?_ ?_).symm
  · intro ⟨i, r⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp ⊢
    calc i * hh + r < i * hh + hh := by omega
      _ = (i + 1) * hh := by ring
      _ ≤ m * hh := Nat.mul_le_mul_right hh hp.1
  · intro ⟨i₁, r₁⟩ h₁ ⟨i₂, r₂⟩ h₂ heq
    dsimp only at heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h₁ h₂
    have hhh : 0 < hh := by omega
    have hdiv1 : (i₁ * hh + r₁) / hh = i₁ := add_mul_div_self_right_lt hhh h₁.2
    have hdiv2 : (i₂ * hh + r₂) / hh = i₂ := add_mul_div_self_right_lt hhh h₂.2
    have hi : i₁ = i₂ := by rw [← hdiv1, ← hdiv2, heq]
    subst hi
    exact Prod.ext rfl (by omega)
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_range] at hs
    have hhh : 0 < hh := by
      by_contra h0; push Not at h0; have : hh = 0 := by omega
      subst this; simp at hs
    refine ⟨(s / hh, s % hh), ?_, Nat.div_add_mod' s hh⟩
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm]), Nat.mod_lt s hhh⟩
  · intro _ _; rfl

/-- Core discrete smoothing master inequality for a single symmetric kernel–boundary pair `(p, w)`:
if `N ≥ 2 * L * (m * hh)` and `A ⊆ range N` is Sidon, then
`|A|^2 ≤ (N + b * H - 1) * (1 + a * (|A| - 1) / H)` with `H = m * hh`. -/
lemma block_kernel_master_ineq {m L hh N : ℕ}
    (hm : 1 ≤ m) (hL : 1 ≤ L) (hhh : 1 ≤ hh)
    (hN_large : 2 * L * (m * hh) ≤ N)
    {p w : ℕ → ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hp_symm : ∀ i, i < m → p (m - 1 - i) = p i)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    {A : Finset ℕ} (hA : A ⊆ Finset.range N) (hS : IsSidon (A : Set ℕ)) :
    let H := m * hh
    let a := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
    let b := 1 + 2 * ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
    (A.card : ℝ) ^ 2 ≤
      ((N : ℝ) + b * (H : ℝ) - 1) * (1 + ((A.card : ℝ) - 1) * (a / (H : ℝ))) := by
  intro H a b
  have hHpos : 1 ≤ H := Nat.mul_pos hm hhh
  have hLH_pos : 1 ≤ L * H := Nat.mul_pos hL hHpos
  have hN2LH : 2 * (L * H) ≤ N := by
    have hmul : 2 * (L * H) = 2 * L * (m * hh) := by dsimp only [H]; ring
    omega
  have hNpos : 1 ≤ N := by omega
  have hhh_pos : (0 : ℝ) < (hh : ℝ) := Nat.cast_pos.mpr hhh
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hH_pos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hHpos
  -- Define block-constant discrete kernel K on ℤ
  let K : ℤ → ℝ := fun z => if 0 ≤ z ∧ z < (H : ℤ) then p (z.toNat / hh) / (hh : ℝ) else 0
  have hK_nat : ∀ s, s < H → K (s : ℤ) = p (s / hh) / (hh : ℝ) := by
    intro s hs
    dsimp only [K]
    rw [if_pos ⟨by omega, by omega⟩]
    simp
  have hK_nonneg : ∀ z : ℤ, 0 ≤ K z := by
    intro z
    dsimp only [K]
    split_ifs with hz
    · apply div_nonneg
      · apply hp_nonneg
        have : z.toNat < m * hh := by omega
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      · exact hhh_pos.le
    · exact le_refl 0
  have hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < (H : ℤ)) → K z = 0 := by
    intro z hz
    dsimp only [K]
    rw [if_neg hz]
  -- 1. Total mass of K is 1
  have hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1 := by
    have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) =
        ∑ s ∈ Finset.range (m * hh), p (s / hh) / (hh : ℝ) :=
      Finset.sum_congr rfl fun s hs => hK_nat s (Finset.mem_range.mp hs)
    rw [hcongr, sum_range_mul_blocks]
    have hblock : ∀ i ∈ Finset.range m,
        ∑ r ∈ Finset.range hh, p ((i * hh + r) / hh) / (hh : ℝ) = p i := by
      intro i _
      have hdiv : ∀ r ∈ Finset.range hh, p ((i * hh + r) / hh) / (hh : ℝ) = p i / (hh : ℝ) := by
        intro r hr
        rw [Finset.mem_range] at hr
        rw [add_mul_div_self_right_lt hhh hr]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hblock, hp_sum]
  -- 2. Symmetry of K: K (H - 1 - s) = K s for s < H
  have hK_symm : ∀ s, s < H → K ((H - 1 - s : ℕ) : ℤ) = K (s : ℤ) := by
    intro s hs
    rw [hK_nat (H - 1 - s) (by omega), hK_nat s hs]
    congr 1
    have hlt : s / hh < m := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have hdiv_refl : (H - 1 - s) / hh = m - 1 - s / hh := by
      have h1 : s = (s / hh) * hh + s % hh := (Nat.div_add_mod' s hh).symm
      have h2 : s % hh < hh := Nat.mod_lt s hhh
      have h3 : H - 1 - s = (m - 1 - s / hh) * hh + (hh - 1 - s % hh) := by
        have hHdef : H = m * hh := rfl
        have hmul : (m - 1 - s / hh) * hh + (s / hh) * hh + hh = m * hh := by
          have : m - 1 - s / hh + s / hh + 1 = m := by omega
          calc (m - 1 - s / hh) * hh + (s / hh) * hh + hh
              = (m - 1 - s / hh + s / hh + 1) * hh := by ring
            _ = m * hh := by rw [this]
        omega
      rw [h3, add_mul_div_self_right_lt hhh (by omega)]
    rw [hdiv_refl, hp_symm (s / hh) hlt]
  -- 3. Autocorrelation at 0 equals a / H
  have hC0 : autocorr H K 0 = a / (H : ℝ) := by
    unfold autocorr
    have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + 0) =
        ∑ s ∈ Finset.range (m * hh), (p (s / hh) / (hh : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [add_zero, hK_nat s (Finset.mem_range.mp hs), sq]
    rw [hcongr, sum_range_mul_blocks]
    have hblock : ∀ i ∈ Finset.range m,
        ∑ r ∈ Finset.range hh, (p ((i * hh + r) / hh) / (hh : ℝ)) ^ 2 = (p i) ^ 2 / (hh : ℝ) := by
      intro i _
      have hdiv : ∀ r ∈ Finset.range hh,
          (p ((i * hh + r) / hh) / (hh : ℝ)) ^ 2 = (p i) ^ 2 / (hh : ℝ) ^ 2 := by
        intro r hr
        rw [Finset.mem_range] at hr
        rw [add_mul_div_self_right_lt hhh hr, div_pow]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hblock, ← Finset.sum_div]
    dsimp only [a, H]
    rw [Nat.cast_mul]
    field_simp
  -- 4. Define reflected boundary weight Q on J = range (N + H - 1)
  let Q : ℕ → ℝ := fun n =>
    if n < L * H then w (n / hh)
    else if N + H - 2 - n < L * H then w ((N + H - 2 - n) / hh)
    else 1
  -- Symmetry of Q on [0, N + H - 2]: Q (N + H - 2 - n) = Q n
  have hQ_symm : ∀ n, n < N + H - 1 → Q (N + H - 2 - n) = Q n := by
    intro n hn
    have hrefl : N + H - 2 - (N + H - 2 - n) = n := by omega
    dsimp only [Q]
    by_cases h1 : n < L * H
    · have h2 : ¬(N + H - 2 - n < L * H) := by omega
      rw [if_pos h1, if_neg h2, hrefl, if_pos h1]
    · by_cases h2 : N + H - 2 - n < L * H
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, hrefl, if_neg h1]
  -- 5. Compute ∑_{n ∈ J} Q(n)^2 = N + b * H - 1
  have hQ_norm : ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 = (N : ℝ) + b * (H : ℝ) - 1 := by
    have hLH_le : L * H ≤ N + H - 1 - L * H := by omega
    have hB_le : N + H - 1 - L * H ≤ N + H - 1 := by omega
    -- Split range (N + H - 1) into [0, LH), [LH, N+H-1-LH), [N+H-1-LH, N+H-1)
    have hsplit1 :
        ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 =
        (∑ n ∈ Finset.range (N + H - 1 - L * H), (Q n) ^ 2) +
        (∑ n ∈ Finset.Ico (N + H - 1 - L * H) (N + H - 1), (Q n) ^ 2) := by
      rw [← Finset.sum_range_add_sum_Ico _ hB_le]
    have hsplit2 :
        ∑ n ∈ Finset.range (N + H - 1 - L * H), (Q n) ^ 2 =
        (∑ n ∈ Finset.range (L * H), (Q n) ^ 2) +
        (∑ n ∈ Finset.Ico (L * H) (N + H - 1 - L * H), (Q n) ^ 2) := by
      rw [← Finset.sum_range_add_sum_Ico _ hLH_le]
    rw [hsplit1, hsplit2]
    -- Left boundary sum
    have hleft : ∑ n ∈ Finset.range (L * H), (Q n) ^ 2 =
        (hh : ℝ) * ∑ j ∈ Finset.range (L * m), (w j) ^ 2 := by
      have hcongr : ∑ n ∈ Finset.range (L * H), (Q n) ^ 2 =
          ∑ n ∈ Finset.range ((L * m) * hh), (w (n / hh)) ^ 2 := by
        have hLHm : L * H = (L * m) * hh := by dsimp only [H]; ring
        rw [hLHm]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [Finset.mem_range] at hn
        dsimp only [Q]
        rw [if_pos (by omega)]
      rw [hcongr, sum_range_mul_blocks]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hdiv : ∀ r ∈ Finset.range hh, (w ((j * hh + r) / hh)) ^ 2 = (w j) ^ 2 := by
        intro r hr
        rw [Finset.mem_range] at hr
        rw [add_mul_div_self_right_lt hhh hr]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- Right boundary sum equals left boundary sum by reflection
    have hright : ∑ n ∈ Finset.Ico (N + H - 1 - L * H) (N + H - 1), (Q n) ^ 2 =
        ∑ n ∈ Finset.range (L * H), (Q n) ^ 2 := by
      refine Finset.sum_nbij (fun n => N + H - 2 - n) ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_Ico, Finset.mem_range] at hn ⊢
        omega
      · intro n₁ h₁ n₂ h₂ heq
        dsimp only at heq
        simp only [Finset.mem_coe, Finset.mem_Ico] at h₁ h₂
        omega
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_range] at hk
        refine ⟨N + H - 2 - k, ?_, by dsimp only; omega⟩
        simp only [Finset.mem_coe, Finset.mem_Ico]
        omega
      · intro n hn
        simp only [Finset.mem_coe, Finset.mem_Ico] at hn
        rw [hQ_symm n hn.2]
    -- Interior sum equals (N + H - 1 - 2 * L * H)
    have hmid : ∑ n ∈ Finset.Ico (L * H) (N + H - 1 - L * H), (Q n) ^ 2 =
        ((N + H - 1 - 2 * (L * H) : ℕ) : ℝ) := by
      have h1 : ∀ n ∈ Finset.Ico (L * H) (N + H - 1 - L * H), (Q n) ^ 2 = 1 := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        dsimp only [Q]
        rw [if_neg (by omega), if_neg (by omega), one_pow]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      congr 1; omega
    rw [hright, hleft, hmid]
    have hcast_mid : ((N + H - 1 - 2 * (L * H) : ℕ) : ℝ) =
        (N : ℝ) + (H : ℝ) - 1 - 2 * (L : ℝ) * (H : ℝ) := by
      have hge : 2 * (L * H) + 1 ≤ N + H := by omega
      have : N + H - 1 - 2 * (L * H) = N + H - (2 * (L * H) + 1) := by omega
      rw [this, Nat.cast_sub hge]
      push_cast
      ring
    rw [hcast_mid]
    dsimp only [b, H]
    rw [Nat.cast_mul]
    field_simp
    ring
  -- 6. Pointwise covering inequality: ∀ x < N, 1 ≤ ∑ s ∈ range H, K s * Q (x + s)
  -- First prove left-boundary case: ∀ x < L * H, 1 ≤ ∑ s ∈ range H, K s * Q (x + s)
  have hcover_left : ∀ x, x < L * H → 1 ≤ ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) := by
    intro x hx
    let q := x / hh
    let t := x % hh
    have hq_lt : q < L * m := by
      have : x < (L * m) * hh := by dsimp only [H] at hx; linarith
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have ht_lt : t < hh := Nat.mod_lt x hhh
    have hx_eq : x = q * hh + t := (Nat.div_add_mod' x hh).symm
    -- Every x + s (s < H) avoids the right boundary, so Q (x + s) = w ((x + s) / hh)
    have hQ_val : ∀ s, s < H → Q (x + s) = w ((x + s) / hh) := by
      intro s hs
      dsimp only [Q]
      by_cases hlt : x + s < L * H
      · rw [if_pos hlt]
      · have hnotR : ¬(N + H - 2 - (x + s) < L * H) := by omega
        rw [if_neg hlt, if_neg hnotR]
        symm
        apply hw_tail
        have hLHm : L * m * hh ≤ x + s := by
          have : L * H = L * m * hh := by dsimp only [H]; ring
          omega
        exact (Nat.le_div_iff_mul_le hhh).mpr hLHm
    have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
        ∑ s ∈ Finset.range (m * hh), (p (s / hh) / (hh : ℝ)) * w ((x + s) / hh) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [hK_nat s hs, hQ_val s hs]
    rw [hcongr, sum_range_mul_blocks]
    have hblock : ∀ i ∈ Finset.range m,
        ∑ r ∈ Finset.range hh,
            (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
          (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p i * w (q + i)) +
          ((t : ℝ) / (hh : ℝ)) * (p i * w (q + 1 + i)) := by
      intro i _
      have hsplit_r :
          ∑ r ∈ Finset.range hh,
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
          (∑ r ∈ Finset.range (hh - t),
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh)) +
          (∑ r ∈ Finset.Ico (hh - t) hh,
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh)) := by
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le hh t)]
      rw [hsplit_r]
      have hpart1 :
          ∑ r ∈ Finset.range (hh - t),
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
          (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p i * w (q + i)) := by
        have hconst : ∀ r ∈ Finset.range (hh - t),
            (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
            (p i / (hh : ℝ)) * w (q + i) := by
          intro r hr
          rw [Finset.mem_range] at hr
          have hr_lt : r < hh := by omega
          have hd1 : (i * hh + r) / hh = i := add_mul_div_self_right_lt hhh hr_lt
          have hd2 : (x + (i * hh + r)) / hh = q + i := by
            have heq : x + (i * hh + r) = (q + i) * hh + (t + r) := by rw [hx_eq]; ring
            rw [heq, add_mul_div_self_right_lt hhh (by omega)]
          rw [hd1, hd2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
      have hpart2 :
          ∑ r ∈ Finset.Ico (hh - t) hh,
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
          ((t : ℝ) / (hh : ℝ)) * (p i * w (q + 1 + i)) := by
        have hconst : ∀ r ∈ Finset.Ico (hh - t) hh,
            (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
            (p i / (hh : ℝ)) * w (q + 1 + i) := by
          intro r hr
          rw [Finset.mem_Ico] at hr
          have hd1 : (i * hh + r) / hh = i := add_mul_div_self_right_lt hhh hr.2
          have hd2 : (x + (i * hh + r)) / hh = q + 1 + i := by
            have hmul : (q + 1 + i) * hh = q * hh + hh + i * hh := by ring
            have heq : x + (i * hh + r) = (q + 1 + i) * hh + (t + r - hh) := by
              rw [hx_eq, hmul]; omega
            rw [heq, add_mul_div_self_right_lt hhh (by omega)]
          rw [hd1, hd2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have hcard : hh - (hh - t) = t := by omega
        rw [hcard]
        ring
      rw [hpart1, hpart2]
    rw [Finset.sum_congr rfl hblock, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hc1 := hcover q (by omega)
    have hc2 := hcover (q + 1) (by omega)
    have hα : 0 ≤ (((hh - t : ℕ) : ℝ) / (hh : ℝ)) := by positivity
    have hβ : 0 ≤ ((t : ℝ) / (hh : ℝ)) := by positivity
    have hsum_coeff : (((hh - t : ℕ) : ℝ) / (hh : ℝ)) + ((t : ℝ) / (hh : ℝ)) = 1 := by
      rw [Nat.cast_sub (by omega : t ≤ hh)]
      field_simp
      ring
    have h1 := mul_le_mul_of_nonneg_left hc1 hα
    have h2 := mul_le_mul_of_nonneg_left hc2 hβ
    linarith
  -- Full pointwise covering for all x < N
  have hcover_all : ∀ x, x < N → 1 ≤ ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) := by
    intro x hx
    by_cases hLcase : x < L * H
    · exact hcover_left x hLcase
    · by_cases hRcase : N - L * H ≤ x
      · -- Right boundary: reflect s' = H - 1 - s and reduce to x' = N - 1 - x < L * H
        let x' := N - 1 - x
        have hx' : x' < L * H := by omega
        have hrefl : ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
            ∑ s' ∈ Finset.range H, K (s' : ℤ) * Q (x' + s') := by
          refine Finset.sum_nbij (fun s => H - 1 - s) ?_ ?_ ?_ ?_
          · intro s hs; simp only [Finset.mem_coe, Finset.mem_range] at hs ⊢; omega
          · intro s₁ h₁ s₂ h₂ heq
            dsimp only at heq
            simp only [Finset.mem_coe, Finset.mem_range] at h₁ h₂
            omega
          · intro s' hs'
            simp only [Finset.mem_coe, Finset.mem_range] at hs'
            exact ⟨H - 1 - s', by simp only [Finset.mem_coe, Finset.mem_range]; omega,
              by dsimp only; omega⟩
          · intro s hs
            simp only [Finset.mem_coe, Finset.mem_range] at hs
            rw [hK_symm s hs]
            have hidx : N + H - 2 - (x + s) = x' + (H - 1 - s) := by omega
            rw [← hQ_symm (x + s) (by omega), hidx]
        rw [hrefl]
        exact hcover_left x' hx'
      · -- Interior: Q (x + s) = 1 for all s < H
        have h1 : ∀ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) = K (s : ℤ) := by
          intro s hs
          rw [Finset.mem_range] at hs
          dsimp only [Q]
          rw [if_neg (by omega), if_neg (by omega), mul_one]
        rw [Finset.sum_congr rfl h1, hK_sum]
  -- 7. Sum covering inequality over x ∈ A and interchange sums: A.card ≤ ⟨Q, u⟩
  have hinner_ge : (A.card : ℝ) ≤
      ∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) := by
    have hstep1 : (A.card : ℝ) ≤ ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) := by
      calc (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) :=
            Finset.sum_le_sum fun x hx => hcover_all x (Finset.mem_range.mp (hA hx))
    have hstep2 :
        ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
        ∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) := by
      have hreidx : ∀ x ∈ A,
          ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
          ∑ n ∈ Finset.range (N + H - 1), Q n * K ((n : ℤ) - (x : ℤ)) := by
        intro x hx
        have hxN := Finset.mem_range.mp (hA hx)
        have hsub : (Finset.range H).image (fun s => x + s) ⊆ Finset.range (N + H - 1) := by
          intro n hn
          rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
          rw [Finset.mem_range] at hs ⊢
          omega
        symm
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
          refine Finset.sum_congr rfl fun s _ => ?_
          have hsub_eq : ((x + s : ℕ) : ℤ) - (x : ℤ) = (s : ℤ) := by omega
          rw [hsub_eq, mul_comm]
        · intro n _ hn
          have hzero : K ((n : ℤ) - (x : ℤ)) = 0 := by
            apply hK_supp
            intro ⟨h0, hlt⟩
            apply hn
            exact Finset.mem_image.mpr ⟨n - x, Finset.mem_range.mpr (by omega), by omega⟩
          rw [hzero, mul_zero]
      rw [Finset.sum_congr rfl hreidx, Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
    linarith
  -- 8. Cauchy–Schwarz + Energy Upper Bound
  have hsq_le : (A.card : ℝ) ^ 2 ≤
      (∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ)))) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
    Q (fun n => ∑ x ∈ A, K ((n : ℤ) - (x : ℤ)))
  have henergy := energy_upper_bound hNpos hHpos hA hS hK_nonneg hK_supp hK_sum
  rw [hC0] at henergy
  have hQ_nonneg : 0 ≤ ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomb := (hsq_le.trans hcs).trans (mul_le_mul_of_nonneg_left henergy hQ_nonneg)
  rwa [hQ_norm] at hcomb

/-- Pure real-algebra helper keeping `Finset.sum` out of `nlinarith` context. -/
private lemma kernel_transfer_collapse {g bm γ t k : ℝ}
    (hg_pos : 0 < g) (hbm_pos : 0 ≤ bm) (hγ_pos : 0 < γ) (hg_lt : g < γ)
    (ht1 : 1 ≤ t) (hk_nonneg : 0 ≤ k)
    (hk2_le : k ^ 2 ≤ (t ^ 4 + g * t ^ 3 + bm) * (1 + g / t + 2 * g / t ^ 2))
    (hT3 : (|(g ^ 2 + 2 * g + bm + 2 * g ^ 2 + g * bm + 2 * g * bm)| + 1) / (2 * (γ - g)) + 1 ≤ t) :
    k ≤ t ^ 2 + γ * t := by
  set C : ℝ := g ^ 2 + 2 * g + bm + 2 * g ^ 2 + g * bm + 2 * g * bm
  have ht_pos : 0 < t := by linarith
  have hexpand :
      (t ^ 4 + g * t ^ 3 + bm) * (1 + g / t + 2 * g / t ^ 2) =
      t ^ 4 + 2 * g * t ^ 3 + (g ^ 2 + 2 * g) * t ^ 2 +
        2 * g ^ 2 * t + bm + g * bm / t + 2 * g * bm / t ^ 2 := by
    field_simp
    ring
  have hcollapse :
      t ^ 4 + 2 * g * t ^ 3 + (g ^ 2 + 2 * g) * t ^ 2 +
        2 * g ^ 2 * t + bm + g * bm / t + 2 * g * bm / t ^ 2 ≤
      t ^ 4 + 2 * g * t ^ 3 + C * t ^ 2 := by
    have hgbm_pos : 0 ≤ g * bm := mul_nonneg hg_pos.le hbm_pos
    have h1_le_t2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
    have ht_le_t2 : t ≤ t ^ 2 := by nlinarith
    have hbm_le : bm ≤ bm * t ^ 2 := le_mul_of_one_le_right hbm_pos h1_le_t2
    have h2g2t_le : 2 * g ^ 2 * t ≤ 2 * g ^ 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_left ht_le_t2 (mul_nonneg (by norm_num) (sq_nonneg g))
    have hinv1 : 1 / t ≤ t ^ 2 := by
      rw [div_le_iff₀ ht_pos]
      have h1 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
      have h2 : t ^ 2 * t = t ^ 3 := by ring
      linarith
    have hdiv1 : g * bm / t ≤ g * bm * t ^ 2 := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv1 hgbm_pos
    have hinv2 : 1 / t ^ 2 ≤ t ^ 2 := by
      rw [div_le_iff₀ (pow_pos ht_pos 2)]
      have h1 : 1 ≤ t ^ 4 := one_le_pow₀ ht1
      have h2 : t ^ 2 * t ^ 2 = t ^ 4 := by ring
      linarith
    have hdiv2 : 2 * g * bm / t ^ 2 ≤ 2 * g * bm * t ^ 2 := by
      have h2gbm : 0 ≤ 2 * g * bm := by linarith
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv2 h2gbm
    dsimp only [C]
    linarith
  have h2gg : 0 < 2 * (γ - g) := by linarith
  have hC_lt : C < 2 * (γ - g) * t := by
    have h1 : (|C| + 1) / (2 * (γ - g)) < t := by linarith
    have h2 := (div_lt_iff₀ h2gg).mp h1
    have h3 : C ≤ |C| := le_abs_self C
    linarith
  have hdiff : 0 ≤ (t ^ 2 + γ * t) ^ 2 - (t ^ 4 + 2 * g * t ^ 3 + C * t ^ 2) := by
    have hEq : (t ^ 2 + γ * t) ^ 2 - (t ^ 4 + 2 * g * t ^ 3 + C * t ^ 2) =
        t ^ 2 * (2 * (γ - g) * t - C + γ ^ 2) := by ring
    rw [hEq]
    exact mul_nonneg (sq_nonneg t) (by nlinarith)
  have hfinal_sq : k ^ 2 ≤ (t ^ 2 + γ * t) ^ 2 := by linarith [hk2_le, hexpand, hcollapse]
  have hrhs_nonneg : 0 ≤ t ^ 2 + γ * t :=
    add_nonneg (sq_nonneg t) (mul_nonneg hγ_pos.le ht_pos.le)
  nlinarith

/-- Asymptotic transfer theorem: any feasible symmetric kernel–boundary pair `(p, w)` with
`b > 0` and `a * b < γ^2` (`γ > 0`) implies `h(N) ≤ √N + γ * N^(1/4)` for all large `N`. -/
theorem kernel_transfer_single {m L : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ L)
    {p w : ℕ → ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hp_symm : ∀ i, i < m → p (m - 1 - i) = p i)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    {γ : ℝ} (hγ_pos : 0 < γ)
    (hb_pos : 0 < 1 + 2 * ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ)))
    (hab_lt : ((m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2) *
        (1 + 2 * ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))) < γ ^ 2) :
    ∀ᶠ N : ℕ in atTop, (h N : ℝ) ≤ Real.sqrt (N : ℝ) + γ * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  set a : ℝ := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
  set b : ℝ := 1 + 2 * ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
  -- Cauchy–Schwarz gives a ≥ 1 > 0
  have ha_ge_one : 1 ≤ a := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ => (1 : ℝ)) p
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    rw [hp_sum, one_pow] at hcs
    exact hcs
  have ha_pos : 0 < a := by linarith
  set g : ℝ := Real.sqrt (a * b)
  have hg_pos : 0 < g := Real.sqrt_pos.mpr (mul_pos ha_pos hb_pos)
  have hg_sq : g ^ 2 = a * b := Real.sq_sqrt (mul_pos ha_pos hb_pos).le
  have hg_lt : g < γ := by
    have : g ^ 2 < γ ^ 2 := by rw [hg_sq]; exact hab_lt
    nlinarith
  set r : ℝ := Real.sqrt (a / b)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos ha_pos hb_pos)
  have hbr : b * r = g := by
    dsimp only [r, g]
    have h1 : b * Real.sqrt (a / b) = Real.sqrt (b ^ 2 * (a / b)) := by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb_pos.le]
    rw [h1]
    congr 1
    field_simp
  have ha_div_r : a / r = g := by
    have hne : r ≠ 0 := hr_pos.ne'
    rw [div_eq_iff hne]
    have h1 : g * r = Real.sqrt ((a * b) * (a / b)) := by
      dsimp only [g, r]
      rw [← Real.sqrt_mul (mul_pos ha_pos hb_pos).le]
    rw [h1]
    have h2 : a * b * (a / b) = a ^ 2 := by field_simp
    rw [h2, Real.sqrt_sq ha_pos.le]
  -- Choose threshold T so all asymptotic inequalities hold for t = N^(1/4) ≥ T
  let C : ℝ := g ^ 2 + 2 * g + b * (m : ℝ) + 2 * g ^ 2 +
    g * (b * (m : ℝ)) + 2 * g * (b * (m : ℝ))
  let T : ℝ := max 1 (max (2 * (L : ℝ) * r + 2 * (L : ℝ) * (m : ℝ) + 1)
      ((|C| + 1) / (2 * (γ - g)) + 1))
  let N0 : ℕ := Nat.ceil (T ^ 4) + 1
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  have hT_ge_one : 1 ≤ T := le_max_left _ _
  have hN_ge_T4 : T ^ 4 ≤ (N : ℝ) := by
    have h1 : T ^ 4 ≤ (Nat.ceil (T ^ 4) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (T ^ 4) : ℝ) ≤ (N : ℝ) := by
      have : Nat.ceil (T ^ 4) ≤ N := by omega
      exact_mod_cast this
    linarith
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < T ^ 4 := by positivity
    linarith
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    norm_num
  have ht_ge_T : T ≤ t := by
    by_contra hlt
    push Not at hlt
    have ht_nonneg : 0 ≤ t := Real.rpow_nonneg hN_pos.le _
    have : t ^ 4 < T ^ 4 := by
      have hsq : t ^ 2 < T ^ 2 := by nlinarith
      nlinarith
    linarith
  have ht1 : 1 ≤ t := hT_ge_one.trans ht_ge_T
  have ht_pos : 0 < t := by linarith
  -- Choose hh = ⌊r * t^3 / m⌋ + 1, H = m * hh
  let hh : ℕ := Nat.floor (r * t ^ 3 / (m : ℝ)) + 1
  have hhh : 1 ≤ hh := Nat.succ_pos _
  let H : ℕ := m * hh
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hH_gt : r * t ^ 3 < (H : ℝ) := by
    dsimp only [H, hh]
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfl := Nat.lt_floor_add_one (r * t ^ 3 / (m : ℝ))
    have := mul_lt_mul_of_pos_left hfl hm_pos
    field_simp at this ⊢
    linarith
  have hH_le : (H : ℝ) ≤ r * t ^ 3 + (m : ℝ) := by
    dsimp only [H, hh]
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfl : (Nat.floor (r * t ^ 3 / (m : ℝ)) : ℝ) ≤ r * t ^ 3 / (m : ℝ) :=
      Nat.floor_le (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hm_pos.le
    have hsimp : (m : ℝ) * (r * t ^ 3 / (m : ℝ)) = r * t ^ 3 := by field_simp
    linarith
  have hN_large : 2 * L * H ≤ N := by
    have hT2 : 2 * (L : ℝ) * r + 2 * (L : ℝ) * (m : ℝ) + 1 ≤ t :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans ht_ge_T
    have hreal : ((2 * L * H : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      have h1 : (2 * (L : ℝ)) * (H : ℝ) ≤ 2 * (L : ℝ) * (r * t ^ 3 + (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hH_le (by positivity)
      have h2 : 2 * (L : ℝ) * (r * t ^ 3 + (m : ℝ)) ≤ t ^ 4 := by
        have ht3_ge1 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
        have hLm_le : 2 * (L : ℝ) * (m : ℝ) ≤ 2 * (L : ℝ) * (m : ℝ) * t ^ 3 :=
          le_mul_of_one_le_right (by positivity) ht3_ge1
        have ht3_pos : 0 ≤ t ^ 3 := pow_nonneg ht_pos.le 3
        have hmul_t3 : (2 * (L : ℝ) * r + 2 * (L : ℝ) * (m : ℝ)) * t ^ 3 ≤ t * t ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) ht3_pos
        linarith
      linarith [ht4]
    exact_mod_cast hreal
  -- Apply block_kernel_master_ineq to a maximum Sidon set A ⊆ range N
  obtain ⟨A, hAsub, hAS, hAcard⟩ := exists_max_sidon_range N
  have hmaster : (h N : ℝ) ^ 2 ≤
      ((N : ℝ) + b * (H : ℝ) - 1) * (1 + ((h N : ℝ) - 1) * (a / (H : ℝ))) := by
    have hraw := block_kernel_master_ineq hm hL hhh hN_large
      hp_nonneg hp_sum hp_symm hw_tail hcover hAsub hAS
    dsimp only at hraw
    rw [hAcard] at hraw
    exact hraw
  set k : ℝ := (h N : ℝ)
  have hk_nonneg : 0 ≤ k := Nat.cast_nonneg _
  -- Lindström gives k ≤ t^2 + t + 1
  have hk_lind : k ≤ t ^ 2 + t + 1 := by
    have hl := lindstrom_theorem N
    have hkeq : k = (h N : ℝ) := rfl
    have hteq : t = (N : ℝ) ^ (4⁻¹ : ℝ) := rfl
    linarith [ht2, hl]
  -- Bound both factors of hmaster
  have hfac1 : (N : ℝ) + b * (H : ℝ) - 1 ≤ t ^ 4 + g * t ^ 3 + b * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hH_le hb_pos.le
    have : b * (H : ℝ) ≤ g * t ^ 3 + b * (m : ℝ) := by
      calc b * (H : ℝ) ≤ b * (r * t ^ 3 + (m : ℝ)) := this
        _ = (b * r) * t ^ 3 + b * (m : ℝ) := by ring
        _ = g * t ^ 3 + b * (m : ℝ) := by rw [hbr]
    linarith [ht4]
  have hfac2 : 1 + (k - 1) * (a / (H : ℝ)) ≤ 1 + g / t + 2 * g / t ^ 2 := by
    have hH_pos' : 0 < (H : ℝ) := by linarith [mul_pos hr_pos (pow_pos ht_pos 3)]
    have hinv : 1 / (H : ℝ) ≤ 1 / (r * t ^ 3) :=
      one_div_le_one_div_of_le (mul_pos hr_pos (pow_pos ht_pos 3)) hH_gt.le
    have haH : a / (H : ℝ) ≤ g / t ^ 3 := by
      have : a / (H : ℝ) ≤ a / (r * t ^ 3) := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv ha_pos.le
      calc a / (H : ℝ) ≤ a / (r * t ^ 3) := this
        _ = (a / r) / t ^ 3 := by rw [div_mul_eq_div_div]
        _ = g / t ^ 3 := by rw [ha_div_r]
    have hkm1 : k - 1 ≤ t ^ 2 + 2 * t := by linarith
    have hkm1_mul : (k - 1) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) := by
      have hpos_aH : 0 ≤ a / (H : ℝ) := div_nonneg ha_pos.le hH_pos'.le
      have h1 : (k - 1) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (a / (H : ℝ)) :=
        mul_le_mul_of_nonneg_right hkm1 hpos_aH
      have h2 : (t ^ 2 + 2 * t) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) :=
        mul_le_mul_of_nonneg_left haH (by nlinarith)
      exact h1.trans h2
    have hsimp : (t ^ 2 + 2 * t) * (g / t ^ 3) = g / t + 2 * g / t ^ 2 := by
      field_simp
    linarith
  have hfac1_nonneg : 0 ≤ (N : ℝ) + b * (H : ℝ) - 1 := by
    have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by rw [← ht4]; exact one_le_pow₀ ht1
    have hbH : 0 ≤ b * (H : ℝ) := mul_nonneg hb_pos.le hH0
    linarith
  have hfac2_nonneg : 0 ≤ 1 + g / t + 2 * g / t ^ 2 := by
    have h1 : 0 ≤ g / t := div_nonneg hg_pos.le ht_pos.le
    have h2 : 0 ≤ 2 * g / t ^ 2 := div_nonneg (by linarith) (sq_nonneg t)
    linarith
  have hk2_le : k ^ 2 ≤ (t ^ 4 + g * t ^ 3 + b * (m : ℝ)) * (1 + g / t + 2 * g / t ^ 2) := by
    have h1 : ((N : ℝ) + b * (H : ℝ) - 1) * (1 + (k - 1) * (a / (H : ℝ))) ≤
        ((N : ℝ) + b * (H : ℝ) - 1) * (1 + g / t + 2 * g / t ^ 2) :=
      mul_le_mul_of_nonneg_left hfac2 hfac1_nonneg
    have h2 : ((N : ℝ) + b * (H : ℝ) - 1) * (1 + g / t + 2 * g / t ^ 2) ≤
        (t ^ 4 + g * t ^ 3 + b * (m : ℝ)) * (1 + g / t + 2 * g / t ^ 2) :=
      mul_le_mul_of_nonneg_right hfac1 hfac2_nonneg
    exact hmaster.trans (h1.trans h2)
  have hk_le : k ≤ t ^ 2 + γ * t := by
    have hT3 : (|C| + 1) / (2 * (γ - g)) + 1 ≤ t :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans ht_ge_T
    exact kernel_transfer_collapse hg_pos (mul_nonneg hb_pos.le hm_pos.le)
      hγ_pos hg_lt ht1 hk_nonneg hk2_le hT3
  linarith [ht2]

/-! ### Section 5: Exact 16-Bin Rational Certificate ($\sqrt{ab} < 0.949$) & Literature Milestones -/

/-- Exact numerator list of the 16-bin symmetric smoothing kernel (denominator `10000`). -/
def certPNum (i : ℕ) : ℕ :=
  match i with
  | 0 => 107 | 1 => 194 | 2 => 290 | 3 => 404
  | 4 => 537 | 5 => 707 | 6 => 932 | 7 => 1829
  | 8 => 1829 | 9 => 932 | 10 => 707 | 11 => 537
  | 12 => 404 | 13 => 290 | 14 => 194 | 15 => 107
  | _ => 0

/-- Exact numerator list of the 32-bin boundary weight vector (denominator `100000`),
taking constant value `100000` (i.e. `1`) on the tail `j ≥ 32`. -/
def certWNum (j : ℕ) : ℕ :=
  match j with
  | 0 => 7342 | 1 => 13312 | 2 => 21112 | 3 => 29932
  | 4 => 41502 | 5 => 55632 | 6 => 75392 | 7 => 141822
  | 8 => 149472 | 9 => 104822 | 10 => 98352 | 11 => 95732
  | 12 => 94582 | 13 => 95332 | 14 => 96392 | 15 => 98772
  | 16 => 103172 | 17 => 101712 | 18 => 100862 | 19 => 100122
  | 20 => 99892 | 21 => 99582 | 22 => 99742 | 23 => 99662
  | 24 => 100022 | 25 => 100112 | 26 => 100102 | 27 => 100072
  | 28 => 100012 | 29 => 100002 | 30 => 99952 | 31 => 100042
  | _ => 100000

noncomputable def certP (i : ℕ) : ℝ := (certPNum i : ℝ) / 10000
noncomputable def certW (j : ℕ) : ℝ := (certWNum j : ℝ) / 100000

-- Pure Lean kernel checks via `decide` (zero extra axioms!)
lemma certPNum_sum : ∑ i ∈ Finset.range 16, certPNum i = 10000 := by decide

lemma certPNum_symm : ∀ i ∈ Finset.range 16, certPNum (15 - i) = certPNum i := by decide

lemma cert_covering_nat :
    ∀ q ∈ Finset.range 33, 1000000000 ≤ ∑ i ∈ Finset.range 16, certPNum i * certWNum (q + i) := by
  decide

lemma certPNum_sq_sum : ∑ i ∈ Finset.range 16, (certPNum i) ^ 2 = 10596968 := by decide

lemma certWNum_sq_sum : ∑ j ∈ Finset.range 32, (certWNum j) ^ 2 = 282462607528 := by decide

/-- Formally verified Sidon upper bound improving upon Balogh–Füredi–Roy (0.998),
O'Bryant (0.99703), Carter–Hunter–O'Bryant (0.98183), and Tao et al. 2025 (0.97633):
`h(N) ≤ √N + 0.949 * N^(1/4)` for all sufficiently large `N`. -/
theorem sidon_sub_0949 :
    ∀ᶠ N : ℕ in atTop, (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (0.949 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  have hp_nonneg : ∀ i, i < 16 → 0 ≤ certP i := fun i _ => by
    dsimp only [certP]; positivity
  have hp_sum : ∑ i ∈ Finset.range 16, certP i = 1 := by
    dsimp only [certP]
    rw [← Finset.sum_div, ← Nat.cast_sum, certPNum_sum]
    norm_num
  have hp_symm : ∀ i, i < 16 → certP (16 - 1 - i) = certP i := by
    intro i hi
    dsimp only [certP]
    have := certPNum_symm i (Finset.mem_range.mpr hi)
    rw [show 16 - 1 - i = 15 - i from rfl, this]
  have hw_tail : ∀ j, 2 * 16 ≤ j → certW j = 1 := by
    intro j hj
    dsimp only [certW, certWNum]
    have hmatch :
        (match j with
        | 0 => 7342 | 1 => 13312 | 2 => 21112 | 3 => 29932
        | 4 => 41502 | 5 => 55632 | 6 => 75392 | 7 => 141822
        | 8 => 149472 | 9 => 104822 | 10 => 98352 | 11 => 95732
        | 12 => 94582 | 13 => 95332 | 14 => 96392 | 15 => 98772
        | 16 => 103172 | 17 => 101712 | 18 => 100862 | 19 => 100122
        | 20 => 99892 | 21 => 99582 | 22 => 99742 | 23 => 99662
        | 24 => 100022 | 25 => 100112 | 26 => 100102 | 27 => 100072
        | 28 => 100012 | 29 => 100002 | 30 => 99952 | 31 => 100042
        | _ => 100000) = 100000 := by
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> first | omega | rfl
    rw [hmatch]
    norm_num
  have hcover : ∀ q, q ≤ 2 * 16 → 1 ≤ ∑ i ∈ Finset.range 16, certP i * certW (q + i) := by
    intro q hq
    have hnat := cert_covering_nat q (Finset.mem_range.mpr (by omega))
    have hreal : (1000000000 : ℝ) ≤
        ((∑ i ∈ Finset.range 16, certPNum i * certWNum (q + i) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hsum_eq :
        ∑ i ∈ Finset.range 16, certP i * certW (q + i) =
        ((∑ i ∈ Finset.range 16, certPNum i * certWNum (q + i) : ℕ) : ℝ) / 1000000000 := by
      dsimp only [certP, certW]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum_eq]
    linarith
  have ha_eq : ((16 : ℕ) : ℝ) * ∑ i ∈ Finset.range 16, (certP i) ^ 2 =
      (16 : ℝ) * 10596968 / 10000 ^ 2 := by
    have hsq : ∑ i ∈ Finset.range 16, (certP i) ^ 2 = (10596968 : ℝ) / 10000 ^ 2 := by
      dsimp only [certP]
      have : ∀ i ∈ Finset.range 16, ((certPNum i : ℝ) / 10000) ^ 2 =
          ((certPNum i ^ 2 : ℕ) : ℝ) / 10000 ^ 2 := by
        intro i _; push_cast; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Nat.cast_sum, certPNum_sq_sum]
      norm_num
    rw [hsq]
    norm_num
  have hb_eq :
      1 + 2 * ((∑ j ∈ Finset.range (2 * 16), (certW j) ^ 2) / ((16 : ℕ) : ℝ) - ((2 : ℕ) : ℝ)) =
      1 + 2 * (((282462607528 : ℝ) / 100000 ^ 2) / 16 - 2) := by
    have hsq : ∑ j ∈ Finset.range (2 * 16), (certW j) ^ 2 = (282462607528 : ℝ) / 100000 ^ 2 := by
      dsimp only [certW]
      have : ∀ j ∈ Finset.range 32, ((certWNum j : ℝ) / 100000) ^ 2 =
          ((certWNum j ^ 2 : ℕ) : ℝ) / 100000 ^ 2 := by
        intro j _; push_cast; ring
      rw [show 2 * 16 = 32 from rfl, Finset.sum_congr rfl this, ← Finset.sum_div,
        ← Nat.cast_sum, certWNum_sq_sum]
      norm_num
    rw [hsq]
    norm_num
  apply kernel_transfer_single (m := 16) (L := 2) (by norm_num) (by norm_num)
    hp_nonneg hp_sum hp_symm hw_tail hcover (γ := (0.949 : ℝ)) (by norm_num)
  · rw [hb_eq]; norm_num
  · rw [ha_eq, hb_eq]; norm_num

/-- Balogh–Füredi–Roy (2023): $h(N) \le \sqrt{N} + 0.998 N^{1/4}$ for all large $N$. -/
theorem balogh_furedi_roy_theorem : BaloghFurediRoyStatement := by
  filter_upwards [sidon_sub_0949] with N hN
  have hnonneg : 0 ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

/-- O'Bryant (2022): $h(N) \le \sqrt{N} + 0.99703 N^{1/4}$ for all large $N$. -/
theorem obryant_theorem : OBryantStatement := by
  filter_upwards [sidon_sub_0949] with N hN
  have hnonneg : 0 ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

/-- Carter–Hunter–O'Bryant (2025): $h(N) \le \sqrt{N} + 0.98183 N^{1/4} + O(1)$. -/
theorem carter_hunter_obryant_theorem : CarterHunterOBryantStatement := by
  refine ⟨0, ?_⟩
  filter_upwards [sidon_sub_0949] with N hN
  have hnonneg : 0 ≤ (N : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

/-! ### Section 6: Bose's Lower Bound Construction (1942) via $\mathbb{F}_{p^2}^\times$ -/

/-- Bose's Construction (1942): for every prime $p$, there is a Sidon set of size $p$
contained in $\{1, \dots, p^2 - 1\}$, hence $p \le h(p^2 - 1)$. -/
theorem bose_lower_bound_theorem : BoseLowerBoundStatement := by
  classical
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p 2
  have hcardK : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hcardF : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hp2 : 2 ≤ p := hp.two_le
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  -- 1. There exists θ ∈ K not in the image of ZMod p
  have hex_theta : ∃ θ : K, θ ∉ Set.range (algebraMap (ZMod p) K) := by
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective (algebraMap (ZMod p) K) := hall
    have hle : Nat.card K ≤ Nat.card (ZMod p) := Nat.card_le_card_of_surjective _ hsurj
    rw [hcardK, hcardF] at hle
    nlinarith
  obtain ⟨θ, hθ⟩ := hex_theta
  -- 2. Every θ + x (x : ZMod p) is nonzero in K
  have hne0 : ∀ x : ZMod p, θ + algebraMap (ZMod p) K x ≠ 0 := by
    intro x hzero
    apply hθ
    refine ⟨-x, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hzero).symm
  -- 3. Kˣ is a finite cyclic group of order p^2 - 1
  have hfinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hcardU : Nat.card Kˣ = p ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hpow_surj : ∀ u : Kˣ, ∃ a : ℕ, 1 ≤ a ∧ a ≤ p ^ 2 - 1 ∧ g ^ a = u := by
    intro u
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hord_pos : 0 < orderOf g := by rw [hord]; omega
    -- Reduce k modulo orderOf g into [0, orderOf g)
    let r : ℕ := (k % (orderOf g : ℤ)).toNat
    have hr_lt : r < orderOf g := by
      have h1 : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg k (by omega)
      have h2 : k % (orderOf g : ℤ) < (orderOf g : ℤ) := Int.emod_lt_of_pos k (by omega)
      omega
    have hgr : g ^ r = u := by
      have h1 : g ^ (k % (orderOf g : ℤ)) = g ^ k := zpow_mod_orderOf g k
      have h2 : (r : ℤ) = k % (orderOf g : ℤ) := by
        have : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg k (by omega)
        omega
      rw [← zpow_natCast, h2, h1, hk]
    by_cases hr0 : r = 0
    · refine ⟨p ^ 2 - 1, by omega, le_refl _, ?_⟩
      rw [← hord, pow_orderOf_eq_one, ← pow_zero g, ← hr0, hgr]
    · refine ⟨r, by omega, by omega, hgr⟩
  -- 4. Choose discrete log a(x) ∈ {1, ..., p^2 - 1} for each x : ZMod p
  have hex_a : ∀ x : ZMod p,
      ∃ a : ℕ, 1 ≤ a ∧ a ≤ p ^ 2 - 1 ∧ (g : K) ^ a = θ + algebraMap (ZMod p) K x := by
    intro x
    obtain ⟨a, ha1, ha2, hga⟩ := hpow_surj (Units.mk0 (θ + algebraMap (ZMod p) K x) (hne0 x))
    refine ⟨a, ha1, ha2, ?_⟩
    have := congrArg (Units.val : Kˣ → K) hga
    simpa [Units.val_pow_eq_pow_val] using this
  choose a ha1 ha2 hga using hex_a
  -- 5. Image A = Finset.univ.image a has size p, lies in Icc 1 (p^2 - 1), and is Sidon
  let A : Finset ℕ := Finset.univ.image a
  have ha_inj : Function.Injective a := by
    intro x y hxy
    have heq : θ + algebraMap (ZMod p) K x = θ + algebraMap (ZMod p) K y := by
      rw [← hga x, ← hga y, hxy]
    have hmap : algebraMap (ZMod p) K x = algebraMap (ZMod p) K y := add_left_cancel heq
    exact (algebraMap (ZMod p) K).injective hmap
  have hA_card : A.card = p := by
    rw [Finset.card_image_of_injective _ ha_inj, Finset.card_univ, ZMod.card]
  have hA_sub : A ⊆ Finset.Icc 1 (p ^ 2 - 1) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
    exact Finset.mem_Icc.mpr ⟨ha1 x, ha2 x⟩
  have hA_sidon : IsSidon (A : Set ℕ) := by
    intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂ hsum
    simp only [A, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      at ha₁ hb₁ ha₂ hb₂
    rcases ha₁ with ⟨x₁, rfl⟩
    rcases hb₁ with ⟨y₁, rfl⟩
    rcases ha₂ with ⟨x₂, rfl⟩
    rcases hb₂ with ⟨y₂, rfl⟩
    have hprod :
        (θ + algebraMap (ZMod p) K x₁) * (θ + algebraMap (ZMod p) K y₁) =
        (θ + algebraMap (ZMod p) K x₂) * (θ + algebraMap (ZMod p) K y₂) := by
      rw [← hga x₁, ← hga y₁, ← hga x₂, ← hga y₂, ← pow_add, ← pow_add, hsum]
    -- θ^2 cancels! Leaves algebraMap (x₁ + y₁ - x₂ - y₂) * θ = algebraMap (x₂*y₂ - x₁*y₁)
    have hlin : algebraMap (ZMod p) K (x₁ + y₁ - (x₂ + y₂)) * θ =
        algebraMap (ZMod p) K (x₂ * y₂ - x₁ * y₁) := by
      rw [map_sub, map_add, map_add, map_sub, map_mul, map_mul]
      linear_combination hprod
    have hsum_eq : x₁ + y₁ = x₂ + y₂ := by
      by_contra hne
      have hdiff_ne : x₁ + y₁ - (x₂ + y₂) ≠ 0 := sub_ne_zero.mpr hne
      apply hθ
      refine ⟨(x₂ * y₂ - x₁ * y₁) / (x₁ + y₁ - (x₂ + y₂)), ?_⟩
      rw [map_div₀]
      have hmap_ne : algebraMap (ZMod p) K (x₁ + y₁ - (x₂ + y₂)) ≠ 0 :=
        (map_ne_zero (algebraMap (ZMod p) K)).mpr hdiff_ne
      rw [div_eq_iff hmap_ne, mul_comm θ, hlin]
    have hmul_eq : x₁ * y₁ = x₂ * y₂ := by
      have h0 : algebraMap (ZMod p) K (x₂ * y₂ - x₁ * y₁) = 0 := by
        rw [← hlin, hsum_eq, sub_self, map_zero, zero_mul]
      have : x₂ * y₂ - x₁ * y₁ = 0 := (map_eq_zero (algebraMap (ZMod p) K)).mp h0
      exact (sub_eq_zero.mp this).symm
    have hquad : (x₁ - x₂) * (x₁ - y₂) = 0 := by
      linear_combination x₁ * hsum_eq - hmul_eq
    rcases mul_eq_zero.mp hquad with hx | hx
    · have hx12 : x₁ = x₂ := sub_eq_zero.mp hx
      have hy12 : y₁ = y₂ := by subst hx12; exact add_left_cancel hsum_eq
      left; rw [hx12, hy12]; exact ⟨rfl, rfl⟩
    · have hx12 : x₁ = y₂ := sub_eq_zero.mp hx
      have hy12 : y₁ = x₂ := by subst hx12; rw [add_comm x₂ x₁] at hsum_eq; exact add_left_cancel hsum_eq
      right; rw [hx12, hy12]; exact ⟨rfl, rfl⟩
  calc p = A.card := hA_card.symm
    _ ≤ h (p ^ 2 - 1) := card_le_h hA_sub hA_sidon

/-! ### Section 7: Asymmetric One-Sided Kernel Transfer & Lean-Verified Sub-0.94295 Bound -/

/-- Asymmetric one-sided discrete smoothing master inequality (no kernel symmetry required!):
using a left-boundary weight `w` (`w j = 1` for `j ≥ L * m`) and constant `1` on the right,
any Sidon set `A ⊆ range N` with `L * (m * hh) ≤ N` satisfies
`|A|^2 ≤ (N + b * H - 1) * (1 + a * (|A| - 1) / H)` with
`a = m * ∑ p_i^2` and `b = 1 + (∑ w_j^2) / m - L`. -/
lemma asymmetric_block_kernel_master_ineq {m L hh N : ℕ}
    (hm : 1 ≤ m) (hL : 1 ≤ L) (hhh : 1 ≤ hh)
    (hN_large : L * (m * hh) ≤ N)
    {p w : ℕ → ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    {A : Finset ℕ} (hA : A ⊆ Finset.range N) (hS : IsSidon (A : Set ℕ)) :
    let H := m * hh
    let a := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
    let b := 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
    (A.card : ℝ) ^ 2 ≤
      ((N : ℝ) + b * (H : ℝ) - 1) * (1 + ((A.card : ℝ) - 1) * (a / (H : ℝ))) := by
  intro H a b
  have hHpos : 1 ≤ H := Nat.mul_pos hm hhh
  have hLH_pos : 1 ≤ L * H := Nat.mul_pos hL hHpos
  have hN_ge_LH : L * H ≤ N := hN_large
  have hNpos : 1 ≤ N := by omega
  have hhh_pos : (0 : ℝ) < (hh : ℝ) := Nat.cast_pos.mpr hhh
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hH_pos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hHpos
  let K : ℤ → ℝ := fun z => if 0 ≤ z ∧ z < (H : ℤ) then p (z.toNat / hh) / (hh : ℝ) else 0
  have hK_nat : ∀ s, s < H → K (s : ℤ) = p (s / hh) / (hh : ℝ) := by
    intro s hs; dsimp only [K]; rw [if_pos ⟨by omega, by omega⟩]; simp
  have hK_nonneg : ∀ z : ℤ, 0 ≤ K z := by
    intro z; dsimp only [K]
    split_ifs with hz
    · apply div_nonneg
      · apply hp_nonneg
        have : z.toNat < m * hh := by omega
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      · exact hhh_pos.le
    · exact le_refl 0
  have hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < (H : ℤ)) → K z = 0 := by
    intro z hz; dsimp only [K]; rw [if_neg hz]
  have hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1 := by
    have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) =
        ∑ s ∈ Finset.range (m * hh), p (s / hh) / (hh : ℝ) :=
      Finset.sum_congr rfl fun s hs => hK_nat s (Finset.mem_range.mp hs)
    rw [hcongr, sum_range_mul_blocks]
    have hblock : ∀ i ∈ Finset.range m,
        ∑ r ∈ Finset.range hh, p ((i * hh + r) / hh) / (hh : ℝ) = p i := by
      intro i _
      have hdiv : ∀ r ∈ Finset.range hh, p ((i * hh + r) / hh) / (hh : ℝ) = p i / (hh : ℝ) := by
        intro r hr; rw [add_mul_div_self_right_lt hhh (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hblock, hp_sum]
  have hC0 : autocorr H K 0 = a / (H : ℝ) := by
    unfold autocorr
    have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + 0) =
        ∑ s ∈ Finset.range (m * hh), (p (s / hh) / (hh : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [add_zero, hK_nat s (Finset.mem_range.mp hs), sq]
    rw [hcongr, sum_range_mul_blocks]
    have hblock : ∀ i ∈ Finset.range m,
        ∑ r ∈ Finset.range hh, (p ((i * hh + r) / hh) / (hh : ℝ)) ^ 2 = (p i) ^ 2 / (hh : ℝ) := by
      intro i _
      have hdiv : ∀ r ∈ Finset.range hh,
          (p ((i * hh + r) / hh) / (hh : ℝ)) ^ 2 = (p i) ^ 2 / (hh : ℝ) ^ 2 := by
        intro r hr; rw [add_mul_div_self_right_lt hhh (Finset.mem_range.mp hr), div_pow]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [Finset.sum_congr rfl hblock, ← Finset.sum_div]
    dsimp only [a, H]; rw [Nat.cast_mul]; field_simp
  -- One-sided boundary weight Q: w on [0, LH), constant 1 on [LH, N + H - 1)
  let Q : ℕ → ℝ := fun n => if n < L * H then w (n / hh) else 1
  have hQ_eq_w : ∀ n, Q n = w (n / hh) := by
    intro n; dsimp only [Q]
    split_ifs with hlt
    · rfl
    · symm; apply hw_tail
      have hLHm : L * m * hh ≤ n := by
        have : L * H = L * m * hh := by dsimp only [H]; ring
        omega
      exact (Nat.le_div_iff_mul_le hhh).mpr hLHm
  -- Norm of Q on J = range (N + H - 1) equals N + b * H - 1
  have hQ_norm : ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 = (N : ℝ) + b * (H : ℝ) - 1 := by
    have hLH_le : L * H ≤ N + H - 1 := by omega
    rw [← Finset.sum_range_add_sum_Ico _ hLH_le]
    have hleft : ∑ n ∈ Finset.range (L * H), (Q n) ^ 2 =
        (hh : ℝ) * ∑ j ∈ Finset.range (L * m), (w j) ^ 2 := by
      have hcongr : ∑ n ∈ Finset.range (L * H), (Q n) ^ 2 =
          ∑ n ∈ Finset.range ((L * m) * hh), (w (n / hh)) ^ 2 := by
        have hLHm : L * H = (L * m) * hh := by dsimp only [H]; ring
        rw [hLHm]
        refine Finset.sum_congr rfl fun n _ => by rw [hQ_eq_w]
      rw [hcongr, sum_range_mul_blocks, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hdiv : ∀ r ∈ Finset.range hh, (w ((j * hh + r) / hh)) ^ 2 = (w j) ^ 2 := by
        intro r hr; rw [add_mul_div_self_right_lt hhh (Finset.mem_range.mp hr)]
      rw [Finset.sum_congr rfl hdiv, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hright : ∑ n ∈ Finset.Ico (L * H) (N + H - 1), (Q n) ^ 2 =
        ((N + H - 1 - L * H : ℕ) : ℝ) := by
      have h1 : ∀ n ∈ Finset.Ico (L * H) (N + H - 1), (Q n) ^ 2 = 1 := by
        intro n hn; rw [Finset.mem_Ico] at hn; dsimp only [Q]; rw [if_neg (by omega), one_pow]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    rw [hleft, hright]
    have hcast_r : ((N + H - 1 - L * H : ℕ) : ℝ) =
        (N : ℝ) + (H : ℝ) - 1 - (L : ℝ) * (H : ℝ) := by
      have hge : L * H + 1 ≤ N + H := by omega
      have : N + H - 1 - L * H = N + H - (L * H + 1) := by omega
      rw [this, Nat.cast_sub hge]; push_cast; ring
    rw [hcast_r]; dsimp only [b, H]; rw [Nat.cast_mul]; field_simp; ring
  -- Pointwise covering for ALL x < N (only 2 cases: x < LH or x ≥ LH!)
  have hcover_all : ∀ x, x < N → 1 ≤ ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) := by
    intro x _
    by_cases hx : x < L * H
    · let q := x / hh
      let t := x % hh
      have hq_lt : q < L * m := by
        have : x < (L * m) * hh := by dsimp only [H] at hx; linarith
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      have ht_lt : t < hh := Nat.mod_lt x hhh
      have hx_eq : x = q * hh + t := (Nat.div_add_mod' x hh).symm
      have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
          ∑ s ∈ Finset.range (m * hh), (p (s / hh) / (hh : ℝ)) * w ((x + s) / hh) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hK_nat s (Finset.mem_range.mp hs), hQ_eq_w]
      rw [hcongr, sum_range_mul_blocks]
      have hblock : ∀ i ∈ Finset.range m,
          ∑ r ∈ Finset.range hh,
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
            (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p i * w (q + i)) +
            ((t : ℝ) / (hh : ℝ)) * (p i * w (q + 1 + i)) := by
        intro i _
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le hh t)]
        have hpart1 :
            ∑ r ∈ Finset.range (hh - t),
                (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
            (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p i * w (q + i)) := by
          have hconst : ∀ r ∈ Finset.range (hh - t),
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
              (p i / (hh : ℝ)) * w (q + i) := by
            intro r hr; rw [Finset.mem_range] at hr
            have hd1 : (i * hh + r) / hh = i := add_mul_div_self_right_lt hhh (by omega)
            have hd2 : (x + (i * hh + r)) / hh = q + i := by
              have heq : x + (i * hh + r) = (q + i) * hh + (t + r) := by rw [hx_eq]; ring
              rw [heq, add_mul_div_self_right_lt hhh (by omega)]
            rw [hd1, hd2]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        have hpart2 :
            ∑ r ∈ Finset.Ico (hh - t) hh,
                (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
            ((t : ℝ) / (hh : ℝ)) * (p i * w (q + 1 + i)) := by
          have hconst : ∀ r ∈ Finset.Ico (hh - t) hh,
              (p ((i * hh + r) / hh) / (hh : ℝ)) * w ((x + (i * hh + r)) / hh) =
              (p i / (hh : ℝ)) * w (q + 1 + i) := by
            intro r hr; rw [Finset.mem_Ico] at hr
            have hd1 : (i * hh + r) / hh = i := add_mul_div_self_right_lt hhh hr.2
            have hd2 : (x + (i * hh + r)) / hh = q + 1 + i := by
              have hmul : (q + 1 + i) * hh = q * hh + hh + i * hh := by ring
              have heq : x + (i * hh + r) = (q + 1 + i) * hh + (t + r - hh) := by
                rw [hx_eq, hmul]; omega
              rw [heq, add_mul_div_self_right_lt hhh (by omega)]
            rw [hd1, hd2]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          rw [show hh - (hh - t) = t by omega]; ring
        rw [hpart1, hpart2]
      rw [Finset.sum_congr rfl hblock, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hc1 := hcover q (by omega)
      have hc2 := hcover (q + 1) (by omega)
      have hα : 0 ≤ (((hh - t : ℕ) : ℝ) / (hh : ℝ)) := by positivity
      have hβ : 0 ≤ ((t : ℝ) / (hh : ℝ)) := by positivity
      have hsum_coeff : (((hh - t : ℕ) : ℝ) / (hh : ℝ)) + ((t : ℝ) / (hh : ℝ)) = 1 := by
        rw [Nat.cast_sub (by omega : t ≤ hh)]; field_simp; ring
      have h1 := mul_le_mul_of_nonneg_left hc1 hα
      have h2 := mul_le_mul_of_nonneg_left hc2 hβ
      linarith
    · have h1 : ∀ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) = K (s : ℤ) := by
        intro s _; dsimp only [Q]; rw [if_neg (by omega), mul_one]
      rw [Finset.sum_congr rfl h1, hK_sum]
  -- Sum over A, Cauchy–Schwarz, and energy_upper_bound
  have hinner_ge : (A.card : ℝ) ≤
      ∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) := by
    have hstep1 : (A.card : ℝ) ≤ ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) := by
      calc (A.card : ℝ) = ∑ _x ∈ A, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) :=
            Finset.sum_le_sum fun x hx => hcover_all x (Finset.mem_range.mp (hA hx))
    have hstep2 :
        ∑ x ∈ A, ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
        ∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ))) := by
      have hreidx : ∀ x ∈ A,
          ∑ s ∈ Finset.range H, K (s : ℤ) * Q (x + s) =
          ∑ n ∈ Finset.range (N + H - 1), Q n * K ((n : ℤ) - (x : ℤ)) := by
        intro x hx
        have hxN := Finset.mem_range.mp (hA hx)
        have hsub : (Finset.range H).image (fun s => x + s) ⊆ Finset.range (N + H - 1) := by
          intro n hn; rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
          rw [Finset.mem_range] at hs ⊢; omega
        symm
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [show ((x + s : ℕ) : ℤ) - (x : ℤ) = (s : ℤ) by omega, mul_comm]
        · intro n _ hn
          have hzero : K ((n : ℤ) - (x : ℤ)) = 0 := by
            apply hK_supp; intro ⟨h0, hlt⟩; apply hn
            exact Finset.mem_image.mpr ⟨n - x, Finset.mem_range.mpr (by omega), by omega⟩
          rw [hzero, mul_zero]
      rw [Finset.sum_congr rfl hreidx, Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
    linarith
  have hsq_le : (A.card : ℝ) ^ 2 ≤
      (∑ n ∈ Finset.range (N + H - 1), Q n * (∑ x ∈ A, K ((n : ℤ) - (x : ℤ)))) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
    Q (fun n => ∑ x ∈ A, K ((n : ℤ) - (x : ℤ)))
  have henergy := energy_upper_bound hNpos hHpos hA hS hK_nonneg hK_supp hK_sum
  rw [hC0] at henergy
  have hQ_nonneg : 0 ≤ ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomb := (hsq_le.trans hcs).trans (mul_le_mul_of_nonneg_left henergy hQ_nonneg)
  rwa [hQ_norm] at hcomb

/-- Asymptotic transfer theorem for asymmetric one-sided kernels. -/
theorem asymmetric_kernel_transfer {m L : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ L)
    {p w : ℕ → ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    {γ : ℝ} (hγ_pos : 0 < γ)
    (hb_pos : 0 < 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ)))
    (hab_lt : ((m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2) *
        (1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))) < γ ^ 2) :
    ∀ᶠ N : ℕ in atTop, (h N : ℝ) ≤ Real.sqrt (N : ℝ) + γ * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  set a : ℝ := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
  set b : ℝ := 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
  have ha_ge_one : 1 ≤ a := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ => (1 : ℝ)) p
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    rw [hp_sum, one_pow] at hcs; exact hcs
  have ha_pos : 0 < a := by linarith
  set g : ℝ := Real.sqrt (a * b)
  have hg_pos : 0 < g := Real.sqrt_pos.mpr (mul_pos ha_pos hb_pos)
  have hg_sq : g ^ 2 = a * b := Real.sq_sqrt (mul_pos ha_pos hb_pos).le
  have hg_lt : g < γ := by
    have : g ^ 2 < γ ^ 2 := by rw [hg_sq]; exact hab_lt
    nlinarith
  set r : ℝ := Real.sqrt (a / b)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos ha_pos hb_pos)
  have hbr : b * r = g := by
    dsimp only [r, g]
    rw [show b * Real.sqrt (a / b) = Real.sqrt (b ^ 2 * (a / b)) from by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb_pos.le]]
    congr 1; field_simp
  have ha_div_r : a / r = g := by
    rw [div_eq_iff hr_pos.ne']
    rw [show g * r = Real.sqrt ((a * b) * (a / b)) from by
      dsimp only [g, r]; rw [← Real.sqrt_mul (mul_pos ha_pos hb_pos).le]]
    rw [show a * b * (a / b) = a ^ 2 from by field_simp, Real.sqrt_sq ha_pos.le]
  let C : ℝ := g ^ 2 + 2 * g + b * (m : ℝ) + 2 * g ^ 2 +
    g * (b * (m : ℝ)) + 2 * g * (b * (m : ℝ))
  let T : ℝ := max 1 (max ((L : ℝ) * r + (L : ℝ) * (m : ℝ) + 1)
      ((|C| + 1) / (2 * (γ - g)) + 1))
  let N0 : ℕ := Nat.ceil (T ^ 4) + 1
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  have hT_ge_one : 1 ≤ T := le_max_left _ _
  have hN_ge_T4 : T ^ 4 ≤ (N : ℝ) := by
    have h1 : T ^ 4 ≤ (Nat.ceil (T ^ 4) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (T ^ 4) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show Nat.ceil (T ^ 4) ≤ N by omega)
    linarith
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < T ^ 4 := by positivity
    linarith
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]; dsimp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  have ht_ge_T : T ≤ t := by
    by_contra hlt; push Not at hlt
    have ht_nonneg : 0 ≤ t := Real.rpow_nonneg hN_pos.le _
    have : t ^ 4 < T ^ 4 := by
      have hsq : t ^ 2 < T ^ 2 := by nlinarith
      nlinarith
    linarith
  have ht1 : 1 ≤ t := hT_ge_one.trans ht_ge_T
  have ht_pos : 0 < t := by linarith
  let hh : ℕ := Nat.floor (r * t ^ 3 / (m : ℝ)) + 1
  have hhh : 1 ≤ hh := Nat.succ_pos _
  let H : ℕ := m * hh
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hH_gt : r * t ^ 3 < (H : ℝ) := by
    dsimp only [H, hh]; rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfl := Nat.lt_floor_add_one (r * t ^ 3 / (m : ℝ))
    have := mul_lt_mul_of_pos_left hfl hm_pos
    field_simp at this ⊢; linarith
  have hH_le : (H : ℝ) ≤ r * t ^ 3 + (m : ℝ) := by
    dsimp only [H, hh]; rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfl : (Nat.floor (r * t ^ 3 / (m : ℝ)) : ℝ) ≤ r * t ^ 3 / (m : ℝ) :=
      Nat.floor_le (by positivity)
    have := mul_le_mul_of_nonneg_left hfl hm_pos.le
    have hsimp : (m : ℝ) * (r * t ^ 3 / (m : ℝ)) = r * t ^ 3 := by field_simp
    linarith
  have hN_large : L * H ≤ N := by
    have hT2 : (L : ℝ) * r + (L : ℝ) * (m : ℝ) + 1 ≤ t :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans ht_ge_T
    have hreal : ((L * H : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      have h1 : (L : ℝ) * (H : ℝ) ≤ (L : ℝ) * (r * t ^ 3 + (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hH_le (by positivity)
      have h2 : (L : ℝ) * (r * t ^ 3 + (m : ℝ)) ≤ t ^ 4 := by
        have ht3_ge1 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
        have hLm_le : (L : ℝ) * (m : ℝ) ≤ (L : ℝ) * (m : ℝ) * t ^ 3 :=
          le_mul_of_one_le_right (by positivity) ht3_ge1
        have hmul_t3 : ((L : ℝ) * r + (L : ℝ) * (m : ℝ)) * t ^ 3 ≤ t * t ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg ht_pos.le 3)
        linarith
      linarith [ht4]
    exact_mod_cast hreal
  obtain ⟨A, hAsub, hAS, hAcard⟩ := exists_max_sidon_range N
  have hmaster : (h N : ℝ) ^ 2 ≤
      ((N : ℝ) + b * (H : ℝ) - 1) * (1 + ((h N : ℝ) - 1) * (a / (H : ℝ))) := by
    have hraw := asymmetric_block_kernel_master_ineq hm hL hhh hN_large
      hp_nonneg hp_sum hw_tail hcover hAsub hAS
    dsimp only at hraw; rw [hAcard] at hraw; exact hraw
  set k : ℝ := (h N : ℝ)
  have hk_nonneg : 0 ≤ k := Nat.cast_nonneg _
  have hk_lind : k ≤ t ^ 2 + t + 1 := by
    have hl := lindstrom_theorem N
    have hkeq : k = (h N : ℝ) := rfl
    have hteq : t = (N : ℝ) ^ (4⁻¹ : ℝ) := rfl
    linarith [ht2, hl]
  have hfac1 : (N : ℝ) + b * (H : ℝ) - 1 ≤ t ^ 4 + g * t ^ 3 + b * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hH_le hb_pos.le
    have : b * (H : ℝ) ≤ g * t ^ 3 + b * (m : ℝ) := by
      calc b * (H : ℝ) ≤ b * (r * t ^ 3 + (m : ℝ)) := this
        _ = (b * r) * t ^ 3 + b * (m : ℝ) := by ring
        _ = g * t ^ 3 + b * (m : ℝ) := by rw [hbr]
    linarith [ht4]
  have hfac2 : 1 + (k - 1) * (a / (H : ℝ)) ≤ 1 + g / t + 2 * g / t ^ 2 := by
    have hH_pos' : 0 < (H : ℝ) := by linarith [mul_pos hr_pos (pow_pos ht_pos 3)]
    have hinv : 1 / (H : ℝ) ≤ 1 / (r * t ^ 3) :=
      one_div_le_one_div_of_le (mul_pos hr_pos (pow_pos ht_pos 3)) hH_gt.le
    have haH : a / (H : ℝ) ≤ g / t ^ 3 := by
      have : a / (H : ℝ) ≤ a / (r * t ^ 3) := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv ha_pos.le
      calc a / (H : ℝ) ≤ a / (r * t ^ 3) := this
        _ = (a / r) / t ^ 3 := by rw [div_mul_eq_div_div]
        _ = g / t ^ 3 := by rw [ha_div_r]
    have hkm1 : k - 1 ≤ t ^ 2 + 2 * t := by linarith
    have hkm1_mul : (k - 1) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) := by
      have hpos_aH : 0 ≤ a / (H : ℝ) := div_nonneg ha_pos.le hH_pos'.le
      have h1 : (k - 1) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (a / (H : ℝ)) :=
        mul_le_mul_of_nonneg_right hkm1 hpos_aH
      have h2 : (t ^ 2 + 2 * t) * (a / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) :=
        mul_le_mul_of_nonneg_left haH (by nlinarith)
      exact h1.trans h2
    have hsimp : (t ^ 2 + 2 * t) * (g / t ^ 3) = g / t + 2 * g / t ^ 2 := by field_simp
    linarith
  have hfac1_nonneg : 0 ≤ (N : ℝ) + b * (H : ℝ) - 1 := by
    have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by rw [← ht4]; exact one_le_pow₀ ht1
    have hbH : 0 ≤ b * (H : ℝ) := mul_nonneg hb_pos.le hH0
    linarith
  have hfac2_nonneg : 0 ≤ 1 + g / t + 2 * g / t ^ 2 := by
    have h1 : 0 ≤ g / t := div_nonneg hg_pos.le ht_pos.le
    have h2 : 0 ≤ 2 * g / t ^ 2 := div_nonneg (by linarith) (sq_nonneg t)
    linarith
  have hk2_le : k ^ 2 ≤ (t ^ 4 + g * t ^ 3 + b * (m : ℝ)) * (1 + g / t + 2 * g / t ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hfac2 hfac1_nonneg
    have h2 := mul_le_mul_of_nonneg_right hfac1 hfac2_nonneg
    exact hmaster.trans (h1.trans h2)
  have hk_le : k ≤ t ^ 2 + γ * t := by
    have hT3 : (|C| + 1) / (2 * (γ - g)) + 1 ≤ t :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans ht_ge_T
    exact kernel_transfer_collapse hg_pos (mul_nonneg hb_pos.le hm_pos.le)
      hγ_pos hg_lt ht1 hk_nonneg hk2_le hT3
  linarith [ht2]

/-- Exact 192-bin left-boundary weight lookup (2-level O(1) dispatch for fast kernel `decide`),
corresponding to linear kernel `p_i = (2*i + 1) / 2304` (`m = 48, L = 4`, denominator `1000000`). -/
def asymWBlock (b r : ℕ) : ℕ :=
  match b with
  | 0 => match r with
    | 0 => 10521 | 1 => 31801 | 2 => 53521 | 3 => 75701
    | 4 => 98341 | 5 => 121471 | 6 => 145081 | 7 => 169201
    | 8 => 193821 | 9 => 218961 | 10 => 244641 | 11 => 270851
    | 12 => 297621 | 13 => 324961 | 14 => 352871 | _ => 381371
  | 1 => match r with
    | 0 => 410471 | 1 => 440181 | 2 => 470511 | 3 => 501491
    | 4 => 533111 | 5 => 565391 | 6 => 598351 | 7 => 632001
    | 8 => 666361 | 9 => 701431 | 10 => 737231 | 11 => 773791
    | 12 => 811101 | 13 => 849211 | 14 => 888101 | _ => 927821
  | 2 => match r with
    | 0 => 968371 | 1 => 1009771 | 2 => 1052041 | 3 => 1095211
    | 4 => 1139281 | 5 => 1184281 | 6 => 1230241 | 7 => 1277161
    | 8 => 1325081 | 9 => 1374021 | 10 => 1423991 | 11 => 1475011
    | 12 => 1527131 | 13 => 1580341 | 14 => 1634691 | _ => 1690191
  | 3 => match r with
    | 0 => 725871 | 1 => 740711 | 2 => 755401 | 3 => 769941
    | 4 => 784321 | 5 => 798521 | 6 => 812531 | 7 => 826321
    | 8 => 839901 | 9 => 853231 | 10 => 866321 | 11 => 879131
    | 12 => 891651 | 13 => 903871 | 14 => 915771 | _ => 927321
  | 4 => match r with
    | 0 => 938501 | 1 => 949311 | 2 => 959711 | 3 => 969681
    | 4 => 979201 | 5 => 988251 | 6 => 996811 | 7 => 1004841
    | 8 => 1012331 | 9 => 1019251 | 10 => 1025561 | 11 => 1031251
    | 12 => 1036271 | 13 => 1040611 | 14 => 1044231 | _ => 1047101
  | 5 => match r with
    | 0 => 1049191 | 1 => 1050451 | 2 => 1050861 | 3 => 1050381
    | 4 => 1048981 | 5 => 1046601 | 6 => 1043221 | 7 => 1038791
    | 8 => 1033261 | 9 => 1026611 | 10 => 1018771 | 11 => 1009701
    | 12 => 999351 | 13 => 987681 | 14 => 974631 | _ => 960151
  | 6 => match r with
    | 0 => 954931 | 1 => 959601 | 2 => 964051 | 3 => 968291
    | 4 => 972321 | 5 => 976131 | 6 => 979721 | 7 => 983091
    | 8 => 986251 | 9 => 989191 | 10 => 991921 | 11 => 994431
    | 12 => 996721 | 13 => 998801 | 14 => 1000681 | _ => 1002341
  | 7 => match r with
    | 0 => 1003811 | 1 => 1005071 | 2 => 1006131 | 3 => 1007001
    | 4 => 1007691 | 5 => 1008191 | 6 => 1008521 | 7 => 1008681
    | 8 => 1008691 | 9 => 1008541 | 10 => 1008251 | 11 => 1007821
    | 12 => 1007281 | 13 => 1006621 | 14 => 1005871 | _ => 1005031
  | 8 => match r with
    | 0 => 1004121 | 1 => 1003161 | 2 => 1002161 | 3 => 1001141
    | 4 => 1000121 | 5 => 999111 | 6 => 998151 | 7 => 997251
    | 8 => 996431 | 9 => 995721 | 10 => 995161 | 11 => 994751
    | 12 => 994551 | 13 => 994571 | 14 => 994851 | _ => 995431
  | 9 => match r with
    | 0 => 996231 | 1 => 997051 | 2 => 997791 | 3 => 998461
    | 4 => 999051 | 5 => 999571 | 6 => 1000031 | 7 => 1000421
    | 8 => 1000751 | 9 => 1001021 | 10 => 1001241 | 11 => 1001411
    | 12 => 1001541 | 13 => 1001621 | 14 => 1001661 | _ => 1001661
  | 10 => match r with
    | 0 => 1001631 | 1 => 1001571 | 2 => 1001491 | 3 => 1001381
    | 4 => 1001251 | 5 => 1001111 | 6 => 1000961 | 7 => 1000801
    | 8 => 1000631 | 9 => 1000461 | 10 => 1000301 | 11 => 1000141
    | 12 => 999981 | 13 => 999831 | 14 => 999701 | _ => 999581
  | _ => match r with
    | 0 => 999471 | 1 => 999381 | 2 => 999311 | 3 => 999271
    | 4 => 999241 | 5 => 999231 | 6 => 999241 | 7 => 999271
    | 8 => 999331 | 9 => 999391 | 10 => 999481 | 11 => 999571
    | 12 => 999681 | 13 => 999781 | 14 => 999891 | _ => 1005481

def asymPNum (i : ℕ) : ℕ := 2 * i + 1
def asymWNum (j : ℕ) : ℕ := if j < 192 then asymWBlock (j / 16) (j % 16) else 1000000

noncomputable def asymP (i : ℕ) : ℝ := (asymPNum i : ℝ) / 2304
noncomputable def asymW (j : ℕ) : ℝ := (asymWNum j : ℝ) / 1000000

-- Fast 2D blocked `ℕ` sum & range-checker so pure kernel `decide` stays well within stack depth
def sumRangeAux : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, acc => acc
  | n + 1, f, acc => sumRangeAux n f (acc + f n)

lemma sumRangeAux_eq (n : ℕ) (f : ℕ → ℕ) (acc : ℕ) :
    sumRangeAux n f acc = acc + ∑ i ∈ Finset.range n, f i := by
  induction n generalizing acc with
  | zero => simp [sumRangeAux]
  | succ n ih =>
    rw [sumRangeAux, ih, Finset.sum_range_succ]
    omega

def sumBlocks (blocks blockSize : ℕ) (f : ℕ → ℕ) : ℕ :=
  sumRangeAux blocks (fun b => sumRangeAux blockSize (fun r => f (b * blockSize + r)) 0) 0

lemma sumBlocks_eq (B S : ℕ) (f : ℕ → ℕ) :
    sumBlocks B S f = ∑ j ∈ Finset.range (B * S), f j := by
  unfold sumBlocks
  rw [sumRangeAux_eq, zero_add]
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ, ih, sumRangeAux_eq, zero_add]
    rw [show (B + 1) * S = B * S + S by ring, Finset.sum_range_add]

def checkRange : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => if p n then checkRange n p else false

lemma checkRange_true {n : ℕ} {p : ℕ → Bool} (h : checkRange n p = true) :
    ∀ q, q < n → p q = true := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    unfold checkRange at h
    split_ifs at h with hpn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | rfl
    · exact ih h q hlt
    · exact hpn

def checkBlocks (blocks blockSize : ℕ) (p : ℕ → Bool) : Bool :=
  checkRange blocks (fun b => checkRange blockSize (fun r => p (b * blockSize + r)))

lemma checkBlocks_true {B S : ℕ} (hS : 0 < S) {p : ℕ → Bool}
    (h : checkBlocks B S p = true) :
    ∀ q, q < B * S → p q = true := by
  intro q hq
  have hdiv : q / S < B := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
  have hmod : q % S < S := Nat.mod_lt q hS
  have hb := checkRange_true h (q / S) hdiv
  have hr := checkRange_true hb (q % S) hmod
  rwa [Nat.div_add_mod' q S] at hr

-- Pure Lean kernel checks via `decide` (zero extra axioms!)
lemma asymPNum_sum : ∑ i ∈ Finset.range 48, asymPNum i = 2304 := by
  have h := sumBlocks_eq 4 12 asymPNum
  have hdec : sumBlocks 4 12 asymPNum = 2304 := by decide
  rw [show (48 : ℕ) = 4 * 12 from rfl, ← h, hdec]

lemma asymPNum_sq_sum : ∑ i ∈ Finset.range 48, (asymPNum i) ^ 2 = 147440 := by
  have h := sumBlocks_eq 4 12 (fun i => (asymPNum i) ^ 2)
  have hdec : sumBlocks 4 12 (fun i => (asymPNum i) ^ 2) = 147440 := by decide
  rw [show (48 : ℕ) = 4 * 12 from rfl, ← h, hdec]

lemma asymWNum_sq_sum : ∑ j ∈ Finset.range 192, (asymWNum j) ^ 2 = 176012388616832 := by
  have h := sumBlocks_eq 12 16 (fun j => (asymWNum j) ^ 2)
  have hdec : sumBlocks 12 16 (fun j => (asymWNum j) ^ 2) = 176012388616832 := by decide
  rw [show (192 : ℕ) = 12 * 16 from rfl, ← h, hdec]

def asymCoverCheck (q : ℕ) : Bool :=
  decide (2304000000 ≤ sumBlocks 4 12 (fun i => asymPNum i * asymWNum (q + i)))

lemma asymCover_chunk0 :
    checkBlocks 3 16 (fun r => asymCoverCheck r) = true := by decide

lemma asymCover_chunk1 :
    checkBlocks 3 16 (fun r => asymCoverCheck (48 + r)) = true := by decide

lemma asymCover_chunk2 :
    checkBlocks 3 16 (fun r => asymCoverCheck (96 + r)) = true := by decide

lemma asymCover_chunk3 :
    checkBlocks 3 16 (fun r => asymCoverCheck (144 + r)) = true := by decide

lemma asymCover_last : asymCoverCheck 192 = true := by decide

lemma asym_covering_nat :
    ∀ q ∈ Finset.range 193,
      2304000000 ≤ ∑ i ∈ Finset.range 48, asymPNum i * asymWNum (q + i) := by
  intro q hq
  rw [Finset.mem_range] at hq
  have htrue : asymCoverCheck q = true := by
    by_cases h0 : q < 48
    · exact checkBlocks_true (by norm_num) asymCover_chunk0 q h0
    · by_cases h1 : q < 96
      · have := checkBlocks_true (by norm_num) asymCover_chunk1 (q - 48) (by omega)
        rwa [show 48 + (q - 48) = q by omega] at this
      · by_cases h2 : q < 144
        · have := checkBlocks_true (by norm_num) asymCover_chunk2 (q - 96) (by omega)
          rwa [show 96 + (q - 96) = q by omega] at this
        · by_cases h3 : q < 192
          · have := checkBlocks_true (by norm_num) asymCover_chunk3 (q - 144) (by omega)
            rwa [show 144 + (q - 144) = q by omega] at this
          · have hq192 : q = 192 := by omega
            subst hq192
            exact asymCover_last
  have hle := of_decide_eq_true htrue
  rw [sumBlocks_eq] at hle
  exact hle

/-- Formally verified Sidon upper bound strictly sharper than Hou–Zhao (Sep 2026, `0.9435`)
and Carter–O'Bryant–Tao (Oct 2026, `0.94304`):
`h(N) ≤ √N + 0.94295 * N^(1/4)` for all sufficiently large `N`, certified via the asymmetric
linear kernel `p_i = (2i+1)/48^2` (`m = 48, L = 4`, `√(ab) = 0.94294036... < 0.94295`). -/
theorem sidon_sub_094295 :
    ∀ᶠ N : ℕ in atTop,
      (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (0.94295 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  have hp_nonneg : ∀ i, i < 48 → 0 ≤ asymP i := fun i _ => by
    dsimp only [asymP]; positivity
  have hp_sum : ∑ i ∈ Finset.range 48, asymP i = 1 := by
    dsimp only [asymP]
    rw [← Finset.sum_div, ← Nat.cast_sum, asymPNum_sum]
    norm_num
  have hw_tail : ∀ j, 4 * 48 ≤ j → asymW j = 1 := by
    intro j hj
    dsimp only [asymW, asymWNum]
    rw [if_neg (by omega)]
    norm_num
  have hcover : ∀ q, q ≤ 4 * 48 → 1 ≤ ∑ i ∈ Finset.range 48, asymP i * asymW (q + i) := by
    intro q hq
    have hnat := asym_covering_nat q (Finset.mem_range.mpr (by omega))
    have hreal : (2304000000 : ℝ) ≤
        ((∑ i ∈ Finset.range 48, asymPNum i * asymWNum (q + i) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hsum_eq :
        ∑ i ∈ Finset.range 48, asymP i * asymW (q + i) =
        ((∑ i ∈ Finset.range 48, asymPNum i * asymWNum (q + i) : ℕ) : ℝ) / 2304000000 := by
      dsimp only [asymP, asymW]
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_eq]
    linarith
  have ha_eq : ((48 : ℕ) : ℝ) * ∑ i ∈ Finset.range 48, (asymP i) ^ 2 =
      (48 : ℝ) * 147440 / 2304 ^ 2 := by
    have hsq : ∑ i ∈ Finset.range 48, (asymP i) ^ 2 = (147440 : ℝ) / 2304 ^ 2 := by
      dsimp only [asymP]
      have : ∀ i ∈ Finset.range 48, ((asymPNum i : ℝ) / 2304) ^ 2 =
          ((asymPNum i ^ 2 : ℕ) : ℝ) / 2304 ^ 2 := by
        intro i _; push_cast; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Nat.cast_sum, asymPNum_sq_sum]
      norm_num
    rw [hsq]; norm_num
  have hb_eq :
      1 + ((∑ j ∈ Finset.range (4 * 48), (asymW j) ^ 2) / ((48 : ℕ) : ℝ) - ((4 : ℕ) : ℝ)) =
      1 + (((176012388616832 : ℝ) / 1000000 ^ 2) / 48 - 4) := by
    have hsq : ∑ j ∈ Finset.range (4 * 48), (asymW j) ^ 2 =
        (176012388616832 : ℝ) / 1000000 ^ 2 := by
      dsimp only [asymW]
      have : ∀ j ∈ Finset.range 192, ((asymWNum j : ℝ) / 1000000) ^ 2 =
          ((asymWNum j ^ 2 : ℕ) : ℝ) / 1000000 ^ 2 := by
        intro j _; push_cast; ring
      rw [show 4 * 48 = 192 from rfl, Finset.sum_congr rfl this, ← Finset.sum_div,
        ← Nat.cast_sum, asymWNum_sq_sum]
      norm_num
    rw [hsq]; norm_num
  apply asymmetric_kernel_transfer (m := 48) (L := 4) (by norm_num) (by norm_num)
    hp_nonneg hp_sum hw_tail hcover (γ := (0.94295 : ℝ)) (by norm_num)
  · rw [hb_eq]; norm_num
  · rw [ha_eq, hb_eq]; norm_num

end Erdos030
