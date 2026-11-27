import Problems.Erdos030.Statement
import Problems.Erdos030.Lasserre2
import Problems.Erdos030.PeriodicDFT
import Problems.Erdos030.SmoothBumpBarrier
import Problems.Erdos030.Track2EquidistAndM3AP
import Problems.Erdos030.Track3BoseVariance
import Problems.Erdos030.Universal3APBound
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic

/-!
# Erdős Problem #30 — Formally Verified Frontier Bounds & Structural Barrier Theorems

This file proves the following theorems for `Erdos030.h` and its convex/fractional
relaxation hierarchy without modifying `Statement.lean`, using only standard Lean 4
axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. `lindstrom_theorem` (`LindstromStatement`):
   $\forall N \in \mathbb{N},\; h(N) \le \sqrt{N} + N^{1/4} + 1$.
2. `erdos_turan_theorem` (`ErdosTuranStatement`):
   $\exists C,\; \forall^\infty N,\; h(N) \le \sqrt{N} + C N^{1/4}$.
3. `kernel_transfer_single` & `sidon_sub_0949`:
   General discrete symmetric smoothing transfer theorem and
   $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.949 N^{1/4}$ ($\sqrt{ab} = 0.9486568\ldots$).
4. `balogh_furedi_roy_theorem`, `obryant_theorem`, `carter_hunter_obryant_theorem`:
   Formal resolutions of the `formal-conjectures` Erdős #30 upper-bound variants.
5. `bose_lower_bound_theorem` (`BoseLowerBoundStatement`):
   $\forall p$ prime, $p \le h(p^2 - 1)$ via Bose's finite-field construction in $\mathbb{F}_{p^2}^\times$.
6. `asymmetric_kernel_transfer` & `sidon_sub_094295`:
   Asymmetric one-sided kernel–boundary transfer and frontier bound
   $\forall^\infty N,\; h(N) \le \sqrt{N} + 0.94295 N^{1/4}$ ($m=48, L=4$, $\sqrt{ab} = 0.94294036\ldots$).
7. `shor_rlt_sdp1_lift` & `shor_rlt_sdp1_lift_3ap_4sidon_cuts`:
   Exact Degree-1 Lasserre / Shor + RLT + BQP + 3-AP + 4-Sidon cutting-plane SDP lift
   from fractional Sidon vectors $\mu \in [0,1]^N$.
8. `fractional_energy_upper_bound`, `sdp1_energy_upper_bound`,
   `fractional_sidon_sub_094295_theta`, `sdp1_sub_094295`,
   `strict_separation_h6_lt_fractional_sdp1`:
   Sharp $\theta$-integrality envelope $\sqrt{N} + 0.94295\sqrt{\theta}\,N^{1/4}$,
   `SDP_1` upper bound $\sqrt{N} + 0.94295 N^{1/4}$, and strict separation $h(6) < M(6) \le \mathrm{SDP}_1(6)$.
9. `bose_modular_difference_set`, `bose_periodic_fourier_flatness`,
   `bose_3ap_free_superset_bound`:
   Exact modular difference-set structure, periodic Fourier flatness
   $|\widehat{\mathbf{1}_{S_p}}(\xi)|^2 \in \{1, p\}$, and 3-AP-free superset bound
   $|T| \le (p^2 - 1)/\sqrt{p}$ for Bose's Sidon set.
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

/-! ### Section 8: Fractional Sidon Relaxation & Full Degree-1 Lasserre (Shor + RLT + BQP) SDP -/

/-- A weight function `μ : ℕ → ℝ` on `{0, ..., N - 1}` is *fractional Sidon* if it lies in `[0, 1]`
and satisfies all `N - 1` exact pointwise pairwise autocorrelation constraints
`∑_{x < N - d} μ(x) * μ(x + d) ≤ 1` (with zero smoothing). -/
def IsFractionalSidon (N : ℕ) (μ : ℕ → ℝ) : Prop :=
  (∀ x, x < N → 0 ≤ μ x ∧ μ x ≤ 1) ∧
  (∀ d, 1 ≤ d → d < N → ∑ x ∈ Finset.range (N - d), μ x * μ (x + d) ≤ 1)

/-- Feasibility predicate for the full Degree-1 Lasserre / Shor + RLT + Nonnegativity
Semidefinite Program `SDP_1(N)` for Sidon sets in `{0, ..., N - 1}`:
1. Symmetry `X i j = X j i`
2. Positive semidefiniteness of the lifted moment matrix `[1, x^T; x, X] ≽ 0`
3. Diagonal `{0, 1}`-integrality `X i i = x i`
4. Nonnegativity and all McCormick / RLT bounds `0 ≤ X i j ≤ min(x i, x j)` and `x i + x j - 1 ≤ X i j`
5. All `N - 1` exact pointwise pairwise Sidon constraints `∑_{i < N - d} X i (i + d) ≤ 1`. -/
def IsSDP1Feasible (N : ℕ) (x : ℕ → ℝ) (X : ℕ → ℕ → ℝ) : Prop :=
  (∀ i, i < N → ∀ j, j < N → X i j = X j i) ∧
  (∀ (c₀ : ℝ) (v : ℕ → ℝ),
    0 ≤ c₀ ^ 2 + 2 * c₀ * (∑ i ∈ Finset.range N, v i * x i) +
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j) ∧
  (∀ i, i < N → X i i = x i) ∧
  (∀ i, i < N → ∀ j, j < N →
    0 ≤ X i j ∧ X i j ≤ x i ∧ X i j ≤ x j ∧ x i + x j - 1 ≤ X i j) ∧
  (∀ d, 1 ≤ d → d < N → ∑ i ∈ Finset.range (N - d), X i (i + d) ≤ 1)

/-- Degree-1 Lasserre / Shor + RLT + BQP Barrier Lift:
Every feasible fractional Sidon measure `μ` lifts via `X i j = if i = j then μ i else μ i * μ j`
to a strictly feasible point of `SDP_1(N)` with the exact same objective `∑ μ_i`, and ALSO
satisfies all Boolean Quadric Polytope (BQP) triangle inequalities `X i j + X i k - X j k ≤ μ i`. -/
theorem shor_rlt_sdp1_lift {N : ℕ} {μ : ℕ → ℝ} (hμ : IsFractionalSidon N μ) :
    let X : ℕ → ℕ → ℝ := fun i j => if i = j then μ i else μ i * μ j
    IsSDP1Feasible N μ X ∧
    (∀ i, i < N → ∀ j, j < N → ∀ k, k < N → i ≠ j → i ≠ k → j ≠ k →
      X i j + X i k - X j k ≤ μ i) := by
  classical
  intro X
  rcases hμ with ⟨hμ_box, hμ_ac⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- Symmetry
    intro i _ j _
    dsimp only [X]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), mul_comm]
  · -- PSD of `[1, μ^T; μ, X]`
    intro c₀ v
    have hsplit :
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j =
        (∑ i ∈ Finset.range N, v i * μ i) ^ 2 +
        ∑ i ∈ Finset.range N, (v i) ^ 2 * (μ i * (1 - μ i)) := by
      have hsq : (∑ i ∈ Finset.range N, v i * μ i) ^ 2 =
          ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * (μ i * μ j) * v j := by
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hsq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hinner :
          ∑ j ∈ Finset.range N, v i * X i j * v j =
          (∑ j ∈ Finset.range N, v i * (μ i * μ j) * v j) +
            (v i) ^ 2 * (μ i * (1 - μ i)) := by
        have hdiff :
            ∑ j ∈ Finset.range N, (v i * X i j * v j - v i * (μ i * μ j) * v j) =
            (v i) ^ 2 * (μ i * (1 - μ i)) := by
          rw [Finset.sum_eq_single i]
          · dsimp only [X]; rw [if_pos rfl]; ring
          · intro j _ hji; dsimp only [X]; rw [if_neg (Ne.symm hji)]; ring
          · intro hi'; exact False.elim (hi' hi)
        rw [Finset.sum_sub_distrib] at hdiff
        linarith
      exact hinner
    rw [hsplit]
    have hdiag_nonneg : 0 ≤ ∑ i ∈ Finset.range N, (v i) ^ 2 * (μ i * (1 - μ i)) := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hb := hμ_box i (Finset.mem_range.mp hi)
      have h1 : 0 ≤ μ i * (1 - μ i) := mul_nonneg hb.1 (by linarith)
      exact mul_nonneg (sq_nonneg _) h1
    have hsq_nonneg : 0 ≤ (c₀ + ∑ i ∈ Finset.range N, v i * μ i) ^ 2 := sq_nonneg _
    nlinarith
  · -- Diagonal integrality
    intro i _; dsimp only [X]; rw [if_pos rfl]
  · -- Nonnegativity & McCormick / RLT inequalities
    intro i hi j hj
    have hbi := hμ_box i hi
    have hbj := hμ_box j hj
    dsimp only [X]
    by_cases h : i = j
    · subst h; rw [if_pos rfl]
      refine ⟨hbi.1, le_refl _, le_refl _, by linarith⟩
    · rw [if_neg h]
      refine ⟨mul_nonneg hbi.1 hbj.1, ?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · nlinarith
  · -- Exact pointwise Sidon constraints
    intro d hd1 hdN
    have hcongr : ∑ i ∈ Finset.range (N - d), X i (i + d) =
        ∑ i ∈ Finset.range (N - d), μ i * μ (i + d) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [X]
      rw [if_neg (by omega)]
    rw [hcongr]
    exact hμ_ac d hd1 hdN
  · -- Boolean Quadric Polytope (BQP) triangle inequalities
    intro i hi j hj k hk hij hik hjk
    have hbi := hμ_box i hi
    have hbj := hμ_box j hj
    have hbk := hμ_box k hk
    dsimp only [X]
    rw [if_neg hij, if_neg hik, if_neg hjk]
    have h1 : 0 ≤ μ i * (1 - μ j) * (1 - μ k) :=
      mul_nonneg (mul_nonneg hbi.1 (by linarith)) (by linarith)
    have h2 : 0 ≤ (1 - μ i) * μ j * μ k :=
      mul_nonneg (mul_nonneg (by linarith) hbj.1) hbk.1
    linarith

/-- Moreover, whenever `μ i ≤ 1 / √3` (which our Cauchy High-Pass Sidon Hybrid with `α = 1/2`
satisfies for all large `N`), the lifted matrix `X` ALSO satisfies all `Θ(N^2)` exact 3-AP-free
linear cuts `X a b + X b c + X a c ≤ 1` and all `Θ(N^3)` exact 4-tuple Sidon linear cuts
`X a b + X a c + X a e + X b c + X b e + X c e ≤ 3`. -/
theorem shor_rlt_sdp1_lift_3ap_4sidon_cuts {N : ℕ} {μ : ℕ → ℝ}
    (hμ : IsFractionalSidon N μ)
    (hμ_cap : ∀ i, i < N → μ i ≤ 1 / Real.sqrt 3) :
    let X : ℕ → ℕ → ℝ := fun i j => if i = j then μ i else μ i * μ j
    IsSDP1Feasible N μ X ∧
    (∀ a b c, a < b → b < c → c < N → a + c = 2 * b →
      X a b + X b c + X a c ≤ 1) ∧
    (∀ a b c e, a < b → b < c → c < e → e < N → a + e = b + c →
      X a b + X a c + X a e + X b c + X b e + X c e ≤ 3) := by
  intro X
  have hlift := (shor_rlt_sdp1_lift hμ).1
  have hprod : ∀ i j, i < N → j < N → i ≠ j → X i j ≤ (1 : ℝ) / 3 := by
    intro i j hi hj hij
    dsimp only [X]
    rw [if_neg hij]
    have h0i := (hμ.1 i hi).1
    have h0j := (hμ.1 j hj).1
    have hci := hμ_cap i hi
    have hcj := hμ_cap j hj
    have hmul : μ i * μ j ≤ (1 / Real.sqrt 3) * (1 / Real.sqrt 3) :=
      mul_le_mul hci hcj h0j (by positivity)
    have hsq3 : (1 / Real.sqrt 3) * (1 / Real.sqrt 3) = (1 : ℝ) / 3 := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt (by norm_num)]
    linarith
  refine ⟨hlift, ?_, ?_⟩
  · intro a b c hab hbc hc _
    have h1 := hprod a b (by omega) (by omega) (by omega)
    have h2 := hprod b c (by omega) (by omega) (by omega)
    have h3 := hprod a c (by omega) (by omega) (by omega)
    linarith
  · intro a b c e hab hbc hce he _
    have h1 := hprod a b (by omega) (by omega) (by omega)
    have h2 := hprod a c (by omega) (by omega) (by omega)
    have h3 := hprod a e (by omega) (by omega) (by omega)
    have h4 := hprod b c (by omega) (by omega) (by omega)
    have h5 := hprod b e (by omega) (by omega) (by omega)
    have h6 := hprod c e (by omega) (by omega) (by omega)
    linarith

/-- Symmetry of discrete kernel autocorrelation: `autocorr H K (-d) = autocorr H K d`. -/
lemma autocorr_neg {H : ℕ} {K : ℤ → ℝ}
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0) (d : ℤ) :
    autocorr H K (-d) = autocorr H K d := by
  unfold autocorr
  have hcast : ∀ s : ℕ, K (s : ℤ) * K ((s : ℤ) + -d) = K ((s : ℤ) - d) * K (s : ℤ) := by
    intro s; rw [← sub_eq_add_neg, mul_comm]
  rw [Finset.sum_congr rfl fun s _ => hcast s]
  -- Both sums equal ∑ z ∈ Icc (-|d|) (H + |d|), K z * K (z + d)
  let M : ℕ := H + d.natAbs
  have h1 : ∑ s ∈ Finset.range H, K ((s : ℤ) - d) * K (s : ℤ) =
      ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), K z * K (z + d) := by
    have hsub : (Finset.range H).image (fun s : ℕ => (s : ℤ) - d) ⊆
        Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
      rw [Finset.mem_range] at hs
      rw [Finset.mem_Icc]; omega
    symm
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
      refine Finset.sum_congr rfl fun s _ => by ring_nf
    · intro z _ hz
      have hzero : K (z + d) = 0 := by
        apply hK_supp
        intro ⟨h0, hlt⟩
        apply hz
        refine Finset.mem_image.mpr ⟨(z + d).toNat, Finset.mem_range.mpr (by omega), by omega⟩
      rw [hzero, mul_zero]
  have h2 : ∑ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + d) =
      ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), K z * K (z + d) := by
    have hsub : (Finset.range H).image (fun s : ℕ => (s : ℤ)) ⊆
        Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
      rw [Finset.mem_range] at hs
      rw [Finset.mem_Icc]; omega
    symm
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (by intro u _ v _ h; exact Int.ofNat.inj h)]
    · intro z _ hz
      have hzero : K z = 0 := by
        apply hK_supp
        intro ⟨h0, hlt⟩
        apply hz
        refine Finset.mem_image.mpr ⟨z.toNat, Finset.mem_range.mpr (by omega), by omega⟩
      rw [hzero, zero_mul]
  rw [h1, h2]

/-- Unified bilinear smoothed energy upper bound for any symmetric matrix `X` satisfying
diagonal sum `∑_{i < N} X i i ≤ E` and exact pointwise Sidon diagonal sums
`∑_{i < N - d} X i (i + d) ≤ 1` (`1 ≤ d < N`). Covers both `IsFractionalSidon` and `IsSDP1Feasible`. -/
lemma matrix_energy_upper_bound {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    {X : ℕ → ℕ → ℝ} {E : ℝ}
    (hX_symm : ∀ i, i < N → ∀ j, j < N → X i j = X j i)
    (hX_diag : ∑ i ∈ Finset.range N, X i i ≤ E)
    (hX_off : ∀ d, 1 ≤ d → d < N → ∑ i ∈ Finset.range (N - d), X i (i + d) ≤ 1)
    {K : ℤ → ℝ} (hK_nonneg : ∀ z, 0 ≤ K z)
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0)
    (hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1) :
    ∑ n ∈ Finset.range (N + H - 1),
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          K ((n : ℤ) - (i : ℤ)) * X i j * K ((n : ℤ) - (j : ℤ)) ≤
      1 + (E - 1) * autocorr H K 0 := by
  -- 1. Interchange sums and identify `autocorr H K (i - j)`
  have hexpand :
      ∑ n ∈ Finset.range (N + H - 1),
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          K ((n : ℤ) - (i : ℤ)) * X i j * K ((n : ℤ) - (j : ℤ)) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        X i j * autocorr H K ((i : ℤ) - (j : ℤ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hiN := Finset.mem_range.mp hi
    have hfact :
        ∑ n ∈ Finset.range (N + H - 1),
          K ((n : ℤ) - (i : ℤ)) * X i j * K ((n : ℤ) - (j : ℤ)) =
        X i j * ∑ n ∈ Finset.range (N + H - 1),
          K ((n : ℤ) - (i : ℤ)) * K ((n : ℤ) - (j : ℤ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [hfact]
    congr 1
    unfold autocorr
    have hsub : (Finset.range H).image (fun s => i + s) ⊆ Finset.range (N + H - 1) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
      rw [Finset.mem_range] at hs ⊢; omega
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
      refine Finset.sum_congr rfl fun s _ => ?_
      have h1 : ((i + s : ℕ) : ℤ) - (i : ℤ) = (s : ℤ) := by omega
      have h2 : ((i + s : ℕ) : ℤ) - (j : ℤ) = (s : ℤ) + ((i : ℤ) - (j : ℤ)) := by omega
      rw [h1, h2]
    · intro n _ hn
      have hzero : K ((n : ℤ) - (i : ℤ)) = 0 := by
        apply hK_supp
        intro ⟨h0, hlt⟩
        apply hn
        exact Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), by omega⟩
      rw [hzero, zero_mul]
  rw [hexpand]
  -- 2. Split into diagonal `i = j`, upper triangle `i < j`, and lower triangle `j < i`
  have htri :
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, X i j * autocorr H K ((i : ℤ) - (j : ℤ)) =
      (∑ i ∈ Finset.range N, X i i) * autocorr H K 0 +
      2 * ∑ d ∈ Finset.Ico 1 N,
        autocorr H K (d : ℤ) * ∑ i ∈ Finset.range (N - d), X i (i + d) := by
    let P := Finset.range N ×ˢ Finset.range N
    let P0 := P.filter (fun p => p.1 = p.2)
    let Ppos := P.filter (fun p => p.1 < p.2)
    let Pneg := P.filter (fun p => p.2 < p.1)
    have hpart :
        ∑ p ∈ P, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        (∑ p ∈ P0, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ))) +
        (∑ p ∈ Ppos, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ))) +
        (∑ p ∈ Pneg, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ))) := by
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
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P0, Ppos, Finset.mem_filter] at h1 h2; omega
      have hd2 : Disjoint (P0 ∪ Ppos) Pneg := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [P0, Ppos, Pneg, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
      rw [hunion, Finset.sum_union hd2, Finset.sum_union hd1]
    have hP0 : ∑ p ∈ P0, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        (∑ i ∈ Finset.range N, X i i) * autocorr H K 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_nbij (fun p => p.1) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [P0, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact hp.1.1
      · intro p hp q hq heq
        dsimp only at heq
        simp only [P0, Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext heq (by omega)
      · intro i hi
        refine ⟨(i, i), ?_, rfl⟩
        simp only [P0, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hi ⊢
        exact ⟨⟨hi, hi⟩, trivial⟩
      · intro p hp
        simp only [P0, Finset.mem_filter] at hp
        rw [hp.2, sub_self]
    have hPpos : ∑ p ∈ Ppos, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ d ∈ Finset.Ico 1 N, autocorr H K (d : ℤ) * ∑ i ∈ Finset.range (N - d), X i (i + d) := by
      have hbi : ∑ p ∈ Ppos, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
          ∑ d ∈ Finset.Ico 1 N, ∑ i ∈ Finset.range (N - d),
            X i (i + d) * autocorr H K (d : ℤ) := by
        have hsig :
            ∑ d ∈ Finset.Ico 1 N, ∑ i ∈ Finset.range (N - d),
              X i (i + d) * autocorr H K (d : ℤ) =
            ∑ x ∈ (Finset.Ico 1 N).sigma (fun d => Finset.range (N - d)),
              X x.2 (x.2 + x.1) * autocorr H K (x.1 : ℤ) :=
          Finset.sum_sigma' (Finset.Ico 1 N) (fun d => Finset.range (N - d))
            (fun d i => X i (i + d) * autocorr H K (d : ℤ))
        rw [hsig]
        refine Finset.sum_nbij (fun p => ⟨p.2 - p.1, p.1⟩) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_range, Finset.mem_sigma, Finset.mem_Ico] at hp ⊢
          omega
        · intro p hp q hq heq
          simp only [Ppos, Finset.mem_coe, Finset.mem_filter] at hp hq
          have h1 : p.2 - p.1 = q.2 - q.1 := congrArg Sigma.fst heq
          have h2 : p.1 = q.1 := congrArg Sigma.snd heq
          exact Prod.ext h2 (by omega)
        · intro ⟨d, i⟩ hdi
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_range] at hdi
          rcases hdi with ⟨⟨hd1, hdN⟩, hi⟩
          refine ⟨(i, i + d), ?_, ?_⟩
          · simp only [Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range]
            exact ⟨⟨by omega, by omega⟩, by omega⟩
          · simp [Nat.add_sub_cancel_left]
        · intro p hp
          simp only [Ppos, Finset.mem_filter] at hp
          have hadd : p.1 + (p.2 - p.1) = p.2 := by omega
          have hsub : (p.1 : ℤ) - (p.2 : ℤ) = -((p.2 - p.1 : ℕ) : ℤ) := by omega
          dsimp only
          rw [hadd, hsub, autocorr_neg hK_supp]
      rw [hbi]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hPneg : ∑ p ∈ Pneg, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) =
        ∑ p ∈ Ppos, X p.1 p.2 * autocorr H K ((p.1 : ℤ) - (p.2 : ℤ)) := by
      refine Finset.sum_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Pneg, Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp
        simp only [Pneg, Ppos, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp ⊢
        refine ⟨(p.2, p.1), ?_, rfl⟩
        simp only [Pneg, P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p hp
        simp only [Pneg, P, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        dsimp only
        rw [hX_symm p.1 hp.1.1 p.2 hp.1.2]
        have hneg : (p.1 : ℤ) - (p.2 : ℤ) = -((p.2 : ℤ) - (p.1 : ℤ)) := by ring
        rw [hneg, autocorr_neg hK_supp]
    rw [← Finset.sum_product']
    change ∑ p ∈ P, _ = _
    rw [hpart, hP0, hPneg, hPpos]
    ring
  rw [htri]
  -- 3. Bound diagonal by `E * autocorr H K 0` and off-diagonal by `1 - autocorr H K 0`
  have hdiag_le : (∑ i ∈ Finset.range N, X i i) * autocorr H K 0 ≤ E * autocorr H K 0 :=
    mul_le_mul_of_nonneg_right hX_diag (autocorr_nonneg H hK_nonneg 0)
  have hoff_step :
      ∑ d ∈ Finset.Ico 1 N, autocorr H K (d : ℤ) * ∑ i ∈ Finset.range (N - d), X i (i + d) ≤
      ∑ d ∈ Finset.Ico 1 N, autocorr H K (d : ℤ) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Ico] at hd
    calc autocorr H K (d : ℤ) * ∑ i ∈ Finset.range (N - d), X i (i + d)
        ≤ autocorr H K (d : ℤ) * 1 :=
          mul_le_mul_of_nonneg_left (hX_off d hd.1 hd.2) (autocorr_nonneg H hK_nonneg _)
      _ = autocorr H K (d : ℤ) := mul_one _
  -- Relate `2 * ∑_{d ∈ Ico 1 N} autocorr H K d` to `∑_{d ∈ Icc (-(H-1)) (H-1)} autocorr H K d - autocorr H K 0`
  have hsym_sum :
      2 * ∑ d ∈ Finset.Ico 1 N, autocorr H K (d : ℤ) ≤
      (∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), autocorr H K d) - autocorr H K 0 := by
    let I := (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)).erase 0
    have h0mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1) := by
      rw [Finset.mem_Icc]; omega
    have hIeq : ∑ d ∈ I, autocorr H K d =
        (∑ d ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1), autocorr H K d) - autocorr H K 0 := by
      have := Finset.add_sum_erase (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1)) (autocorr H K) h0mem
      linarith
    rw [← hIeq]
    -- Restrict `Ico 1 N` to `d < H` (for `d ≥ H`, `autocorr H K d = 0`)
    have htrunc : ∑ d ∈ Finset.Ico 1 N, autocorr H K (d : ℤ) =
        ∑ d ∈ (Finset.Ico 1 N).filter (fun d => d < H), autocorr H K (d : ℤ) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun d hd hdn => ?_
      have hge : H ≤ d := by
        by_contra hlt; push Not at hlt
        exact hdn (Finset.mem_filter.mpr ⟨hd, hlt⟩)
      unfold autocorr
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Finset.mem_range] at hs
      rw [hK_supp ((s : ℤ) + (d : ℤ)) (by omega), mul_zero]
    rw [htrunc]
    let Spos := ((Finset.Ico 1 N).filter (fun d => d < H)).image (fun d : ℕ => (d : ℤ))
    let Sneg := ((Finset.Ico 1 N).filter (fun d => d < H)).image (fun d : ℕ => -(d : ℤ))
    have hpos_eq : ∑ d ∈ Spos, autocorr H K d =
        ∑ d ∈ (Finset.Ico 1 N).filter (fun d => d < H), autocorr H K (d : ℤ) := by
      rw [Finset.sum_image (by intro u _ v _ h; exact Int.ofNat.inj h)]
    have hneg_eq : ∑ d ∈ Sneg, autocorr H K d =
        ∑ d ∈ (Finset.Ico 1 N).filter (fun d => d < H), autocorr H K (d : ℤ) := by
      rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
      refine Finset.sum_congr rfl fun d _ => autocorr_neg hK_supp (d : ℤ)
    have hdisj : Disjoint Spos Sneg := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      rcases Finset.mem_image.mp hz1 with ⟨u, hu, rfl⟩
      rcases Finset.mem_image.mp hz2 with ⟨v, hv, hveq⟩
      rw [Finset.mem_filter, Finset.mem_Ico] at hu hv
      omega
    have hsub : Spos ∪ Sneg ⊆ I := by
      intro z hz
      rw [Finset.mem_union] at hz
      rcases hz with hz | hz
      · rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
        rw [Finset.mem_filter, Finset.mem_Ico] at hu
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      · rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
        rw [Finset.mem_filter, Finset.mem_Ico] at hu
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have hunion_le := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => autocorr_nonneg H hK_nonneg d)
    rw [Finset.sum_union hdisj, hpos_eq, hneg_eq] at hunion_le
    linarith
  have hsum1 := sum_autocorr_eq_one hH hK_supp hK_sum
  linarith

/-- Energy upper bound specialized to `IsFractionalSidon N μ` (keeping exact `∑ μ_x^2` dependence). -/
lemma fractional_energy_upper_bound {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    {μ : ℕ → ℝ} (hμ : IsFractionalSidon N μ)
    {K : ℤ → ℝ} (hK_nonneg : ∀ z, 0 ≤ K z)
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0)
    (hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1) :
    ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ Finset.range N, μ x * K ((n : ℤ) - (x : ℤ))) ^ 2 ≤
      1 + ((∑ x ∈ Finset.range N, (μ x) ^ 2) - 1) * autocorr H K 0 := by
  have hsq :
      ∑ n ∈ Finset.range (N + H - 1), (∑ x ∈ Finset.range N, μ x * K ((n : ℤ) - (x : ℤ))) ^ 2 =
      ∑ n ∈ Finset.range (N + H - 1),
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          K ((n : ℤ) - (i : ℤ)) * (μ i * μ j) * K ((n : ℤ) - (j : ℤ)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsq]
  have hdiag : ∑ i ∈ Finset.range N, μ i * μ i ≤ ∑ i ∈ Finset.range N, (μ i) ^ 2 := by
    refine le_of_eq (Finset.sum_congr rfl fun i _ => (sq (μ i)).symm)
  exact matrix_energy_upper_bound hN hH
    (X := fun i j => μ i * μ j) (fun _ _ _ _ => mul_comm _ _) hdiag hμ.2 hK_nonneg hK_supp hK_sum

/-- Energy upper bound specialized to the full Degree-1 Lasserre SDP `IsSDP1Feasible N x X`,
using `X - x x^T ≽ 0` to dominate `(∑ x_i K(n - i))^2` by `∑_{i, j} K(n - i) X i j K(n - j)`. -/
lemma sdp1_energy_upper_bound {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H)
    {x : ℕ → ℝ} {X : ℕ → ℕ → ℝ} (hF : IsSDP1Feasible N x X)
    {K : ℤ → ℝ} (hK_nonneg : ∀ z, 0 ≤ K z)
    (hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0)
    (hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1) :
    ∑ n ∈ Finset.range (N + H - 1), (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) ^ 2 ≤
      1 + ((∑ i ∈ Finset.range N, x i) - 1) * autocorr H K 0 := by
  rcases hF with ⟨hX_symm, hPSD, hX_diag, _, hX_off⟩
  have hstep1 :
      ∑ n ∈ Finset.range (N + H - 1), (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) ^ 2 ≤
      ∑ n ∈ Finset.range (N + H - 1),
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          K ((n : ℤ) - (i : ℤ)) * X i j * K ((n : ℤ) - (j : ℤ)) := by
    refine Finset.sum_le_sum fun n _ => ?_
    let v : ℕ → ℝ := fun i => K ((n : ℤ) - (i : ℤ))
    have hpsd_n := hPSD (-(∑ i ∈ Finset.range N, v i * x i)) v
    have hcomm : ∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ)) =
        ∑ i ∈ Finset.range N, v i * x i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hcomm]
    linarith
  have hdiag_le : ∑ i ∈ Finset.range N, X i i ≤ ∑ i ∈ Finset.range N, x i :=
    le_of_eq (Finset.sum_congr rfl fun i hi => hX_diag i (Finset.mem_range.mp hi))
  exact hstep1.trans
    (matrix_energy_upper_bound hN hH hX_symm hdiag_le hX_off hK_nonneg hK_supp hK_sum)

/-- Unified asymmetric one-sided master inequality for ANY nonnegative weights `x : ℕ → ℝ`
satisfying a smoothed energy upper bound `≤ 1 + (E - 1) * (a / H)`. -/
lemma weighted_asymmetric_master_ineq {m L hh N : ℕ}
    (hm : 1 ≤ m) (hL : 1 ≤ L) (hhh : 1 ≤ hh)
    (hN_large : L * (m * hh) ≤ N)
    {p w x : ℕ → ℝ} {E : ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    (hx_nonneg : ∀ i, i < N → 0 ≤ x i)
    (henergy : ∀ K : ℤ → ℝ,
      (∀ z, 0 ≤ K z) →
      (∀ z : ℤ, ¬(0 ≤ z ∧ z < (m * hh : ℕ)) → K z = 0) →
      (∑ s ∈ Finset.range (m * hh), K (s : ℤ) = 1) →
      ∑ n ∈ Finset.range (N + m * hh - 1),
          (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) ^ 2 ≤
        1 + (E - 1) * autocorr (m * hh) K 0) :
    let H := m * hh
    let a := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
    let b := 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
    (∑ i ∈ Finset.range N, x i) ^ 2 ≤
      ((N : ℝ) + b * (H : ℝ) - 1) * (1 + (E - 1) * (a / (H : ℝ))) := by
  intro H a b
  have hHpos : 1 ≤ H := Nat.mul_pos hm hhh
  have hLH_pos : 1 ≤ L * H := Nat.mul_pos hL hHpos
  have hN_ge_LH : L * H ≤ N := hN_large
  have hhh_pos : (0 : ℝ) < (hh : ℝ) := Nat.cast_pos.mpr hhh
  let K : ℤ → ℝ := fun z => if 0 ≤ z ∧ z < (H : ℤ) then p (z.toNat / hh) / (hh : ℝ) else 0
  have hK_nat : ∀ s, s < H → K (s : ℤ) = p (s / hh) / (hh : ℝ) := by
    intro s hs; dsimp only [K]; rw [if_pos ⟨by omega, by omega⟩]; simp
  have hK_nonneg : ∀ z : ℤ, 0 ≤ K z := by
    intro z; dsimp only [K]
    split_ifs with hz
    · apply div_nonneg
      · exact hp_nonneg _ (Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega))
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
  have hcover_all : ∀ i, i < N → 1 ≤ ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) := by
    intro i _
    by_cases hx : i < L * H
    · let q := i / hh
      let t := i % hh
      have hq_lt : q < L * m := by
        have : i < (L * m) * hh := by dsimp only [H] at hx; linarith
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])
      have ht_lt : t < hh := Nat.mod_lt i hhh
      have hx_eq : i = q * hh + t := (Nat.div_add_mod' i hh).symm
      have hcongr : ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) =
          ∑ s ∈ Finset.range (m * hh), (p (s / hh) / (hh : ℝ)) * w ((i + s) / hh) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hK_nat s (Finset.mem_range.mp hs), hQ_eq_w]
      rw [hcongr, sum_range_mul_blocks]
      have hblock : ∀ idx ∈ Finset.range m,
          ∑ r ∈ Finset.range hh,
              (p ((idx * hh + r) / hh) / (hh : ℝ)) * w ((i + (idx * hh + r)) / hh) =
            (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p idx * w (q + idx)) +
            ((t : ℝ) / (hh : ℝ)) * (p idx * w (q + 1 + idx)) := by
        intro idx _
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.sub_le hh t)]
        have hpart1 :
            ∑ r ∈ Finset.range (hh - t),
                (p ((idx * hh + r) / hh) / (hh : ℝ)) * w ((i + (idx * hh + r)) / hh) =
            (((hh - t : ℕ) : ℝ) / (hh : ℝ)) * (p idx * w (q + idx)) := by
          have hconst : ∀ r ∈ Finset.range (hh - t),
              (p ((idx * hh + r) / hh) / (hh : ℝ)) * w ((i + (idx * hh + r)) / hh) =
              (p idx / (hh : ℝ)) * w (q + idx) := by
            intro r hr; rw [Finset.mem_range] at hr
            have hd1 : (idx * hh + r) / hh = idx := add_mul_div_self_right_lt hhh (by omega)
            have hd2 : (i + (idx * hh + r)) / hh = q + idx := by
              have heq : i + (idx * hh + r) = (q + idx) * hh + (t + r) := by rw [hx_eq]; ring
              rw [heq, add_mul_div_self_right_lt hhh (by omega)]
            rw [hd1, hd2]
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        have hpart2 :
            ∑ r ∈ Finset.Ico (hh - t) hh,
                (p ((idx * hh + r) / hh) / (hh : ℝ)) * w ((i + (idx * hh + r)) / hh) =
            ((t : ℝ) / (hh : ℝ)) * (p idx * w (q + 1 + idx)) := by
          have hconst : ∀ r ∈ Finset.Ico (hh - t) hh,
              (p ((idx * hh + r) / hh) / (hh : ℝ)) * w ((i + (idx * hh + r)) / hh) =
              (p idx / (hh : ℝ)) * w (q + 1 + idx) := by
            intro r hr; rw [Finset.mem_Ico] at hr
            have hd1 : (idx * hh + r) / hh = idx := add_mul_div_self_right_lt hhh hr.2
            have hd2 : (i + (idx * hh + r)) / hh = q + 1 + idx := by
              have hmul : (q + 1 + idx) * hh = q * hh + hh + idx * hh := by ring
              have heq : i + (idx * hh + r) = (q + 1 + idx) * hh + (t + r - hh) := by
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
    · have h1 : ∀ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) = K (s : ℤ) := by
        intro s _; dsimp only [Q]; rw [if_neg (by omega), mul_one]
      rw [Finset.sum_congr rfl h1, hK_sum]
  have hinner_ge : ∑ i ∈ Finset.range N, x i ≤
      ∑ n ∈ Finset.range (N + H - 1), Q n * (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) := by
    have hstep1 : ∑ i ∈ Finset.range N, x i ≤
        ∑ i ∈ Finset.range N, x i * ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hiN := Finset.mem_range.mp hi
      calc x i = x i * 1 := (mul_one _).symm
        _ ≤ x i * ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) :=
            mul_le_mul_of_nonneg_left (hcover_all i hiN) (hx_nonneg i hiN)
    have hstep2 :
        ∑ i ∈ Finset.range N, x i * ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) =
        ∑ n ∈ Finset.range (N + H - 1),
          Q n * (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) := by
      have hreidx : ∀ i ∈ Finset.range N,
          x i * ∑ s ∈ Finset.range H, K (s : ℤ) * Q (i + s) =
          ∑ n ∈ Finset.range (N + H - 1), Q n * (x i * K ((n : ℤ) - (i : ℤ))) := by
        intro i hi
        have hiN := Finset.mem_range.mp hi
        have hsub : (Finset.range H).image (fun s => i + s) ⊆ Finset.range (N + H - 1) := by
          intro n hn; rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
          rw [Finset.mem_range] at hs ⊢; omega
        symm
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [show ((i + s : ℕ) : ℤ) - (i : ℤ) = (s : ℤ) by omega]; ring
        · intro n _ hn
          have hzero : K ((n : ℤ) - (i : ℤ)) = 0 := by
            apply hK_supp; intro ⟨h0, hlt⟩; apply hn
            exact Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), by omega⟩
          rw [hzero, mul_zero, mul_zero]
      rw [Finset.sum_congr rfl hreidx, Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
    linarith
  have hxsum_nonneg : 0 ≤ ∑ i ∈ Finset.range N, x i :=
    Finset.sum_nonneg fun i hi => hx_nonneg i (Finset.mem_range.mp hi)
  have hsq_le : (∑ i ∈ Finset.range N, x i) ^ 2 ≤
      (∑ n ∈ Finset.range (N + H - 1),
        Q n * (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ)))) ^ 2 := by
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
    Q (fun n => ∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ)))
  have hen := henergy K hK_nonneg hK_supp hK_sum
  rw [hC0] at hen
  have hQ_nonneg : 0 ≤ ∑ n ∈ Finset.range (N + H - 1), (Q n) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcomb := (hsq_le.trans hcs).trans (mul_le_mul_of_nonneg_left hen hQ_nonneg)
  rwa [hQ_norm] at hcomb

/-- Coarse Lindström bound for any nonnegative weight `x` satisfying the uniform-window energy
inequality with `E ≤ ∑ x_i`: `∑ x_i ≤ √N + N^(1/4) + 1`. -/
lemma weighted_lindstrom_bound {N : ℕ} (hN : 1 ≤ N) {x : ℕ → ℝ}
    (hx_nonneg : ∀ i, i < N → 0 ≤ x i)
    (henergy : ∀ H : ℕ, 1 ≤ H → ∀ K : ℤ → ℝ,
      (∀ z, 0 ≤ K z) →
      (∀ z : ℤ, ¬(0 ≤ z ∧ z < (H : ℤ)) → K z = 0) →
      (∑ s ∈ Finset.range H, K (s : ℤ) = 1) →
      ∑ n ∈ Finset.range (N + H - 1),
          (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) ^ 2 ≤
        1 + ((∑ i ∈ Finset.range N, x i) - 1) * autocorr H K 0) :
    ∑ i ∈ Finset.range N, x i ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  set k : ℝ := ∑ i ∈ Finset.range N, x i
  have hk_nonneg : 0 ≤ k := Finset.sum_nonneg fun i hi => hx_nonneg i (Finset.mem_range.mp hi)
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hN_pos _
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]; dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  let H : ℕ := Nat.floor (t ^ 3) + 1
  have hH : 1 ≤ H := Nat.succ_pos _
  have hH_gt : t ^ 3 < (H : ℝ) := by
    dsimp only [H]; rw [Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one (t ^ 3)
  have hH_le : (H : ℝ) ≤ t ^ 3 + 1 := by
    dsimp only [H]; rw [Nat.cast_add, Nat.cast_one]
    have := Nat.floor_le (pow_nonneg ht_pos.le 3); linarith
  -- Apply uniform kernel `K(s) = 1/H` on `[0, H)`
  let K : ℤ → ℝ := fun z => if 0 ≤ z ∧ z < H then (1 : ℝ) / (H : ℝ) else 0
  have hHposR : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  have hK_nonneg : ∀ z, 0 ≤ K z := fun z => by dsimp only [K]; split_ifs <;> positivity
  have hK_supp : ∀ z : ℤ, ¬(0 ≤ z ∧ z < H) → K z = 0 := fun z hz => by
    dsimp only [K]; rw [if_neg hz]
  have hK_sum : ∑ s ∈ Finset.range H, K (s : ℤ) = 1 := by
    have : ∀ s ∈ Finset.range H, K (s : ℤ) = 1 / (H : ℝ) := fun s hs => by
      rw [Finset.mem_range] at hs; dsimp only [K]; rw [if_pos ⟨by omega, by omega⟩]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have hC0 : autocorr H K 0 = 1 / (H : ℝ) := by
    unfold autocorr
    have : ∀ s ∈ Finset.range H, K (s : ℤ) * K ((s : ℤ) + 0) = (1 / (H : ℝ)) ^ 2 := fun s hs => by
      rw [Finset.mem_range] at hs; dsimp only [K]; rw [add_zero, if_pos ⟨by omega, by omega⟩, sq]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have hsum_u : ∑ n ∈ Finset.range (N + H - 1),
      (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) = k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_sum]
    have hiN := Finset.mem_range.mp hi
    have hsub : (Finset.range H).image (fun s => i + s) ⊆ Finset.range (N + H - 1) := by
      intro n hn; rcases Finset.mem_image.mp hn with ⟨s, hs, rfl⟩
      rw [Finset.mem_range] at hs ⊢; omega
    have h1 : ∑ n ∈ Finset.range (N + H - 1), K ((n : ℤ) - (i : ℤ)) = 1 := by
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (by intro u _ v _ h; dsimp only at h; omega)]
        convert hK_sum using 2 with s; congr 1; omega
      · intro n _ hn
        apply hK_supp; intro ⟨h0, hlt⟩; apply hn
        exact Finset.mem_image.mpr ⟨n - i, Finset.mem_range.mpr (by omega), by omega⟩
    rw [h1, mul_one]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (N + H - 1))
    (fun _ => (1 : ℝ)) (fun n => ∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  rw [hsum_u] at hcs
  have hcardJ : ((N + H - 1 : ℕ) : ℝ) = (N : ℝ) + (H : ℝ) - 1 := by
    have : 1 ≤ N + H := by omega
    rw [Nat.cast_sub this, Nat.cast_add, Nat.cast_one]
  rw [hcardJ] at hcs
  have hen := henergy H hH K hK_nonneg hK_supp hK_sum
  rw [hC0] at hen
  have hJ_nonneg : 0 ≤ (N : ℝ) + (H : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hmaster : k ^ 2 * (H : ℝ) ≤ ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + k - 1) := by
    have h1 := hcs.trans (mul_le_mul_of_nonneg_left hen hJ_nonneg)
    have h2 := mul_le_mul_of_nonneg_right h1 hHposR.le
    have h3 : ((N : ℝ) + (H : ℝ) - 1) * (1 + (k - 1) * (1 / (H : ℝ))) * (H : ℝ) =
        ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + k - 1) := by field_simp; ring
    linarith
  -- Same 5-line quadratic finish as `lindstrom_theorem`
  have ht1 : 1 ≤ t := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hH_ge_1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hNH_le : (N : ℝ) + (H : ℝ) - 1 ≤ t ^ 4 + t ^ 3 := by linarith [ht4, hH_le]
  have hk_bound : k ^ 2 * (H : ℝ) ≤ (t ^ 4 + t ^ 3) * ((H : ℝ) + k) := by
    have h1 : (H : ℝ) + k - 1 ≤ (H : ℝ) + k := by linarith
    have h2 : ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + k - 1) ≤
        ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + k) := mul_le_mul_of_nonneg_left h1 hJ_nonneg
    have h3 : ((N : ℝ) + (H : ℝ) - 1) * ((H : ℝ) + k) ≤ (t ^ 4 + t ^ 3) * ((H : ℝ) + k) :=
      mul_le_mul_of_nonneg_right hNH_le (by linarith)
    exact hmaster.trans (h2.trans h3)
  by_contra hgt
  push Not at hgt
  have hk_gt : t ^ 2 + t + 1 < k := by linarith [ht2]
  have hquad_pos : 0 < k ^ 2 * (H : ℝ) - (t ^ 4 + t ^ 3) * ((H : ℝ) + k) := by
    have h1 : (t ^ 2 + t) * t ^ 3 < (t ^ 2 + t) * (H : ℝ) :=
      mul_lt_mul_of_pos_left hH_gt (by positivity)
    have h2 : (t ^ 2 + t + 1) ^ 2 = t ^ 4 + 2 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1 := by ring
    have hk_sq : (t ^ 2 + t + 1) ^ 2 < k ^ 2 := by nlinarith
    have hdiff_k : k ^ 2 - (t ^ 4 + t ^ 3) ≥ (k - (t ^ 2 + t)) * (k + (t ^ 2 + t)) := by nlinarith
    -- Check at k > t^2 + t + 1: k^2 * H - (t^4 + t^3) * (H + k) =
    --   (k^2 - t^4 - t^3) * H - (t^4 + t^3) * k
    -- > (k^2 - t^4 - t^3) * t^3 - (t^4 + t^3) * k = t^3 * (k^2 - (t + 1) * k - t^4 - t^3)
    have hfac : k ^ 2 - (t ^ 4 + t ^ 3) > 0 := by nlinarith
    have hmulH : (k ^ 2 - (t ^ 4 + t ^ 3)) * t ^ 3 < (k ^ 2 - (t ^ 4 + t ^ 3)) * (H : ℝ) :=
      mul_lt_mul_of_pos_left hH_gt hfac
    have hpoly : 0 < k ^ 2 - (t + 1) * k - (t ^ 4 + t ^ 3) := by
      have hfactor : k ^ 2 - (t + 1) * k - (t ^ 4 + t ^ 3) =
          (k - (t ^ 2 + t + 1)) * (k + t ^ 2) + (t ^ 2 + t + 1) * t ^ 2 -
          (t + 1) * (t ^ 2 + t + 1) + (t ^ 2 + t + 1) ^ 2 - (t ^ 4 + t ^ 3) -
          (t ^ 2 + t + 1) * t ^ 2 := by ring
      have h1' : (t ^ 2 + t + 1) ^ 2 - (t + 1) * (t ^ 2 + t + 1) - (t ^ 4 + t ^ 3) =
          t ^ 2 + 1 - 1 := by ring
      -- Wait: at k = t^2 + t + 1, k^2 - (t+1)k - t^4 - t^3 = t^2 > 0!
      have hval : (t ^ 2 + t + 1) ^ 2 - (t + 1) * (t ^ 2 + t + 1) - (t ^ 4 + t ^ 3) = t ^ 2 := by ring
      have hmono : (k - (t ^ 2 + t + 1)) * (k + t ^ 2) > 0 := by nlinarith
      nlinarith
    have hmul_t3 : 0 < t ^ 3 * (k ^ 2 - (t + 1) * k - (t ^ 4 + t ^ 3)) :=
      mul_pos (pow_pos ht_pos 3) hpoly
    nlinarith
  linarith

/-- Opaque asymmetric asymptotic transfer theorem for arbitrary nonnegative weights `x` with
`L^2`-integrality parameter `θ ∈ (0, 1]`. Keeping `p` and `w` opaque prevents `Finset.range`
unfolding during real arithmetic tactics. -/
private lemma weighted_asymmetric_transfer {m L : ℕ} (hm : 1 ≤ m) (hL : 1 ≤ L)
    {p w : ℕ → ℝ}
    (hp_nonneg : ∀ i, i < m → 0 ≤ p i)
    (hp_sum : ∑ i ∈ Finset.range m, p i = 1)
    (hw_tail : ∀ j, L * m ≤ j → w j = 1)
    (hcover : ∀ q, q ≤ L * m → 1 ≤ ∑ i ∈ Finset.range m, p i * w (q + i))
    {θ γ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1) (hγ_pos : 0 < γ)
    (hb_pos : 0 < 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ)))
    (hab_lt : θ * ((m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2) *
        (1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))) < γ ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      (∀ i, i < N → 0 ≤ x i) →
      (∀ H : ℕ, 1 ≤ H → ∀ K : ℤ → ℝ,
        (∀ z, 0 ≤ K z) →
        (∀ z : ℤ, ¬(0 ≤ z ∧ z < (H : ℤ)) → K z = 0) →
        (∑ s ∈ Finset.range H, K (s : ℤ) = 1) →
        ∑ n ∈ Finset.range (N + H - 1),
            (∑ i ∈ Finset.range N, x i * K ((n : ℤ) - (i : ℤ))) ^ 2 ≤
          1 + (θ * (∑ i ∈ Finset.range N, x i) - 1) * autocorr H K 0) →
      ∑ i ∈ Finset.range N, x i ≤ Real.sqrt (N : ℝ) + γ * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  set a : ℝ := (m : ℝ) * ∑ i ∈ Finset.range m, (p i) ^ 2
  set b : ℝ := 1 + ((∑ j ∈ Finset.range (L * m), (w j) ^ 2) / (m : ℝ) - (L : ℝ))
  have ha_ge_one : 1 ≤ a := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ => (1 : ℝ)) p
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
    rw [hp_sum, one_pow] at hcs; exact hcs
  have ha_pos : 0 < a := by linarith
  set aθ : ℝ := θ * a
  have haθ_pos : 0 < aθ := mul_pos hθ_pos ha_pos
  set g : ℝ := Real.sqrt (aθ * b)
  have hg_pos : 0 < g := Real.sqrt_pos.mpr (mul_pos haθ_pos hb_pos)
  have hg_sq : g ^ 2 = aθ * b := Real.sq_sqrt (mul_pos haθ_pos hb_pos).le
  have hg_lt : g < γ := by
    have hsq : g ^ 2 < γ ^ 2 := by rw [hg_sq]; exact hab_lt
    nlinarith
  set r : ℝ := Real.sqrt (aθ / b)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos haθ_pos hb_pos)
  have hbr : b * r = g := by
    dsimp only [r, g]
    rw [show b * Real.sqrt (aθ / b) = Real.sqrt (b ^ 2 * (aθ / b)) from by
      rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb_pos.le]]
    congr 1; field_simp
  have haθ_div_r : aθ / r = g := by
    rw [div_eq_iff hr_pos.ne']
    rw [show g * r = Real.sqrt ((aθ * b) * (aθ / b)) from by
      dsimp only [g, r]; rw [← Real.sqrt_mul (mul_pos haθ_pos hb_pos).le]]
    rw [show aθ * b * (aθ / b) = aθ ^ 2 from by field_simp, Real.sqrt_sq haθ_pos.le]
  let C : ℝ := g ^ 2 + 2 * g + b * (m : ℝ) + 2 * g ^ 2 +
    g * (b * (m : ℝ)) + 2 * g * (b * (m : ℝ))
  let T : ℝ := max 1 (max ((L : ℝ) * r + (L : ℝ) * (m : ℝ) + 1)
      ((|C| + 1) / (2 * (γ - g)) + 1))
  let N0 : ℕ := Nat.ceil (T ^ 4) + 1
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN x hx_nonneg henergy
  have hT_ge_one : 1 ≤ T := le_max_left _ _
  have hN_ge_T4 : T ^ 4 ≤ (N : ℝ) := by
    have h1 : T ^ 4 ≤ (Nat.ceil (T ^ 4) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (T ^ 4) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (show Nat.ceil (T ^ 4) ≤ N by omega)
    linarith
  set t : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < T ^ 4 := by positivity
    linarith
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : (1 : ℝ) ≤ T ^ 4 := one_le_pow₀ hT_ge_one
      linarith
    exact_mod_cast h1
  have ht4 : t ^ 4 = (N : ℝ) := by
    dsimp only [t]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
  have ht2 : t ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]; dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
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
  set k : ℝ := ∑ i ∈ Finset.range N, x i
  have hk_nonneg : 0 ≤ k := Finset.sum_nonneg fun i hi => hx_nonneg i (Finset.mem_range.mp hi)
  have hk_lind : k ≤ t ^ 2 + t + 1 := by
    have hl := weighted_lindstrom_bound hN1 hx_nonneg (fun H' hH' K h1 h2 h3 => by
      have hen := henergy H' hH' K h1 h2 h3
      have hc0 := autocorr_nonneg H' h1 0
      have hθk : θ * (∑ i ∈ Finset.range N, x i) ≤ ∑ i ∈ Finset.range N, x i := by nlinarith
      nlinarith)
    have hkeq : k = ∑ i ∈ Finset.range N, x i := rfl
    have hteq : t = (N : ℝ) ^ (4⁻¹ : ℝ) := rfl
    linarith [ht2, hl]
  have hmaster : k ^ 2 ≤ ((N : ℝ) + b * (H : ℝ) - 1) * (1 + (θ * k - 1) * (a / (H : ℝ))) :=
    weighted_asymmetric_master_ineq hm hL hhh hN_large
      hp_nonneg hp_sum hw_tail hcover hx_nonneg (E := θ * k)
      (fun K h1 h2 h3 => henergy (m * hh) (Nat.mul_pos hm hhh) K h1 h2 h3)
  have hfac1 : (N : ℝ) + b * (H : ℝ) - 1 ≤ t ^ 4 + g * t ^ 3 + b * (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hH_le hb_pos.le
    have : b * (H : ℝ) ≤ g * t ^ 3 + b * (m : ℝ) := by
      calc b * (H : ℝ) ≤ b * (r * t ^ 3 + (m : ℝ)) := this
        _ = (b * r) * t ^ 3 + b * (m : ℝ) := by ring
        _ = g * t ^ 3 + b * (m : ℝ) := by rw [hbr]
    linarith [ht4]
  have hfac2 : 1 + (θ * k - 1) * (a / (H : ℝ)) ≤ 1 + g / t + 2 * g / t ^ 2 := by
    have hH_pos' : 0 < (H : ℝ) := by linarith [mul_pos hr_pos (pow_pos ht_pos 3)]
    have hinv : 1 / (H : ℝ) ≤ 1 / (r * t ^ 3) :=
      one_div_le_one_div_of_le (mul_pos hr_pos (pow_pos ht_pos 3)) hH_gt.le
    have haθH : aθ / (H : ℝ) ≤ g / t ^ 3 := by
      have : aθ / (H : ℝ) ≤ aθ / (r * t ^ 3) := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv haθ_pos.le
      calc aθ / (H : ℝ) ≤ aθ / (r * t ^ 3) := this
        _ = (aθ / r) / t ^ 3 := by rw [div_mul_eq_div_div]
        _ = g / t ^ 3 := by rw [haθ_div_r]
    have hstep : (θ * k - 1) * (a / (H : ℝ)) ≤ k * (aθ / (H : ℝ)) := by
      have hpos_aH : 0 ≤ a / (H : ℝ) := div_nonneg ha_pos.le hH_pos'.le
      have : (θ * k - 1) * (a / (H : ℝ)) = k * (aθ / (H : ℝ)) - a / (H : ℝ) := by
        dsimp only [aθ]; ring
      linarith
    have hk_le2 : k ≤ t ^ 2 + 2 * t := by linarith
    have hk_mul : k * (aθ / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) := by
      have h1 : k * (aθ / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (aθ / (H : ℝ)) :=
        mul_le_mul_of_nonneg_right hk_le2 (div_nonneg haθ_pos.le hH_pos'.le)
      have h2 : (t ^ 2 + 2 * t) * (aθ / (H : ℝ)) ≤ (t ^ 2 + 2 * t) * (g / t ^ 3) :=
        mul_le_mul_of_nonneg_left haθH (by nlinarith)
      exact h1.trans h2
    have hsimp : (t ^ 2 + 2 * t) * (g / t ^ 3) = g / t + 2 * g / t ^ 2 := by field_simp
    linarith
  have hfac1_nonneg : 0 ≤ (N : ℝ) + b * (H : ℝ) - 1 := by
    have hH0 : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by rw [← ht4]; exact one_le_pow₀ ht1
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

/-- Reusable certificate package for our `m = 48, L = 4` asymmetric linear kernel `(asymP, asymW)`. -/
private lemma asym_cert_package :
    (∀ i, i < 48 → 0 ≤ asymP i) ∧
    (∑ i ∈ Finset.range 48, asymP i = 1) ∧
    (∀ j, 4 * 48 ≤ j → asymW j = 1) ∧
    (∀ q, q ≤ 4 * 48 → 1 ≤ ∑ i ∈ Finset.range 48, asymP i * asymW (q + i)) ∧
    (((48 : ℕ) : ℝ) * ∑ i ∈ Finset.range 48, (asymP i) ^ 2 = (48 : ℝ) * 147440 / 2304 ^ 2) ∧
    (1 + ((∑ j ∈ Finset.range (4 * 48), (asymW j) ^ 2) / ((48 : ℕ) : ℝ) - ((4 : ℕ) : ℝ)) =
      1 + (((176012388616832 : ℝ) / 1000000 ^ 2) / 48 - 4)) := by
  refine ⟨fun i _ => by dsimp only [asymP]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [asymP]; rw [← Finset.sum_div, ← Nat.cast_sum, asymPNum_sum]; norm_num
  · intro j hj; dsimp only [asymW, asymWNum]; rw [if_neg (by omega)]; norm_num
  · intro q hq
    have hnat := asym_covering_nat q (Finset.mem_range.mpr (by omega))
    have hreal : (2304000000 : ℝ) ≤
        ((∑ i ∈ Finset.range 48, asymPNum i * asymWNum (q + i) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hsum_eq : ∑ i ∈ Finset.range 48, asymP i * asymW (q + i) =
        ((∑ i ∈ Finset.range 48, asymPNum i * asymWNum (q + i) : ℕ) : ℝ) / 2304000000 := by
      dsimp only [asymP, asymW]; push_cast; rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum_eq]; linarith
  · have hsq : ∑ i ∈ Finset.range 48, (asymP i) ^ 2 = (147440 : ℝ) / 2304 ^ 2 := by
      dsimp only [asymP]
      have : ∀ i ∈ Finset.range 48, ((asymPNum i : ℝ) / 2304) ^ 2 =
          ((asymPNum i ^ 2 : ℕ) : ℝ) / 2304 ^ 2 := fun i _ => by push_cast; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_div, ← Nat.cast_sum, asymPNum_sq_sum]; norm_num
    rw [hsq]; norm_num
  · have hsq : ∑ j ∈ Finset.range (4 * 48), (asymW j) ^ 2 =
        (176012388616832 : ℝ) / 1000000 ^ 2 := by
      dsimp only [asymW]
      have : ∀ j ∈ Finset.range 192, ((asymWNum j : ℝ) / 1000000) ^ 2 =
          ((asymWNum j ^ 2 : ℕ) : ℝ) / 1000000 ^ 2 := fun j _ => by push_cast; ring
      rw [show 4 * 48 = 192 from rfl, Finset.sum_congr rfl this, ← Finset.sum_div,
        ← Nat.cast_sum, asymWNum_sq_sum]; norm_num
    rw [hsq]; norm_num

/-- Exact `θ`-Integrality Upper Envelope for the Pointwise Fractional Sidon Relaxation `M_θ(N)`:
for EVERY `θ ∈ (0, 1]`, for all sufficiently large `N`, EVERY `IsFractionalSidon N μ` with
`L^2`-integrality ratio `∑ μ_x^2 ≤ θ * ∑ μ_x` satisfies
`∑_{x < N} μ(x) ≤ √N + 0.94295 * √θ * N^(1/4)`. -/
theorem fractional_sidon_sub_094295_theta {θ : ℝ} (hθ_pos : 0 < θ) (hθ_le : θ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ μ : ℕ → ℝ,
      IsFractionalSidon N μ →
      (∑ x ∈ Finset.range N, (μ x) ^ 2 ≤ θ * ∑ x ∈ Finset.range N, μ x) →
      ∑ x ∈ Finset.range N, μ x ≤
        Real.sqrt (N : ℝ) + (0.94295 : ℝ) * Real.sqrt θ * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  obtain ⟨hp_nn, hp_s, hw_t, hcov, ha_eq, hb_eq⟩ := asym_cert_package
  have htrans := weighted_asymmetric_transfer (m := 48) (L := 4) (by norm_num) (by norm_num)
    hp_nn hp_s hw_t hcov hθ_pos hθ_le
    (γ := (0.94295 : ℝ) * Real.sqrt θ) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hθ_pos))
    (by rw [hb_eq]; norm_num)
    (by
      rw [ha_eq, hb_eq, mul_pow, Real.sq_sqrt hθ_pos.le]
      have hnum : ((48 : ℝ) * 147440 / 2304 ^ 2) *
          (1 + (((176012388616832 : ℝ) / 1000000 ^ 2) / 48 - 4)) < (0.94295 : ℝ) ^ 2 := by
        norm_num
      nlinarith)
  filter_upwards [htrans, Filter.eventually_ge_atTop 1] with N hN hN1 μ hμ hθ_mu
  refine hN μ (fun i hi => (hμ.1 i hi).1) (fun H hH K h1 h2 h3 => ?_)
  have hen := fractional_energy_upper_bound hN1 hH hμ h1 h2 h3
  have hc0 := autocorr_nonneg H h1 0
  have hmul : ((∑ x ∈ Finset.range N, (μ x) ^ 2) - 1) * autocorr H K 0 ≤
      (θ * (∑ x ∈ Finset.range N, μ x) - 1) * autocorr H K 0 :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hθ_mu 1) hc0
  exact hen.trans (add_le_add (le_refl 1) hmul)

/-- Matching upper bound for the full Degree-1 Lasserre / Shor + RLT SDP `SDP_1(N)`:
for all sufficiently large `N`, EVERY `IsSDP1Feasible N x X` satisfies
`∑_{i < N} x(i) ≤ √N + 0.94295 * N^(1/4)`. -/
theorem sdp1_sub_094295 :
    ∀ᶠ N : ℕ in atTop, ∀ (x : ℕ → ℝ) (X : ℕ → ℕ → ℝ),
      IsSDP1Feasible N x X →
      ∑ i ∈ Finset.range N, x i ≤ Real.sqrt (N : ℝ) + (0.94295 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  obtain ⟨hp_nn, hp_s, hw_t, hcov, ha_eq, hb_eq⟩ := asym_cert_package
  have htrans := weighted_asymmetric_transfer (m := 48) (L := 4) (by norm_num) (by norm_num)
    hp_nn hp_s hw_t hcov (θ := 1) (by norm_num) (le_refl 1) (γ := 0.94295) (by norm_num)
    (by rw [hb_eq]; norm_num)
    (by rw [ha_eq, hb_eq]; norm_num)
  filter_upwards [htrans, Filter.eventually_ge_atTop 1] with N hN hN1 x X hF
  refine hN x (fun i hi => by
    have hdiag := hF.2.2.1 i hi
    have hnn := (hF.2.2.2.1 i hi i hi).1
    linarith) (fun H hH K h1 h2 h3 => ?_)
  simpa only [one_mul] using sdp1_energy_upper_bound hN1 hH hF h1 h2 h3

/-- Concrete machine-checked strict separation `h(6) < M(6) ≤ SDP_1(6)`:
`h(6) ≤ 3`, whereas `μ = [1, 2/5, 2/5, 0, 2/5, 1]` is strictly feasible for both
`IsFractionalSidon 6` and `IsSDP1Feasible 6` with objective `16/5 = 3.2 > 3`. -/
theorem strict_separation_h6_lt_fractional_sdp1 :
    (h 6 : ℝ) < (16 : ℝ) / 5 ∧
    ∃ (μ : ℕ → ℝ) (X : ℕ → ℕ → ℝ),
      IsFractionalSidon 6 μ ∧ IsSDP1Feasible 6 μ X ∧ ∑ i ∈ Finset.range 6, μ i = (16 : ℝ) / 5 := by
  have hh6 : h 6 ≤ 3 := by
    obtain ⟨A, hAsub, hAS, hAcard⟩ := exists_max_sidon 6
    rw [← hAcard]
    by_contra hgt
    push Not at hgt
    have hpairs : (A.offDiag.filter (fun p => p.2 < p.1)).card ≤ 5 := by
      have himg : ((A.offDiag.filter (fun p => p.2 < p.1)).image (fun p => p.1 - p.2)) ⊆
          Finset.Icc 1 5 := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
        rw [Finset.mem_filter, Finset.mem_offDiag] at hp
        have h1 := Finset.mem_Icc.mp (hAsub hp.1.1)
        have h2 := Finset.mem_Icc.mp (hAsub hp.1.2.1)
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2)
          ((A.offDiag.filter (fun p => p.2 < p.1)) : Set (ℕ × ℕ)) := by
        intro p hp q hq heq
        dsimp only at heq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp hq
        have hsum : p.1 + q.2 = q.1 + p.2 := by omega
        rcases hAS p.1 hp.1.1 q.2 hq.1.2.1 q.1 hq.1.1 p.2 hp.1.2.1 hsum with ⟨h1, h2⟩ | ⟨h1, _⟩
        · exact Prod.ext h1 h2.symm
        · omega
      calc (A.offDiag.filter (fun p => p.2 < p.1)).card
          = ((A.offDiag.filter (fun p => p.2 < p.1)).image (fun p => p.1 - p.2)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc 1 5).card := Finset.card_le_card himg
        _ = 5 := by decide
    have hcard_off : 2 * (A.offDiag.filter (fun p => p.2 < p.1)).card = A.offDiag.card := by
      have hunion : A.offDiag =
          A.offDiag.filter (fun p => p.2 < p.1) ∪ A.offDiag.filter (fun p => p.1 < p.2) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
        constructor
        · intro h; rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt'
          · left; exact ⟨h, hlt⟩
          · exact False.elim (h.2.2 heq.symm)
          · right; exact ⟨h, hgt'⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      have hdisj : Disjoint (A.offDiag.filter (fun p => p.2 < p.1))
          (A.offDiag.filter (fun p => p.1 < p.2)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        rw [Finset.mem_filter] at h1 h2; omega
      have hswap : (A.offDiag.filter (fun p => p.1 < p.2)).card =
          (A.offDiag.filter (fun p => p.2 < p.1)).card := by
        refine Finset.card_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
          exact ⟨⟨hp.1.2.1, hp.1.1, Ne.symm hp.1.2.2⟩, hp.2⟩
        · intro p _ q _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
          refine ⟨(p.2, p.1), ?_, rfl⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_offDiag]
          exact ⟨⟨hp.1.2.1, hp.1.1, Ne.symm hp.1.2.2⟩, hp.2⟩
      conv_rhs => rw [hunion]
      rw [Finset.card_union_of_disjoint hdisj, hswap]; ring
    have hoff_eq : A.offDiag.card + A.card = A.card * A.card := by
      have hle : A.card ≤ A.card * A.card := Nat.le_mul_self A.card
      rw [Finset.offDiag_card]; omega
    nlinarith
  have hh6R : (h 6 : ℝ) ≤ 3 := by exact_mod_cast hh6
  refine ⟨by linarith, ?_⟩
  let μ : ℕ → ℝ := fun i =>
    match i with
    | 0 => 1 | 1 => 2 / 5 | 2 => 2 / 5 | 3 => 0 | 4 => 2 / 5 | 5 => 1 | _ => 0
  have hμ : IsFractionalSidon 6 μ := by
    refine ⟨?_, ?_⟩
    · intro x hx
      interval_cases x <;> dsimp only [μ] <;> norm_num
    · intro d hd1 hd6
      interval_cases d <;> simp [Finset.sum_range_succ, μ] <;> norm_num
  refine ⟨μ, (fun i j => if i = j then μ i else μ i * μ j), hμ, (shor_rlt_sdp1_lift hμ).1, ?_⟩
  simp [Finset.sum_range_succ, μ]
  norm_num

/-! ### Section 9: Exact Bose Periodic Fourier Flatness & 3-AP-Free Superset Barrier -/

/-- Exact modular difference set structure of Bose's Sidon set `S ⊆ range (p^2 - 1)`:
for every prime `p`, there exists `S ⊆ range (p^2 - 1)` of size `p` such that
`(a, b) ↦ (a + (p^2 - 1) - b) % (p^2 - 1)` is a bijection from `S.offDiag` onto
`{d ∈ range (p^2 - 1) | ¬((p + 1) ∣ d)}`. -/
lemma bose_modular_difference_set {p : ℕ} (hp : p.Prime) :
    let M := p ^ 2 - 1
    ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ S.card = p ∧
      (∀ q ∈ S.offDiag, (q.1 + M - q.2) % M ∈ (Finset.range M).filter (fun d => ¬((p + 1) ∣ d))) ∧
      Set.InjOn (fun q : ℕ × ℕ => (q.1 + M - q.2) % M) (S.offDiag : Set (ℕ × ℕ)) ∧
      (∀ d ∈ (Finset.range M).filter (fun d => ¬((p + 1) ∣ d)),
        ∃ q ∈ S.offDiag, (q.1 + M - q.2) % M = d) := by
  classical
  intro M
  have : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p 2
  have hcardK : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hcardF : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hp2 : 2 ≤ p := hp.two_le
  have hM_eq : M = (p - 1) * (p + 1) := by
    dsimp only [M]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hM_pos : 0 < M := by dsimp only [M]; exact Nat.sub_pos_of_lt (by nlinarith)
  have hex_theta : ∃ θ : K, θ ∉ Set.range (algebraMap (ZMod p) K) := by
    by_contra hall; push Not at hall
    have hle : Nat.card K ≤ Nat.card (ZMod p) := Nat.card_le_card_of_surjective _ hall
    rw [hcardK, hcardF] at hle; nlinarith
  obtain ⟨θ, hθ⟩ := hex_theta
  have hne0 : ∀ x : ZMod p, θ + algebraMap (ZMod p) K x ≠ 0 := by
    intro x hzero; apply hθ; refine ⟨-x, ?_⟩
    rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hzero).symm
  have hfinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hcardK]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hcardU : Nat.card Kˣ = M := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = M := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hpow_surj : ∀ u : Kˣ, ∃ a : ℕ, a < M ∧ g ^ a = u := by
    intro u
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    let r : ℕ := (k % (M : ℤ)).toNat
    have hr_lt : r < M := by
      have h1 : 0 ≤ k % (M : ℤ) := Int.emod_nonneg k (by omega)
      have h2 : k % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos k (by omega)
      omega
    refine ⟨r, hr_lt, ?_⟩
    have h1 : g ^ (k % (orderOf g : ℤ)) = g ^ k := zpow_mod_orderOf g k
    have h2 : (r : ℤ) = k % (M : ℤ) := by
      have : 0 ≤ k % (M : ℤ) := Int.emod_nonneg k (by omega)
      omega
    rw [hord] at h1
    rw [← zpow_natCast, h2, h1, hk]
  have hex_a : ∀ x : ZMod p,
      ∃ a : ℕ, a < M ∧ (g : K) ^ a = θ + algebraMap (ZMod p) K x := by
    intro x
    obtain ⟨a, haM, hga⟩ := hpow_surj (Units.mk0 (θ + algebraMap (ZMod p) K x) (hne0 x))
    refine ⟨a, haM, ?_⟩
    have := congrArg (Units.val : Kˣ → K) hga
    simpa [Units.val_pow_eq_pow_val] using this
  choose a haM hga using hex_a
  have ha_inj : Function.Injective a := by
    intro x y hxy
    have heq : θ + algebraMap (ZMod p) K x = θ + algebraMap (ZMod p) K y := by
      rw [← hga x, ← hga y, hxy]
    exact (algebraMap (ZMod p) K).injective (add_left_cancel heq)
  -- Characterize the `(p-1)`-torsion subgroup of `Kˣ` as the image of `(ZMod p)ˣ`
  have htors_eq : ∀ d < M, (p + 1) ∣ d →
      ∃ c : ZMod p, (g : K) ^ d = algebraMap (ZMod p) K c := by
    -- The `p - 1` nonzero elements of `ZMod p` map injectively into `{u : Kˣ | u^(p-1) = 1}`,
    -- which has cardinality `p - 1` since `g` has order `(p-1)*(p+1)`.
    let T : Finset Kˣ := Finset.univ.filter (fun u : Kˣ => u ^ (p - 1) = 1)
    let Fimg : Finset Kˣ :=
      (Finset.univ.filter (fun c : ZMod p => c ≠ 0)).image
        (fun c => if h : c ≠ 0 then
          Units.mk0 (algebraMap (ZMod p) K c) ((map_ne_zero _).mpr h) else 1)
    have hsub : Fimg ⊆ T := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨c, hc, rfl⟩
      rw [Finset.mem_filter] at hc
      rw [dif_pos hc.2]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [← map_pow, ZMod.pow_card_sub_one_eq_one hc.2, map_one]
    have hcard_Fimg : Fimg.card = p - 1 := by
      have hinj : Set.InjOn (fun c : ZMod p => if h : c ≠ 0 then
          Units.mk0 (algebraMap (ZMod p) K c) ((map_ne_zero _).mpr h) else 1)
          ((Finset.univ.filter (fun c : ZMod p => c ≠ 0)) : Set (ZMod p)) := by
        intro c₁ hc₁ c₂ hc₂ heq
        dsimp only at heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hc₁ hc₂
        rw [dif_pos hc₁.2, dif_pos hc₂.2] at heq
        have hval := congrArg (Units.val : Kˣ → K) heq
        simp only [Units.val_mk0] at hval
        exact (algebraMap (ZMod p) K).injective hval
      rw [Finset.card_image_of_injOn hinj]
      have hfil : Finset.univ.filter (fun c : ZMod p => c ≠ 0) = Finset.univ.erase (0 : ZMod p) := by
        ext c; simp [ne_comm]
      rw [hfil, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hcard_T : T.card ≤ p - 1 := by
      have hT_sub : T ⊆ (Finset.range (p - 1)).image (fun k => g ^ (k * (p + 1))) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨d, hdM, rfl⟩ := hpow_surj u
        have hpow1 : g ^ (d * (p - 1)) = 1 := by rw [pow_mul]; exact hu.2
        have hdvd : M ∣ d * (p - 1) := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpow1
        have hdiv : (p + 1) ∣ d := by
          rw [hM_eq, mul_comm (p - 1) (p + 1)] at hdvd
          exact (mul_dvd_mul_iff_right (by omega : p - 1 ≠ 0)).mp hdvd
        rcases hdiv with ⟨k, rfl⟩
        refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr ?_, by rw [mul_comm]⟩
        rw [hM_eq] at hdM
        nlinarith
      exact (Finset.card_le_card hT_sub).trans Finset.card_image_le |>.trans (by simp)
    have hTeq : Fimg = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro d hdM hdvd
    have hmemT : g ^ d ∈ T := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← pow_mul]
      rcases hdvd with ⟨k, rfl⟩
      have hmul : (p + 1) * k * (p - 1) = M * k := by rw [hM_eq]; ring
      rw [hmul, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    rw [← hTeq] at hmemT
    rcases Finset.mem_image.mp hmemT with ⟨c, hc, hce⟩
    rw [Finset.mem_filter] at hc
    rw [dif_pos hc.2] at hce
    refine ⟨c, ?_⟩
    have hval := congrArg (Units.val : Kˣ → K) hce
    simpa [Units.val_pow_eq_pow_val] using hval.symm
  -- Build S = image a ⊆ range M
  let S : Finset ℕ := Finset.univ.image a
  have hS_sub : S ⊆ Finset.range M := by
    intro n hn; rcases Finset.mem_image.mp hn with ⟨x, _, rfl⟩
    exact Finset.mem_range.mpr (haM x)
  have hS_card : S.card = p := by
    rw [Finset.card_image_of_injective _ ha_inj, Finset.card_univ, ZMod.card]
  -- Key relation: g ^ ((a x + M - a y) % M) * (θ + y) = θ + x
  have hg_diff : ∀ x y : ZMod p,
      (g : K) ^ ((a x + M - a y) % M) * (θ + algebraMap (ZMod p) K y) =
      θ + algebraMap (ZMod p) K x := by
    intro x y
    have hax := haM x
    have hay := haM y
    rw [← hga y, ← hga x, ← pow_add]
    have hmod_eq : ((a x + M - a y) % M + a y) % M = a x % M := by
      have h1 : (a x + M - a y) % M + a y + M * ((a x + M - a y) / M) = a x + M := by
        have hdm := Nat.div_add_mod (a x + M - a y) M
        omega
      have h2 := congrArg (· % M) h1
      simpa [Nat.add_mul_mod_self_left, Nat.add_mod_right] using h2
    have hpowM : (g : K) ^ M = 1 := by
      have hgm : g ^ M = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
      simpa [Units.val_pow_eq_pow_val] using congrArg (Units.val : Kˣ → K) hgm
    have hpow_mod : ∀ n : ℕ, (g : K) ^ n = (g : K) ^ (n % M) := by
      intro n
      conv_lhs => rw [← Nat.div_add_mod n M]
      rw [pow_add, pow_mul, hpowM, one_pow, one_mul]
    rw [hpow_mod, hmod_eq, ← hpow_mod]
  -- Map `q ↦ (q.1 + M - q.2) % M` maps `S.offDiag` injectively into `filter (¬ (p+1) ∣ ·)`
  let Dset : Finset ℕ := (Finset.range M).filter (fun d => ¬((p + 1) ∣ d))
  have hmaps : ∀ q ∈ S.offDiag, (q.1 + M - q.2) % M ∈ Dset := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    rcases Finset.mem_image.mp hq.1 with ⟨x, _, hx⟩
    rcases Finset.mem_image.mp hq.2.1 with ⟨y, _, hy⟩
    rw [← hx, ← hy]
    have hxy : x ≠ y := fun h => hq.2.2 (by rw [← hx, ← hy, h])
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hM_pos, ?_⟩
    intro hdvd
    obtain ⟨c, hc⟩ := htors_eq _ (Nat.mod_lt _ hM_pos) hdvd
    have heq := hg_diff x y
    rw [hc] at heq
    -- c * (θ + y) = θ + x  ==>  (c - 1) * θ = x - c * y
    have hlin : algebraMap (ZMod p) K (c - 1) * θ = algebraMap (ZMod p) K (x - c * y) := by
      rw [map_sub, map_one, map_sub, map_mul]
      linear_combination heq
    have hc1 : c = 1 := by
      by_contra hne
      have hdiff_ne : c - 1 ≠ 0 := sub_ne_zero.mpr hne
      apply hθ
      refine ⟨(x - c * y) / (c - 1), ?_⟩
      rw [map_div₀]
      have hmap_ne : algebraMap (ZMod p) K (c - 1) ≠ 0 := (map_ne_zero _).mpr hdiff_ne
      rw [div_eq_iff hmap_ne, mul_comm θ, hlin]
    subst hc1
    rw [sub_self, map_zero, zero_mul, one_mul] at hlin
    have : x - y = 0 := (map_eq_zero (algebraMap (ZMod p) K)).mp hlin.symm
    exact hxy (sub_eq_zero.mp this)
  have hinj : Set.InjOn (fun q : ℕ × ℕ => (q.1 + M - q.2) % M) (S.offDiag : Set (ℕ × ℕ)) := by
    intro q₁ hq₁ q₂ hq₂ heq
    dsimp only at heq
    simp only [Finset.mem_coe, Finset.mem_offDiag] at hq₁ hq₂
    rcases Finset.mem_image.mp hq₁.1 with ⟨x₁, _, hx₁⟩
    rcases Finset.mem_image.mp hq₁.2.1 with ⟨y₁, _, hy₁⟩
    rcases Finset.mem_image.mp hq₂.1 with ⟨x₂, _, hx₂⟩
    rcases Finset.mem_image.mp hq₂.2.1 with ⟨y₂, _, hy₂⟩
    rw [← hx₁, ← hy₁, ← hx₂, ← hy₂] at heq
    have hxy₁ : x₁ ≠ y₁ := fun h => hq₁.2.2 (by rw [← hx₁, ← hy₁, h])
    have hd1 := hg_diff x₁ y₁
    have hd2 := hg_diff x₂ y₂
    rw [heq] at hd1
    have hprod :
        (θ + algebraMap (ZMod p) K x₁) * (θ + algebraMap (ZMod p) K y₂) =
        (θ + algebraMap (ZMod p) K x₂) * (θ + algebraMap (ZMod p) K y₁) := by
      have hgne : (g : K) ^ ((a x₂ + M - a y₂) % M) ≠ 0 := by
        have := (g ^ ((a x₂ + M - a y₂) % M)).ne_zero
        simpa [Units.val_pow_eq_pow_val] using this
      linear_combination -(θ + algebraMap (ZMod p) K y₂) * hd1 +
        (θ + algebraMap (ZMod p) K y₁) * hd2
    have hlin : algebraMap (ZMod p) K (x₁ + y₂ - (x₂ + y₁)) * θ =
        algebraMap (ZMod p) K (x₂ * y₁ - x₁ * y₂) := by
      rw [map_sub, map_add, map_add, map_sub, map_mul, map_mul]
      linear_combination hprod
    have hsum_eq : x₁ + y₂ = x₂ + y₁ := by
      by_contra hne
      have hdiff_ne : x₁ + y₂ - (x₂ + y₁) ≠ 0 := sub_ne_zero.mpr hne
      apply hθ
      refine ⟨(x₂ * y₁ - x₁ * y₂) / (x₁ + y₂ - (x₂ + y₁)), ?_⟩
      rw [map_div₀]
      have hmap_ne : algebraMap (ZMod p) K (x₁ + y₂ - (x₂ + y₁)) ≠ 0 := (map_ne_zero _).mpr hdiff_ne
      rw [div_eq_iff hmap_ne, mul_comm θ, hlin]
    have hmul_eq : x₁ * y₂ = x₂ * y₁ := by
      have h0 : algebraMap (ZMod p) K (x₂ * y₁ - x₁ * y₂) = 0 := by
        rw [← hlin, hsum_eq, sub_self, map_zero, zero_mul]
      exact (sub_eq_zero.mp ((map_eq_zero (algebraMap (ZMod p) K)).mp h0)).symm
    have hquad : (x₁ - x₂) * (x₁ - y₁) = 0 := by
      linear_combination x₁ * hsum_eq - hmul_eq
    rcases mul_eq_zero.mp hquad with hx | hx
    · have hx12 : x₁ = x₂ := sub_eq_zero.mp hx
      have hy12 : y₁ = y₂ := by subst hx12; exact (add_left_cancel hsum_eq).symm
      exact Prod.ext (by rw [← hx₁, ← hx₂, hx12]) (by rw [← hy₁, ← hy₂, hy12])
    · exact False.elim (hxy₁ (sub_eq_zero.mp hx))
  -- Cardinality match proves surjectivity onto `Dset`!
  have hcard_Dset : Dset.card = S.offDiag.card := by
    have hmult : (Finset.range M).filter (fun d => (p + 1) ∣ d) =
        (Finset.range (p - 1)).image (fun k => k * (p + 1)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hdM, k, rfl⟩
        refine ⟨k, ?_, by ring⟩
        rw [hM_eq] at hdM; nlinarith
      · rintro ⟨k, hk, rfl⟩
        refine ⟨?_, k, by ring⟩
        rw [hM_eq]; nlinarith
    have hmult_card : ((Finset.range M).filter (fun d => (p + 1) ∣ d)).card = p - 1 := by
      rw [hmult, Finset.card_image_of_injective _ (fun u v h =>
        Nat.eq_of_mul_eq_mul_right (by omega) h), Finset.card_range]
    have hcomp : ((Finset.range M).filter (fun d => (p + 1) ∣ d)).card + Dset.card = M := by
      have hdisj : Disjoint ((Finset.range M).filter (fun d => (p + 1) ∣ d)) Dset := by
        rw [Finset.disjoint_left]; intro d h1 h2
        rw [Finset.mem_filter] at h1 h2; exact h2.2 h1.2
      have hunion : (Finset.range M).filter (fun d => (p + 1) ∣ d) ∪ Dset = Finset.range M := by
        ext d; simp only [Dset, Finset.mem_union, Finset.mem_filter]; tauto
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
    rw [hmult_card] at hcomp
    have hoff_card : S.offDiag.card = p * p - p := by
      rw [Finset.offDiag_card, hS_card]
    have hM_def : M = p * p - 1 := by dsimp only [M]; ring
    omega
  have hsurj : ∀ d ∈ Dset, ∃ q ∈ S.offDiag, (q.1 + M - q.2) % M = d := by
    have himg_eq : S.offDiag.image (fun q => (q.1 + M - q.2) % M) = Dset := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro d hd; rcases Finset.mem_image.mp hd with ⟨q, hq, rfl⟩; exact hmaps q hq
      · rw [Finset.card_image_of_injOn hinj, hcard_Dset]
    intro d hd
    rw [← himg_eq] at hd
    exact Finset.mem_image.mp hd
  exact ⟨S, hS_sub, hS_card, hmaps, hinj, hsurj⟩

/-- Primitive `M`-th root of unity helper: `ω^k = 1 ↔ M ∣ k`. -/
private lemma rootOfUnity_pow_eq_one_iff {M : ℕ} (hM : 0 < M) (k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))) ^ k = 1 ↔ M ∣ k := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  have h2piI : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  constructor
  · rintro ⟨n, hn⟩
    have hmul : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
        (n : ℂ) * (M : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have := congrArg (· * (M : ℂ)) hn
      have hL : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ)) * (M : ℂ) =
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by field_simp
      rw [hL] at this
      linear_combination this
    have hkC : (k : ℂ) = (n : ℂ) * (M : ℂ) := mul_right_cancel₀ h2piI hmul
    have hkZ : (k : ℤ) = n * (M : ℤ) := by
      have := congrArg Complex.re hkC
      simp only [Complex.natCast_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.natCast_im, mul_zero, sub_zero] at this
      exact_mod_cast this
    have hn_nonneg : 0 ≤ n := by nlinarith
    refine ⟨n.toNat, ?_⟩
    have : (k : ℤ) = (M : ℤ) * (n.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hn_nonneg, mul_comm]; exact hkZ
    exact_mod_cast this
  · rintro ⟨q, rfl⟩
    refine ⟨(q : ℤ), ?_⟩
    push_cast
    field_simp

/-- Exact conjugation & periodicity of `ω = exp(2πi / M)`. -/
private lemma rootOfUnity_conj_mul {M : ℕ} (hM : 0 < M) (ξ a b : ℕ) (ha : a < M) (hb : b < M) :
    let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))
    ω ^ (ξ * a) * starRingEnd ℂ (ω ^ (ξ * b)) = ω ^ (ξ * ((a + M - b) % M)) := by
  intro ω
  have hωM : ω ^ M = 1 := (rootOfUnity_pow_eq_one_iff hM M).mpr (dvd_refl M)
  have hω_ne : ω ≠ 0 := Complex.exp_ne_zero _
  have hconj : starRingEnd ℂ ω = ω⁻¹ := by
    dsimp only [ω]
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  rw [map_pow, hconj, inv_pow]
  have hpow_mod : ∀ n : ℕ, ω ^ n = ω ^ (n % M) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n M]
    rw [pow_add, pow_mul, hωM, one_pow, one_mul]
  have heq_mul : ω ^ (ξ * a) * (ω ^ (ξ * b))⁻¹ = ω ^ (ξ * (a + M - b)) := by
    rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hω_ne), ← pow_add]
    have h1 : ξ * (a + M - b) + ξ * b = ξ * a + M * ξ := by
      have : a + M - b + b = a + M := by omega
      calc ξ * (a + M - b) + ξ * b = ξ * (a + M - b + b) := by ring
        _ = ξ * (a + M) := by rw [this]
        _ = ξ * a + M * ξ := by ring
    rw [h1, pow_add, show ω ^ (M * ξ) = (ω ^ M) ^ ξ by rw [pow_mul], hωM, one_pow, mul_one]
  rw [heq_mul, hpow_mod (ξ * (a + M - b)), hpow_mod (ξ * ((a + M - b) % M))]
  congr 1
  rw [Nat.mul_mod ξ (a + M - b), Nat.mul_mod ξ ((a + M - b) % M), Nat.mod_mod]

/-- Exact Periodic Fourier Flatness of Bose's Sidon Set:
for EVERY prime `p` (`M = p^2 - 1`), Bose's Sidon set `S ⊆ range M` of size `p` satisfies
`‖∑ a ∈ S, exp(2πi ξ a / M)‖^2 = if (p - 1) ∣ ξ then 1 else p` for ALL `1 ≤ ξ < M`
(and hence `≤ p` for all nonzero frequencies `ξ`). -/
theorem bose_periodic_fourier_flatness {p : ℕ} (hp : p.Prime) :
    let M : ℕ := p ^ 2 - 1
    let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))
    ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ S.card = p ∧
      ∀ ξ : ℕ, 1 ≤ ξ → ξ < M →
        ‖∑ a ∈ S, ω ^ (ξ * a)‖ ^ 2 = if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ) := by
  classical
  intro M ω
  have hp2 : 2 ≤ p := hp.two_le
  have hM_eq : M = (p - 1) * (p + 1) := by
    dsimp only [M]
    zify [show 1 ≤ p by omega, show 1 ≤ p ^ 2 by nlinarith]
    ring
  have hM_pos : 0 < M := by dsimp only [M]; exact Nat.sub_pos_of_lt (by nlinarith)
  obtain ⟨S, hS_sub, hS_card, hmaps, hinj, hsurj⟩ := bose_modular_difference_set hp
  refine ⟨S, hS_sub, hS_card, ?_⟩
  intro ξ hξ1 hξM
  let Dset : Finset ℕ := (Finset.range M).filter (fun d => ¬((p + 1) ∣ d))
  let Mset : Finset ℕ := (Finset.range M).filter (fun d => (p + 1) ∣ d)
  -- Express `‖∑ a ∈ S, ω^(ξ*a)‖^2` as the real part of `(∑ a ∈ S, ω^(ξ*a)) * conj(...)`
  have hnorm_re : ‖∑ a ∈ S, ω ^ (ξ * a)‖ ^ 2 =
      ((∑ a ∈ S, ω ^ (ξ * a)) * starRingEnd ℂ (∑ b ∈ S, ω ^ (ξ * b))).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
  rw [hnorm_re]
  -- Expand product and split `S ×ˢ S = S.diag ∪ S.offDiag`
  have hexpand :
      (∑ a ∈ S, ω ^ (ξ * a)) * starRingEnd ℂ (∑ b ∈ S, ω ^ (ξ * b)) =
      (p : ℂ) + ∑ d ∈ Dset, (ω ^ ξ) ^ d := by
    rw [map_sum, Finset.sum_mul]
    have hprod : ∑ a ∈ S, ω ^ (ξ * a) * ∑ b ∈ S, starRingEnd ℂ (ω ^ (ξ * b)) =
        ∑ q ∈ S ×ˢ S, ω ^ (ξ * ((q.1 + M - q.2) % M)) := by
      rw [Finset.sum_product' (s := S) (t := S) (f := fun a b => ω ^ (ξ * ((a + M - b) % M)))]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      exact rootOfUnity_conj_mul hM_pos ξ a b
        (Finset.mem_range.mp (hS_sub ha)) (Finset.mem_range.mp (hS_sub hb))
    rw [hprod, ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag S)]
    congr 1
    · -- Diagonal `a = b` gives `S.card = p`
      have hdiag : ∀ q ∈ S.diag, ω ^ (ξ * ((q.1 + M - q.2) % M)) = 1 := by
        intro q hq
        rw [Finset.mem_diag] at hq
        rw [hq.2, show q.2 + M - q.2 = M by omega, Nat.mod_self, mul_zero, pow_zero]
      rw [Finset.sum_congr rfl hdiag, Finset.sum_const, Finset.diag_card, hS_card, nsmul_eq_mul,
        mul_one]
    · -- Off-diagonal bijects onto `Dset`
      refine Finset.sum_nbij (fun q => (q.1 + M - q.2) % M) ?_ ?_ ?_ ?_
      · intro q hq; exact hmaps q (Finset.mem_coe.mp hq)
      · exact hinj
      · intro d hd
        obtain ⟨q, hq, hqd⟩ := hsurj d (Finset.mem_coe.mp hd)
        exact ⟨q, Finset.mem_coe.mpr hq, hqd⟩
      · intro q _; rw [pow_mul]
  rw [hexpand]
  -- Evaluate `∑ d ∈ Dset, (ω ^ ξ) ^ d = - ∑ d ∈ Mset, (ω ^ ξ) ^ d`
  have hωξ_ne : ω ^ ξ ≠ 1 := by
    intro h1
    have hdvd := (rootOfUnity_pow_eq_one_iff hM_pos ξ).mp h1
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hsum_all : ∑ d ∈ Finset.range M, (ω ^ ξ) ^ d = 0 := by
    rw [geom_sum_eq hωξ_ne, ← pow_mul, mul_comm, pow_mul,
      (rootOfUnity_pow_eq_one_iff hM_pos M).mpr (dvd_refl M), one_pow, sub_self, zero_div]
  have hD_plus_M : ∑ d ∈ Mset, (ω ^ ξ) ^ d + ∑ d ∈ Dset, (ω ^ ξ) ^ d =
      ∑ d ∈ Finset.range M, (ω ^ ξ) ^ d :=
    Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun d => (p + 1) ∣ d) _
  have hD_eq : ∑ d ∈ Dset, (ω ^ ξ) ^ d = - ∑ d ∈ Mset, (ω ^ ξ) ^ d := by
    linear_combination hD_plus_M + hsum_all
  rw [hD_eq]
  -- Rewrite `∑ d ∈ Mset, (ω ^ ξ) ^ d` as geometric sum `∑ k ∈ range (p - 1), (ω ^ (ξ * (p + 1))) ^ k`
  have hMset_eq : Mset = (Finset.range (p - 1)).image (fun k => k * (p + 1)) := by
    ext d; simp only [Mset, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hdM, k, rfl⟩; refine ⟨k, ?_, by ring⟩; rw [hM_eq] at hdM; nlinarith
    · rintro ⟨k, hk, rfl⟩; refine ⟨?_, k, by ring⟩; rw [hM_eq]; nlinarith
  have hMsum : ∑ d ∈ Mset, (ω ^ ξ) ^ d =
      ∑ k ∈ Finset.range (p - 1), (ω ^ (ξ * (p + 1))) ^ k := by
    rw [hMset_eq, Finset.sum_image (fun u _ v _ h =>
      Nat.eq_of_mul_eq_mul_right (by omega) h)]
    refine Finset.sum_congr rfl fun k _ => by rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [hMsum]
  by_cases hdvd : (p - 1) ∣ ξ
  · rw [if_pos hdvd]
    have hzeta1 : ω ^ (ξ * (p + 1)) = 1 := by
      rw [rootOfUnity_pow_eq_one_iff hM_pos]
      rcases hdvd with ⟨q, rfl⟩
      exact ⟨q, by rw [hM_eq]; ring⟩
    have hgeom : ∑ k ∈ Finset.range (p - 1), (ω ^ (ξ * (p + 1))) ^ k = ((p - 1 : ℕ) : ℂ) := by
      simp [hzeta1]
    rw [hgeom]
    have hp1 : 1 ≤ p := by omega
    rw [Complex.add_re, Complex.neg_re, Complex.natCast_re, Complex.natCast_re,
      Nat.cast_sub hp1, Nat.cast_one]
    ring
  · rw [if_neg hdvd]
    have hzeta_ne : ω ^ (ξ * (p + 1)) ≠ 1 := by
      intro h1
      have hMdvd := (rootOfUnity_pow_eq_one_iff hM_pos _).mp h1
      rw [hM_eq] at hMdvd
      exact hdvd ((mul_dvd_mul_iff_right (by omega : p + 1 ≠ 0)).mp hMdvd)
    have hgeom : ∑ k ∈ Finset.range (p - 1), (ω ^ (ξ * (p + 1))) ^ k = 0 := by
      rw [geom_sum_eq hzeta_ne, ← pow_mul,
        show ξ * (p + 1) * (p - 1) = M * ξ by rw [hM_eq]; ring,
        pow_mul, (rootOfUnity_pow_eq_one_iff hM_pos M).mpr (dvd_refl M),
        one_pow, sub_self, zero_div]
    rw [hgeom, neg_zero, add_zero, Complex.natCast_re]

/-- Exact 3-AP-Free Superset Barrier Theorem for Bose's Sidon Set:
for EVERY prime `p` (`M = p^2 - 1`), Bose's Sidon set `S ⊆ range M` of size `p` satisfies:
any subset `T ⊆ range M` forming zero modular 3-APs `t₁ + t₂ ≡ 2 * a (mod M)` (`t₁, t₂ ∈ T, a ∈ S`)
has cardinality `(T.card : ℝ) ≤ (M : ℝ) / Real.sqrt (p : ℝ)` (density `≤ 1 / √p ≈ M^(-1/4)`). -/
theorem bose_3ap_free_superset_bound {p : ℕ} (hp : p.Prime) :
    let M := p ^ 2 - 1
    ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ S.card = p ∧
      ∀ T : Finset ℕ, T ⊆ Finset.range M →
        (∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ a ∈ S, (t₁ + t₂) % M ≠ (2 * a) % M) →
        (T.card : ℝ) ≤ (M : ℝ) / Real.sqrt (p : ℝ) := by
  classical
  intro M
  have hp2 : 2 ≤ p := hp.two_le
  have hM_pos : 0 < M := by dsimp only [M]; exact Nat.sub_pos_of_lt (by nlinarith)
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (M : ℂ))
  obtain ⟨S, hS_sub, hS_card, hflat⟩ := bose_periodic_fourier_flatness hp
  refine ⟨S, hS_sub, hS_card, ?_⟩
  intro T hT_sub hno3ap
  by_cases hT0 : T.card = 0
  · rw [hT0, Nat.cast_zero]; positivity
  have hTpos : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT0)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hsqrtp_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp_pos
  have hωM : ω ^ M = 1 := (rootOfUnity_pow_eq_one_iff hM_pos M).mpr (dvd_refl M)
  have hω_ne : ω ≠ 0 := Complex.exp_ne_zero _
  have hconj : starRingEnd ℂ ω = ω⁻¹ := by
    dsimp only [ω]
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  -- Helper: orthogonality `∑ ξ ∈ range M, ω ^ (ξ * k) = if M ∣ k then M else 0`
  have hortho : ∀ k : ℕ, ∑ ξ ∈ Finset.range M, ω ^ (ξ * k) = if M ∣ k then (M : ℂ) else 0 := by
    intro k
    have hpow : ∀ ξ : ℕ, ω ^ (ξ * k) = (ω ^ k) ^ ξ := fun ξ => by rw [mul_comm, pow_mul]
    rw [Finset.sum_congr rfl fun ξ _ => hpow ξ]
    by_cases hk : M ∣ k
    · rw [if_pos hk, (rootOfUnity_pow_eq_one_iff hM_pos k).mpr hk]
      simp
    · rw [if_neg hk]
      have hne : ω ^ k ≠ 1 := fun h => hk ((rootOfUnity_pow_eq_one_iff hM_pos k).mp h)
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hωM, one_pow, sub_self, zero_div]
  -- 1. Parseval on `T`: `∑ ξ ∈ range M, ‖∑ t ∈ T, ω^(ξ*t)‖^2 = M * T.card`
  have hparseval : ∑ ξ ∈ Finset.range M, ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 = (M : ℝ) * (T.card : ℝ) := by
    have hre : ∑ ξ ∈ Finset.range M, ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 =
        (∑ ξ ∈ Finset.range M, (∑ t ∈ T, ω ^ (ξ * t)) * starRingEnd ℂ (∑ u ∈ T, ω ^ (ξ * u))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
    rw [hre]
    have hsumC : ∑ ξ ∈ Finset.range M,
        (∑ t ∈ T, ω ^ (ξ * t)) * starRingEnd ℂ (∑ u ∈ T, ω ^ (ξ * u)) =
        (M : ℂ) * (T.card : ℂ) := by
      have hexp : ∑ ξ ∈ Finset.range M,
          (∑ t ∈ T, ω ^ (ξ * t)) * starRingEnd ℂ (∑ u ∈ T, ω ^ (ξ * u)) =
          ∑ t ∈ T, ∑ u ∈ T, ∑ ξ ∈ Finset.range M, ω ^ (ξ * ((t + M - u) % M)) := by
        have h1 : ∀ ξ ∈ Finset.range M,
            (∑ t ∈ T, ω ^ (ξ * t)) * starRingEnd ℂ (∑ u ∈ T, ω ^ (ξ * u)) =
            ∑ t ∈ T, ∑ u ∈ T, ω ^ (ξ * ((t + M - u) % M)) := by
          intro ξ _
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u hu => ?_
          exact rootOfUnity_conj_mul hM_pos ξ t u
            (Finset.mem_range.mp (hT_sub ht)) (Finset.mem_range.mp (hT_sub hu))
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_comm
      rw [hexp]
      have hinner : ∀ t ∈ T, ∑ u ∈ T, ∑ ξ ∈ Finset.range M, ω ^ (ξ * ((t + M - u) % M)) = (M : ℂ) := by
        intro t ht
        have htM := Finset.mem_range.mp (hT_sub ht)
        rw [Finset.sum_eq_single t]
        · rw [show t + M - t = M by omega, Nat.mod_self, hortho 0, if_pos (dvd_zero M)]
        · intro u hu hut
          have huM := Finset.mem_range.mp (hT_sub hu)
          rw [hortho, if_neg]
          intro hdvd
          have hmod0 : (t + M - u) % M = 0 := by
            have hlt : (t + M - u) % M < M := Nat.mod_lt _ hM_pos
            exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
          have h1 : M ∣ (t + M - u) := Nat.dvd_of_mod_eq_zero hmod0
          rcases h1 with ⟨q, hq⟩
          have hq1 : q = 1 := by
            by_contra hqne
            rcases lt_or_gt_of_ne hqne with hlt | hgt
            · have : q = 0 := by omega
              subst this; omega
            · have : 2 ≤ q := by omega
              have : 2 * M ≤ M * q := by nlinarith
              omega
          subst hq1
          omega
        · intro ht'; exact False.elim (ht' ht)
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hsumC]
    simp
  -- 2. Exact 3-AP Fourier counting identity = 0
  let F : ℕ → ℂ := fun ξ =>
    (∑ t ∈ T, ω ^ (ξ * t)) ^ 2 * starRingEnd ℂ (∑ a ∈ S, ω ^ (ξ * (2 * a)))
  have hcount_zero : ∑ ξ ∈ Finset.range M, F ξ = 0 := by
    have hF_exp : ∀ ξ ∈ Finset.range M,
        F ξ = ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ a ∈ S, ω ^ (ξ * ((t₁ + t₂ + 2 * M - 2 * a) % M)) := by
      intro ξ _
      dsimp only [F]
      rw [sq, map_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
      have h1 : (ω ^ (ξ * t₁) * ∑ t₂ ∈ T, ω ^ (ξ * t₂)) *
          ∑ a ∈ S, starRingEnd ℂ (ω ^ (ξ * (2 * a))) =
          ∑ t₂ ∈ T, ∑ a ∈ S, (ω ^ (ξ * t₁) * ω ^ (ξ * t₂)) * starRingEnd ℂ (ω ^ (ξ * (2 * a))) := by
        rw [Finset.mul_sum T (fun t₂ => ω ^ (ξ * t₂)), Finset.sum_mul]
        refine Finset.sum_congr rfl fun t₂ _ => Finset.mul_sum _ _ _
      rw [h1]
      refine Finset.sum_congr rfl fun t₂ ht₂ => Finset.sum_congr rfl fun a ha => ?_
      have haM := Finset.mem_range.mp (hS_sub ha)
      rw [← pow_add, map_pow, hconj, inv_pow]
      have hpow_mod : ∀ n : ℕ, ω ^ n = ω ^ (n % M) := by
        intro n; conv_lhs => rw [← Nat.div_add_mod n M]
        rw [pow_add, pow_mul, hωM, one_pow, one_mul]
      have heq_mul : ω ^ (ξ * t₁ + ξ * t₂) * (ω ^ (ξ * (2 * a)))⁻¹ =
          ω ^ (ξ * (t₁ + t₂ + 2 * M - 2 * a)) := by
        rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hω_ne), ← pow_add]
        have hsub : t₁ + t₂ + 2 * M - 2 * a + 2 * a = t₁ + t₂ + 2 * M := by omega
        have h2 : ξ * (t₁ + t₂ + 2 * M - 2 * a) + ξ * (2 * a) =
            (ξ * t₁ + ξ * t₂) + M * (2 * ξ) := by
          calc ξ * (t₁ + t₂ + 2 * M - 2 * a) + ξ * (2 * a)
              = ξ * (t₁ + t₂ + 2 * M - 2 * a + 2 * a) := by ring
            _ = ξ * (t₁ + t₂ + 2 * M) := by rw [hsub]
            _ = (ξ * t₁ + ξ * t₂) + M * (2 * ξ) := by ring
        rw [h2, pow_add ω (ξ * t₁ + ξ * t₂) (M * (2 * ξ)), pow_mul, hωM, one_pow, mul_one]
      rw [heq_mul, hpow_mod (ξ * (t₁ + t₂ + 2 * M - 2 * a)),
        hpow_mod (ξ * ((t₁ + t₂ + 2 * M - 2 * a) % M))]
      congr 1
      rw [Nat.mul_mod ξ (t₁ + t₂ + 2 * M - 2 * a),
        Nat.mul_mod ξ ((t₁ + t₂ + 2 * M - 2 * a) % M), Nat.mod_mod]
    rw [Finset.sum_congr rfl hF_exp, Finset.sum_comm]
    refine Finset.sum_eq_zero fun t₁ ht₁ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t₂ ht₂ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hortho, if_neg]
    intro hdvd
    have hha := Finset.mem_range.mp (hS_sub ha)
    have hmod0 : (t₁ + t₂ + 2 * M - 2 * a) % M = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hM_pos)
    have h1 : t₁ + t₂ + 2 * M = (t₁ + t₂ + 2 * M - 2 * a) + 2 * a := by omega
    have h2 := congrArg (· % M) h1
    conv_rhs at h2 => rw [Nat.add_mod, hmod0, zero_add, Nat.mod_mod]
    have h3 : (t₁ + t₂ + 2 * M) % M = (t₁ + t₂) % M := by
      rw [Nat.add_mul_mod_self_right]
    rw [h3] at h2
    exact hno3ap t₁ ht₁ t₂ ht₂ a ha h2
  -- 3. Split frequencies into `Z = {ξ < M | M ∣ 2 * ξ}` (real & nonneg, containing `0`) and `NZ`
  let Z : Finset ℕ := (Finset.range M).filter (fun ξ => M ∣ 2 * ξ)
  let NZ : Finset ℕ := (Finset.range M).filter (fun ξ => ¬(M ∣ 2 * ξ))
  have hsplit_re : ∑ ξ ∈ Z, (F ξ).re + ∑ ξ ∈ NZ, (F ξ).re = 0 := by
    rw [← Complex.re_sum, ← Complex.re_sum, ← Complex.add_re,
      Finset.sum_filter_add_sum_filter_not, hcount_zero, Complex.zero_re]
  -- On `Z`, `(F ξ).re ≥ 0`, and at `ξ = 0`, `(F 0).re = p * T.card^2`
  have hZ_ge : (p : ℝ) * (T.card : ℝ) ^ 2 ≤ ∑ ξ ∈ Z, (F ξ).re := by
    have h0mem : 0 ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hM_pos, by simp⟩
    have h0val : (F 0).re = (p : ℝ) * (T.card : ℝ) ^ 2 := by
      dsimp only [F]
      simp [hS_card, sq]
      ring
    have hZ_nn : ∀ ξ ∈ Z, 0 ≤ (F ξ).re := by
      intro ξ hξ
      rw [Finset.mem_filter] at hξ
      have hω2ξ : ω ^ (2 * ξ) = 1 := (rootOfUnity_pow_eq_one_iff hM_pos _).mpr hξ.2
      have hSval : ∑ a ∈ S, ω ^ (ξ * (2 * a)) = (p : ℂ) := by
        have : ∀ a ∈ S, ω ^ (ξ * (2 * a)) = 1 := fun a _ => by
          rw [show ξ * (2 * a) = (2 * ξ) * a by ring, pow_mul, hω2ξ, one_pow]
        rw [Finset.sum_congr rfl this, Finset.sum_const, hS_card, nsmul_eq_mul, mul_one]
      have hreal_ωξ : (ω ^ ξ).im = 0 := by
        have hsq : (ω ^ ξ) ^ 2 = 1 := by rw [← pow_mul, mul_comm, hω2ξ]
        have hfac : (ω ^ ξ - 1) * (ω ^ ξ + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.mp hfac with h1 | h1
        · have : ω ^ ξ = 1 := sub_eq_zero.mp h1; rw [this, Complex.one_im]
        · have : ω ^ ξ = -1 := eq_neg_of_add_eq_zero_left h1; rw [this, Complex.neg_im, Complex.one_im, neg_zero]
      have hreal_sum : (∑ t ∈ T, ω ^ (ξ * t)).im = 0 := by
        rw [Complex.im_sum]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [pow_mul]
        have him0 : ∀ n : ℕ, ((ω ^ ξ) ^ n).im = 0 := by
          intro n; induction n with
          | zero => simp
          | succ n ih => simp [pow_succ, Complex.mul_im, ih, hreal_ωξ]
        exact him0 t
      dsimp only [F]
      rw [hSval, map_natCast, sq, Complex.mul_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, hreal_sum]
      nlinarith
    calc (p : ℝ) * (T.card : ℝ) ^ 2 = (F 0).re := h0val.symm
      _ ≤ ∑ ξ ∈ Z, (F ξ).re := Finset.single_le_sum hZ_nn h0mem
  -- On `NZ`, `|(F ξ).re| ≤ ‖∑ t ∈ T, ω^(ξ*t)‖^2 * √p`
  have hNZ_bound : -(∑ ξ ∈ NZ, (F ξ).re) ≤ (M : ℝ) * (T.card : ℝ) * Real.sqrt (p : ℝ) := by
    calc -(∑ ξ ∈ NZ, (F ξ).re)
        ≤ |∑ ξ ∈ NZ, (F ξ).re| := neg_le_abs _
      _ ≤ ∑ ξ ∈ NZ, |(F ξ).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ξ ∈ NZ, ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 * Real.sqrt (p : ℝ) := by
          refine Finset.sum_le_sum fun ξ hξ => ?_
          rw [Finset.mem_filter, Finset.mem_range] at hξ
          have hre_le : |(F ξ).re| ≤ ‖F ξ‖ := Complex.abs_re_le_norm (F ξ)
          have hFnorm : ‖F ξ‖ = ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 * ‖∑ a ∈ S, ω ^ (ξ * (2 * a))‖ := by
            dsimp only [F]
            rw [norm_mul, norm_pow, Complex.norm_conj]
          have hmod_pos : 1 ≤ (2 * ξ) % M := by
            by_contra h0; push Not at h0
            have : (2 * ξ) % M = 0 := by omega
            exact hξ.2 (Nat.dvd_of_mod_eq_zero this)
          have hmod_lt : (2 * ξ) % M < M := Nat.mod_lt _ hM_pos
          have hS_congr : ∑ a ∈ S, ω ^ (ξ * (2 * a)) = ∑ a ∈ S, ω ^ (((2 * ξ) % M) * a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            have hpow_mod : ∀ n : ℕ, ω ^ n = ω ^ (n % M) := by
              intro n; conv_lhs => rw [← Nat.div_add_mod n M]
              rw [pow_add, pow_mul, hωM, one_pow, one_mul]
            rw [show ξ * (2 * a) = (2 * ξ) * a by ring, hpow_mod ((2 * ξ) * a),
              hpow_mod (((2 * ξ) % M) * a)]
            congr 1
            rw [Nat.mul_mod (2 * ξ) a, Nat.mul_mod ((2 * ξ) % M) a, Nat.mod_mod]
          have hS_sq : ‖∑ a ∈ S, ω ^ (ξ * (2 * a))‖ ^ 2 ≤ (p : ℝ) := by
            rw [hS_congr, hflat ((2 * ξ) % M) hmod_pos hmod_lt]
            split_ifs
            · exact_mod_cast (show 1 ≤ p by omega)
            · exact le_refl _
          have hS_le : ‖∑ a ∈ S, ω ^ (ξ * (2 * a))‖ ≤ Real.sqrt (p : ℝ) := by
            have := Real.sqrt_le_sqrt hS_sq
            rwa [Real.sqrt_sq (norm_nonneg _)] at this
          calc |(F ξ).re| ≤ ‖F ξ‖ := hre_le
            _ = ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 * ‖∑ a ∈ S, ω ^ (ξ * (2 * a))‖ := hFnorm
            _ ≤ ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2 * Real.sqrt (p : ℝ) :=
                mul_le_mul_of_nonneg_left hS_le (sq_nonneg _)
      _ = (∑ ξ ∈ NZ, ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2) * Real.sqrt (p : ℝ) := (Finset.sum_mul ..).symm
      _ ≤ (∑ ξ ∈ Finset.range M, ‖∑ t ∈ T, ω ^ (ξ * t)‖ ^ 2) * Real.sqrt (p : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _)
            hsqrtp_pos.le
      _ = (M : ℝ) * (T.card : ℝ) * Real.sqrt (p : ℝ) := by rw [hparseval]
  have hmain : (p : ℝ) * (T.card : ℝ) ^ 2 ≤ (M : ℝ) * (T.card : ℝ) * Real.sqrt (p : ℝ) := by
    linarith
  rw [le_div_iff₀ hsqrtp_pos]
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt hp_pos.le
  nlinarith

/-! ### Section 10: Asymptotic Exact Pointwise Fractional & Degree-1 Lasserre SDP Barrier -/

/-- Explicit Asymptotic Exact Pointwise Fractional & Degree-1 Lasserre SDP + BQP + 3-AP + 4-Sidon
Barrier Theorem:
for EVERY prime `p ≥ 10000` (`M = p^2 - 1`), there exist `μ : ℕ → ℝ` and `X : ℕ → ℕ → ℝ`
satisfying:
1. `IsFractionalSidon M μ` (with zero clipping: `0 ≤ μ i ≤ 1 / √3` everywhere),
2. `IsSDP1Feasible M μ X` (full Shor + RLT + McCormick + exact pointwise Sidon constraints),
3. all Boolean Quadric Polytope (BQP) triangle inequalities `X i j + X i k - X j k ≤ μ i`,
4. all `Θ(M^2)` exact 3-AP linear cuts `X a b + X b c + X a c ≤ 1`,
5. all `Θ(M^3)` exact 4-tuple Sidon linear cuts `X a b + X a c + X a e + X b c + X b e + X c e ≤ 3`,
6. objective `∑_{i < M} μ i ≥ p + (1 / 250) * √p > √M + (1 / 250) * M^(1/4)`. -/
theorem asymptotic_fractional_sdp1_barrier_explicit {p : ℕ} (hp : p.Prime) (hp10k : 10000 ≤ p) :
    let M : ℕ := p ^ 2 - 1
    ∃ (μ : ℕ → ℝ) (X : ℕ → ℕ → ℝ),
      IsFractionalSidon M μ ∧
      IsSDP1Feasible M μ X ∧
      (∀ i, i < M → ∀ j, j < M → ∀ k, k < M → i ≠ j → i ≠ k → j ≠ k →
        X i j + X i k - X j k ≤ μ i) ∧
      (∀ a b c, a < b → b < c → c < M → a + c = 2 * b →
        X a b + X b c + X a c ≤ 1) ∧
      (∀ a b c e, a < b → b < c → c < e → e < M → a + e = b + c →
        X a b + X a c + X a e + X b c + X b e + X c e ≤ 3) ∧
      (p : ℝ) + (1 / 250 : ℝ) * Real.sqrt (p : ℝ) ≤ ∑ i ∈ Finset.range M, μ i ∧
      Real.sqrt (M : ℝ) + (1 / 250 : ℝ) * (M : ℝ) ^ (4⁻¹ : ℝ) < ∑ i ∈ Finset.range M, μ i := by
  intro M
  obtain ⟨S, hS_sub, hS_card, hflat⟩ := bose_periodic_fourier_flatness hp
  obtain ⟨μ, hμ_cap, hμ_ac, hμ_mass⟩ :=
    smooth_bump_periodic_barrier_of_bose_flat hp hp10k hS_sub hS_card hflat
  have h1_div_sqrt3_le_one : (1 : ℝ) / Real.sqrt 3 ≤ 1 := by
    rw [div_le_one (Real.sqrt_pos.mpr (by norm_num))]
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    exact h1
  have hμ_frac : IsFractionalSidon M μ :=
    ⟨fun x hx => ⟨(hμ_cap x hx).1, (hμ_cap x hx).2.trans h1_div_sqrt3_le_one⟩, hμ_ac⟩
  obtain ⟨hSDP1, hBQP⟩ := shor_rlt_sdp1_lift hμ_frac
  obtain ⟨_, h3AP, h4Sidon⟩ :=
    shor_rlt_sdp1_lift_3ap_4sidon_cuts hμ_frac (fun i hi => (hμ_cap i hi).2)
  have hM_lt_p2 : (M : ℝ) < (p : ℝ) ^ 2 := by
    dsimp only [M]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p ^ 2), Nat.cast_pow, Nat.cast_one]
    linarith
  have hM_posR : (0 : ℝ) < (M : ℝ) := by
    dsimp only [M]
    have : 10000 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp10k 2
    exact_mod_cast (show 0 < p ^ 2 - 1 by omega)
  have hsqrtM_lt_p : Real.sqrt (M : ℝ) < (p : ℝ) := by
    have h1 := Real.sqrt_lt_sqrt hM_posR.le hM_lt_p2
    rwa [Real.sqrt_sq (Nat.cast_nonneg p)] at h1
  have hM14_lt_sqrtp : (M : ℝ) ^ (4⁻¹ : ℝ) < Real.sqrt (p : ℝ) := by
    have hsq1 : ((M : ℝ) ^ (4⁻¹ : ℝ)) ^ 2 = Real.sqrt (M : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hM_posR.le]
      norm_num
    have hsq2 : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
    have hnn1 : 0 ≤ (M : ℝ) ^ (4⁻¹ : ℝ) := Real.rpow_nonneg hM_posR.le _
    have hnn2 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
    nlinarith
  exact ⟨μ, (fun i j => if i = j then μ i else μ i * μ j),
    hμ_frac, hSDP1, hBQP, h3AP, h4Sidon, hμ_mass, by linarith⟩

/-- Asymptotic `atTop` formulation of the Exact Pointwise Fractional & Degree-1 Lasserre
SDP + BQP + 3-AP + 4-Sidon Barrier Theorem:
`∃ c₀ > 0, ∀ᶠ p in atTop, p.Prime → ...` with excess `≥ c₀ * M^(1/4)`. -/
theorem asymptotic_fractional_sdp1_barrier :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      let M : ℕ := p ^ 2 - 1
      ∃ (μ : ℕ → ℝ) (X : ℕ → ℕ → ℝ),
        IsFractionalSidon M μ ∧
        IsSDP1Feasible M μ X ∧
        (∀ i, i < M → ∀ j, j < M → ∀ k, k < M → i ≠ j → i ≠ k → j ≠ k →
          X i j + X i k - X j k ≤ μ i) ∧
        (∀ a b c, a < b → b < c → c < M → a + c = 2 * b →
          X a b + X b c + X a c ≤ 1) ∧
        (∀ a b c e, a < b → b < c → c < e → e < M → a + e = b + c →
          X a b + X a c + X a e + X b c + X b e + X c e ≤ 3) ∧
        Real.sqrt (M : ℝ) + c₀ * (M : ℝ) ^ (4⁻¹ : ℝ) ≤ ∑ i ∈ Finset.range M, μ i := by
  refine ⟨1 / 250, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 10000] with p hp10k hp
  obtain ⟨μ, X, h1, h2, h3, h4, h5, _, hstrict⟩ :=
    asymptotic_fractional_sdp1_barrier_explicit hp hp10k
  exact ⟨μ, X, h1, h2, h3, h4, h5, hstrict.le⟩

/-! ### Section 11: Degree-2 Lasserre Hierarchy Projection & Frontier Upper Bound -/

/-- Exact projection of Degree-2 Lasserre onto Degree-1 Lasserre (`IsSDP1Feasible`) plus all
`Θ(N^2)` exact 3-AP cuts and all `Θ(N^3)` pairwise & 6-edge 4-Sidon cuts. -/
theorem lasserre2_implies_sdp1_with_cuts {N : ℕ} {y : Finset ℕ → ℝ}
    (hy : IsLasserre2Feasible N y) :
    let x : ℕ → ℝ := fun i => y {i}
    let X : ℕ → ℕ → ℝ := fun i j => y {i, j}
    IsSDP1Feasible N x X ∧
    (∀ a b c, a < b → b < c → c < N → a + c = 2 * b →
      X a b + X b c + X a c ≤ 1) ∧
    (∀ a b c e, a < b → b < c → c < e → e < N → a + e = b + c →
      X a b + X c e ≤ 1 ∧ X a c + X b e ≤ 1 ∧ X a e + X b c ≤ 1 ∧
      X a b + X a c + X a e + X b c + X b e + X c e ≤ 3) := by
  intro x X
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i _ j _; dsimp only [X]; rw [Finset.pair_comm]
  · exact lasserre2_psd1 hy
  · intro i _; dsimp only [X, x]; rw [Finset.pair_eq_singleton]
  · intro i hi j hj; exact lasserre2_mccormick hy hi hj
  · intro d hd1 hdN; exact lasserre2_sidon_offdiag hy hd1 hdN
  · intro a b c hab hbc hcN hap; exact lasserre2_3ap_cut hy hab hbc hcN hap
  · intro a b c e hab hbc hce heN hsid4; exact lasserre2_4sidon_cuts hy hab hbc hce heN hsid4

/-- Frontier upper bound for the Degree-2 Lasserre hierarchy:
for all sufficiently large `N`, EVERY `IsLasserre2Feasible N y` satisfies
`∑_{i < N} y {i} ≤ √N + 0.94295 * N^(1/4)`. -/
theorem lasserre2_sub_094295 :
    ∀ᶠ N : ℕ in atTop, ∀ y : Finset ℕ → ℝ,
      IsLasserre2Feasible N y →
      ∑ i ∈ Finset.range N, y {i} ≤ Real.sqrt (N : ℝ) + (0.94295 : ℝ) * (N : ℝ) ^ (4⁻¹ : ℝ) := by
  filter_upwards [sdp1_sub_094295] with N hN y hy
  exact hN (fun i => y {i}) (fun i j => y {i, j}) (lasserre2_implies_sdp1_with_cuts hy).1

/-! ### Section 12: Track 2 — `M_3AP(11)` Separation, Exact Mod-`q` Equidistribution, & Universal `O(N^(11/12))` Support Bound -/

/-- Theorem T2-C (Strict Nonlinear `M_3AP` Separation at `N = 11`):
`h(11) = 4 < 3√2`, yet there exist `μ` and `X` satisfying `IsFractionalSidon 11 μ`,
`IsSDP1Feasible 11 μ X`, and strict 3-AP-freeness `Is3APFreeMeasure 11 μ` with
`∑_{x < 11} μ x = 3√2`. -/
theorem strict_separation_h11_lt_m3ap :
    h 11 = 4 ∧ (h 11 : ℝ) < 3 * Real.sqrt 2 ∧
    ∃ (μ : ℕ → ℝ) (X : ℕ → ℕ → ℝ),
      IsFractionalSidon 11 μ ∧
      IsSDP1Feasible 11 μ X ∧
      Is3APFreeMeasure 11 μ ∧
      ∑ x ∈ Finset.range 11, μ x = 3 * Real.sqrt 2 := by
  obtain ⟨hh11, hlt, μ, hbox, hac, h3ap, hsum⟩ := strict_separation_h11_lt_m3ap_core
  have hfrac : IsFractionalSidon 11 μ := ⟨hbox, hac⟩
  obtain ⟨hSDP1, _⟩ := shor_rlt_sdp1_lift hfrac
  exact ⟨hh11, hlt, μ, (fun i j => if i = j then μ i else μ i * μ j), hfrac, hSDP1, h3ap, hsum⟩

/-- Theorem T2-A (Exact Mod-`q` Equidistribution for `IsFractionalSidon`):
For all `N, q, m ≥ 1`, setting `S_r = ∑_{y < N, y % q = r} μ y`,
`q * ∑_{r < q} S_r^2 ≤ (N + m * q - 1) * (1 + (‖μ‖_2^2 - 1) / m)`. -/
theorem fractional_sidon_mod_q_equidistribution {N q m : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hm : 1 ≤ m) {μ : ℕ → ℝ} (hμ : IsFractionalSidon N μ) :
    (q : ℝ) * ∑ r ∈ Finset.range q,
        (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 ≤
      ((N + m * q - 1 : ℕ) : ℝ) *
        (1 + ((∑ y ∈ Finset.range N, (μ y) ^ 2) - 1) / (m : ℝ)) := by
  refine matrix_mod_q_equidistribution hN hq hm
    (X := fun i j => μ i * μ j) (E := ∑ y ∈ Finset.range N, (μ y) ^ 2) ?_ ?_ ?_ ?_
  · intro i _ j _; ring
  · refine le_of_eq (Finset.sum_congr rfl fun i _ => (sq (μ i)).symm)
  · exact hμ.2
  · intro r _ x _
    rw [sq, Finset.sum_mul]
    refine le_of_eq (Finset.sum_congr rfl fun y _ => Finset.mul_sum _ _ _)

/-- Theorem T2-A (Exact Mod-`q` Equidistribution for `IsSDP1Feasible`, with `‖μ‖_1` diagonal):
For all `N, q, m ≥ 1`, setting `S_r = ∑_{y < N, y % q = r} μ y`,
`q * ∑_{r < q} S_r^2 ≤ (N + m * q - 1) * (1 + (‖μ‖_1 - 1) / m)`. -/
theorem sdp1_mod_q_equidistribution {N q m : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hm : 1 ≤ m)
    {μ : ℕ → ℝ} {X : ℕ → ℕ → ℝ} (hSDP : IsSDP1Feasible N μ X) :
    (q : ℝ) * ∑ r ∈ Finset.range q,
        (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 ≤
      ((N + m * q - 1 : ℕ) : ℝ) *
        (1 + ((∑ y ∈ Finset.range N, μ y) - 1) / (m : ℝ)) := by
  classical
  rcases hSDP with ⟨hSymm, hPSD, hDiag, _, hOff⟩
  refine matrix_mod_q_equidistribution hN hq hm
    (X := X) (E := ∑ y ∈ Finset.range N, μ y) hSymm ?_ hOff ?_
  · exact le_of_eq (Finset.sum_congr rfl fun i hi => hDiag i (Finset.mem_range.mp hi))
  · intro r _ x _
    let W := (Finset.range N).filter (fun y => y % q = r ∧ y ≤ x ∧ x < y + m * q)
    have hWsub : W ⊆ Finset.range N := Finset.filter_subset _ _
    let v : ℕ → ℝ := fun i => if i ∈ W then 1 else 0
    have hlin : ∑ i ∈ Finset.range N, v i * μ i = ∑ y ∈ W, μ y := by
      rw [← Finset.sum_subset hWsub]
      · refine Finset.sum_congr rfl fun y hy => by simp [v, hy]
      · intro i _ hi; simp [v, hi]
    have hquad : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, v i * X i j * v j =
        ∑ y ∈ W, ∑ z ∈ W, X y z := by
      rw [← Finset.sum_subset hWsub]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [← Finset.sum_subset hWsub]
        · refine Finset.sum_congr rfl fun z hz => by simp [v, hy, hz]
        · intro j _ hj; simp [v, hj]
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => by simp [v, hi]
    have hpsd := hPSD (-(∑ y ∈ W, μ y)) v
    rw [hlin, hquad] at hpsd
    nlinarith only [hpsd]

/-- Theorem T2-A Corollary (Mod-`q` Residue-Class Collapse for `IsFractionalSidon`):
If `supp(μ)` hits at most `k` residue classes mod `q`, then
`(∑ μ)^2 ≤ (k / q) * (N + m * q - 1) * (1 + (‖μ‖_2^2 - 1) / m)`. -/
theorem fractional_sidon_mod_q_support_collapse {N q m k : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hm : 1 ≤ m) {μ : ℕ → ℝ} (hμ : IsFractionalSidon N μ)
    {R : Finset ℕ} (hR_sub : R ⊆ Finset.range q) (hR_card : R.card ≤ k)
    (hsupp : ∀ y, y < N → y % q ∉ R → μ y = 0) :
    (∑ y ∈ Finset.range N, μ y) ^ 2 ≤
      ((k : ℝ) / (q : ℝ)) * ((N + m * q - 1 : ℕ) : ℝ) *
        (1 + ((∑ y ∈ Finset.range N, (μ y) ^ 2) - 1) / (m : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hcol := mod_q_support_collapse_of_equidist hq hR_sub hR_card hsupp
  have heq := fractional_sidon_mod_q_equidistribution hN hq hm hμ
  have hdiv : ∑ r ∈ Finset.range q, (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 ≤
      (((N + m * q - 1 : ℕ) : ℝ) * (1 + ((∑ y ∈ Finset.range N, (μ y) ^ 2) - 1) / (m : ℝ))) / (q : ℝ) :=
    (le_div_iff₀' hqpos).mpr heq
  have hmul := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg k)
  calc (∑ y ∈ Finset.range N, μ y) ^ 2
      ≤ (k : ℝ) * ∑ r ∈ Finset.range q,
          (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 := hcol
    _ ≤ (k : ℝ) * ((((N + m * q - 1 : ℕ) : ℝ) *
          (1 + ((∑ y ∈ Finset.range N, (μ y) ^ 2) - 1) / (m : ℝ))) / (q : ℝ)) := hmul
    _ = ((k : ℝ) / (q : ℝ)) * ((N + m * q - 1 : ℕ) : ℝ) *
          (1 + ((∑ y ∈ Finset.range N, (μ y) ^ 2) - 1) / (m : ℝ)) := by ring

/-- Theorem T2-A Corollary (Mod-`q` Residue-Class Collapse for `IsSDP1Feasible`):
If `supp(μ)` hits at most `k` residue classes mod `q`, then
`(∑ μ)^2 ≤ (k / q) * (N + m * q - 1) * (1 + (‖μ‖_1 - 1) / m)`. -/
theorem sdp1_mod_q_support_collapse {N q m k : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hm : 1 ≤ m) {μ : ℕ → ℝ} {X : ℕ → ℕ → ℝ} (hSDP : IsSDP1Feasible N μ X)
    {R : Finset ℕ} (hR_sub : R ⊆ Finset.range q) (hR_card : R.card ≤ k)
    (hsupp : ∀ y, y < N → y % q ∉ R → μ y = 0) :
    (∑ y ∈ Finset.range N, μ y) ^ 2 ≤
      ((k : ℝ) / (q : ℝ)) * ((N + m * q - 1 : ℕ) : ℝ) *
        (1 + ((∑ y ∈ Finset.range N, μ y) - 1) / (m : ℝ)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hcol := mod_q_support_collapse_of_equidist hq hR_sub hR_card hsupp
  have heq := sdp1_mod_q_equidistribution hN hq hm hSDP
  have hdiv : ∑ r ∈ Finset.range q, (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 ≤
      (((N + m * q - 1 : ℕ) : ℝ) * (1 + ((∑ y ∈ Finset.range N, μ y) - 1) / (m : ℝ))) / (q : ℝ) :=
    (le_div_iff₀' hqpos).mpr heq
  have hmul := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg k)
  calc (∑ y ∈ Finset.range N, μ y) ^ 2
      ≤ (k : ℝ) * ∑ r ∈ Finset.range q,
          (∑ y ∈ (Finset.range N).filter (fun y => y % q = r), μ y) ^ 2 := hcol
    _ ≤ (k : ℝ) * ((((N + m * q - 1 : ℕ) : ℝ) *
          (1 + ((∑ y ∈ Finset.range N, μ y) - 1) / (m : ℝ))) / (q : ℝ)) := hmul
    _ = ((k : ℝ) / (q : ℝ)) * ((N + m * q - 1 : ℕ) : ℝ) *
          (1 + ((∑ y ∈ Finset.range N, μ y) - 1) / (m : ℝ)) := by ring

/-- Theorem T2-B (Universal Power-Saving `O(N^(11/12))` 3-AP-Free Support Bound):
For every `C₀ : ℝ`, eventually for all `N`, ANY dense fractional Sidon measure `μ` with
`∑ μ ≥ √N - C₀ N^(1/4)` forces EVERY `T ⊆ range N` forming zero nontrivial linear 3-APs
`t₁ + t₂ = 2x` (`t₁ ≠ t₂`, `μ x > 0`) to satisfy `|T| ≤ 66 * N^(11/12)`. -/
theorem universal_3ap_free_superset_bound (C₀ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ : ℕ → ℝ) (T : Finset ℕ),
        IsFractionalSidon N μ →
        Real.sqrt (N : ℝ) - C₀ * (N : ℝ) ^ (4⁻¹ : ℝ) ≤ ∑ x ∈ Finset.range N, μ x →
        T ⊆ Finset.range N →
        (∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ x < N, t₁ ≠ t₂ → t₁ + t₂ = 2 * x → μ x = 0) →
        (T.card : ℝ) ≤ 66 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  filter_upwards [universal_3ap_free_superset_asymptotic C₀] with N hN μ T hμ hdense hT h3ap
  have hdense' : Real.sqrt (N : ℝ) - C₀ * (N : ℝ) ^ (1 / 4 : ℝ) ≤ ∑ x ∈ Finset.range N, μ x := by
    simpa [one_div] using hdense
  exact hN μ T hμ.1 hμ.2 hdense' hT h3ap

/-- Theorem T2-B Corollary (Dense Nonlinear `M_3AP(N)` Support Size Bound):
For every `C₀ : ℝ`, eventually for all `N`, ANY dense feasible witness `μ` of the nonlinear
3-AP-free relaxation `M_3AP(N)` (`IsFractionalSidon N μ ∧ Is3APFreeMeasure N μ` with
`∑ μ ≥ √N - C₀ N^(1/4)`) MUST have support cardinality `|supp(μ)| ≤ 66 * N^(11/12)`
(unconditionally ruling out all Behrend-density supports). -/
theorem m3ap_dense_support_card_bound (C₀ : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ μ : ℕ → ℝ,
        IsFractionalSidon N μ →
        Is3APFreeMeasure N μ →
        Real.sqrt (N : ℝ) - C₀ * (N : ℝ) ^ (4⁻¹ : ℝ) ≤ ∑ x ∈ Finset.range N, μ x →
        (((Finset.range N).filter (fun x => 0 < μ x)).card : ℝ) ≤ 66 * (N : ℝ) ^ (11 / 12 : ℝ) := by
  classical
  filter_upwards [universal_3ap_free_superset_bound C₀] with N hN μ hμ h3ap hdense
  refine hN μ ((Finset.range N).filter (fun x => 0 < μ x)) hμ hdense (Finset.filter_subset _ _) ?_
  intro t₁ ht₁ t₂ ht₂ x hx hne hsum
  have ht₁' := Finset.mem_filter.mp ht₁
  have ht₂' := Finset.mem_filter.mp ht₂
  have ht₁N := Finset.mem_range.mp ht₁'.1
  have ht₂N := Finset.mem_range.mp ht₂'.1
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hzero := h3ap t₁ x t₂ (by omega) (by omega) ht₂N hsum
    have hprod : μ t₁ * μ t₂ > 0 := mul_pos ht₁'.2 ht₂'.2
    nlinarith only [hzero, hprod]
  · have hzero := h3ap t₂ x t₁ (by omega) (by omega) ht₁N (by omega)
    have hprod : μ t₂ * μ t₁ > 0 := mul_pos ht₂'.2 ht₁'.2
    nlinarith only [hzero, hprod]

/-! ### Section 13: Track 3 — Bose Sparse-Background Cross-Variance & Binary-Autocorrelation Rigidity -/

/-- Theorem T3-B (Exact Bose Sparse-Background Parseval Cross-Variance Lower Bound):
For EVERY prime `p` (`M = p^2 - 1`), Bose's periodic Fourier-flat Sidon set `S ⊆ range M`
(`|S| = p`) satisfies, for ANY `IsFractionalSidon M ν`:
1. `V(S, ν) ≥ (p(p-2)/(p-1)) * (‖ν‖_2^2 - 2)`,
2. If `supp(ν) ⊆ T ⊆ range M` (`|T| ≥ 1`), then `V(S, ν) ≥ (p(p-2)/(p-1)) * (‖ν‖_1^2 / |T| - 2)`,
where `V(S, ν) = ∑_{d < M} ((1_S ⋆_cyc ν)(d) - p ‖ν‖_1 / M)^2`. -/
theorem bose_sparse_background_cross_variance {p : ℕ} (hp : p.Prime) :
    let M : ℕ := p ^ 2 - 1
    ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ S.card = p ∧
      (∀ ξ : ℕ, 1 ≤ ξ → ξ < M →
        ‖∑ a ∈ S, (rootOfUnity M) ^ (ξ * a)‖ ^ 2 = if (p - 1) ∣ ξ then (1 : ℝ) else (p : ℝ)) ∧
      ∀ ν : ℕ → ℝ, IsFractionalSidon M ν →
        let indS : ℕ → ℝ := fun x => if x ∈ S then 1 else 0
        let V : ℝ := ∑ d ∈ Finset.range M,
          (cyclicConv M indS ν d - (p : ℝ) * (∑ x ∈ Finset.range M, ν x) / (M : ℝ)) ^ 2
        ((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) * ((∑ x ∈ Finset.range M, (ν x) ^ 2) - 2) ≤ V ∧
        ∀ T : Finset ℕ, T ⊆ Finset.range M → 1 ≤ T.card →
          (∀ x, x < M → x ∉ T → ν x = 0) →
          ((p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1)) *
            ((∑ x ∈ Finset.range M, ν x) ^ 2 / (T.card : ℝ) - 2) ≤ V := by
  intro M
  obtain ⟨S, hS_sub, hS_card, hflat⟩ := bose_periodic_fourier_flatness hp
  refine ⟨S, hS_sub, hS_card, hflat, ?_⟩
  intro ν hν
  exact bose_sparse_background_cross_variance_of_flat hp hS_sub hS_card hflat hν.2

end Erdos030
