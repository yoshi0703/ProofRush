import CanonicalQuantile
import HeadProfileBridge
import RegularHeadPrior
import TestRelabel

open scoped BigOperators
open CanonneDiffuse CanonneNearOneTesting

namespace CanonneHeadEnvelope

variable {H T : Type*} [Fintype H] [Fintype T]

/-- Head profiles in the regular lower bound and in the crossing argument agree exactly. -/
theorem regularHeadProfile_eq_quantile {d : ℕ} {n : ℝ} (order : Fin (d+1) ≃ H)
    {q : H ⊕ T → ℝ} (hq : IsLaw q) (hn : 0 < n)
    (hpos : ∀ i, 0 < q (Sum.inl (order i))) :
    headMass q * headProfile (n*headMass q) (orderedConditional order q) =
      CanonneQuantile.headProfile (fun i : Fin d ↦ (q (Sum.inl (order i.succ)))^((1 : ℝ)/3))
        (cutoffCandidates d) (cutoffCandidates_nonempty d) n := by
  let A := headMass q
  let h := orderedConditional order q
  have hA : 0 < A := by
    refine (hpos 0).trans_le ?_
    exact Finset.single_le_sum (fun i _ ↦ hq.nonneg (Sum.inl i)) (Finset.mem_univ (order 0))
  have hh : ∀ i, 0 ≤ h i := fun i ↦ div_nonneg (hq.nonneg _) hA.le
  rw [← headProfile_scale hn hA hh]
  have he : (fun i ↦ A * h i) = fun i ↦ q (Sum.inl (order i)) := by
    funext i
    change A * (q (Sum.inl (order i)) / A) = _
    field_simp
  rw [he]
  exact headProfile_eq_quantile hn (fun i ↦ hq.nonneg _)

section Relabeling

variable {A B : Type*} [Fintype A] [Fintype B]

theorem goodTest_exists_iff_identity {n : ℕ} {ε : ℝ} (q : A → ℝ) :
    (∃ f, GoodTest q ε n f) ↔ GoodIdentityTest n q ε := by
  constructor
  · rintro ⟨f,hf,hnull,halt⟩
    exact ⟨f,fun i ↦ (hf i).1,fun i ↦ (hf i).2,hnull,
      fun p hp₀ hp₁ hfar ↦ by
        have hh := halt p ⟨hp₀,hp₁⟩ hfar
        change (2 : ℝ)/3 ≤ ∑ x, iidMass n p x * f x at hh
        linarith⟩
  · rintro ⟨f,hf₀,hf₁,hnull,halt⟩
    exact ⟨f,fun i ↦ ⟨hf₀ i,hf₁ i⟩,hnull,
      fun p hp hfar ↦ by
        have hh := halt p hp.nonneg hp.total hfar
        change (2 : ℝ)/3 ≤ ∑ x, iidMass n p x * f x
        linarith⟩

theorem goodTest_exists_equiv (e : B ≃ A) (q : A → ℝ) (n : ℕ) (ε : ℝ) :
    (∃ f, GoodTest (q ∘ e) ε n f) ↔ ∃ f, GoodTest q ε n f := by
  rw [goodTest_exists_iff_identity, goodTest_exists_iff_identity]
  exact goodIdentityTest_equiv e

end Relabeling

variable {A : Type*} [Fintype A] {q : A → ℝ} {ε : ℝ}

namespace CanonicalSplit

def pulledLaw (s : CanonicalSplit q ε) : Fin (s.headPred+1) ⊕ Fin s.tailSize → ℝ := q ∘ s.label

theorem pulledLaw_isLaw (s : CanonicalSplit q ε) (hq : IsLaw q) :
    IsLaw s.pulledLaw := ⟨fun i ↦ hq.nonneg (s.label i), (s.label.sum_comp q).trans hq.total⟩

theorem tailMass_nonneg (s : CanonicalSplit q ε) (hq : IsLaw q) : 0 ≤ s.tailMass :=
  Finset.sum_nonneg fun _ _ ↦ hq.nonneg _

theorem headProfile_eq_horizontal (s : CanonicalSplit q ε) (hq : IsLaw q) {n : ℝ}
    (hn : 0 < n) :
    CanonneHeadEnvelope.headMass s.pulledLaw *
      headProfile (n*CanonneHeadEnvelope.headMass s.pulledLaw) (orderedConditional (Equiv.refl _) s.pulledLaw) =
      CanonneQuantile.headProfile (fun i : Fin s.headPred ↦ (q (s.head i.succ))^((1 : ℝ)/3))
        (cutoffCandidates s.headPred) (cutoffCandidates_nonempty s.headPred) n :=
  regularHeadProfile_eq_quantile (Equiv.refl (Fin (s.headPred+1)))
    (s.pulledLaw_isLaw hq) hn (fun i ↦ s.head_pos i)

theorem goodTest_iff (s : CanonicalSplit q ε) (n : ℕ) :
    (∃ f, GoodTest s.pulledLaw ε n f) ↔ ∃ f, GoodTest q ε n f :=
  goodTest_exists_equiv s.label q n ε

end CanonicalSplit

end CanonneHeadEnvelope
