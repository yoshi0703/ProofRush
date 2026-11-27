import MarkerPrior
import RegularCut

open scoped BigOperators
open CanonneDiffuse CanonneHeadTransfer CanonneRegularTransfer CanonneNearOneTesting

namespace CanonneHeadEnvelope

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

noncomputable def headMass (q : H ⊕ T → ℝ) : ℝ :=
  ∑ h : H, q (Sum.inl h)

noncomputable def orderedConditional {d : ℕ} (order : Fin (d+1) ≃ H) (q : H ⊕ T → ℝ)
    (i : Fin (d+1)) : ℝ :=
  q (Sum.inl (order i)) / headMass q

omit [DecidableEq H] [DecidableEq T] in
theorem exists_regular_head_prior {d n : ℕ} (order : Fin (d+1) ≃ H)
    {q : H ⊕ T → ℝ} (hq : IsLaw q) (hn : 0 < n)
    (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i ↦ q (Sum.inl (order i))))
    {ε : ℝ} (hfar : 32*ε < headMass q * headProfile ((n : ℝ)*headMass q)
      (orderedConditional order q)) :
    ∃ weights : (Fin ((d+1)/2) → Bool) → ℝ, ∃ alts : (Fin ((d+1)/2) → Bool) → H ⊕ Unit → ℝ,
      IsLaw weights ∧ (∀ s, IsLaw (alts s)) ∧
      (∀ s, alts s (Sum.inr ()) = collapsed q (Sum.inr ())) ∧
      (∀ s, ε < trueHeadDeficit q (alts s)) ∧
      totalVariation (mixLaw weights (fun s ↦ pilotLaw (I := Fin n) (alts s)))
        (pilotLaw (collapsed q)) ≤ 1/8 := by
  let A := headMass q
  let h := orderedConditional order q
  have hA : 0 < A := by
    have hp := hpos 0
    apply hp.trans_le
    exact Finset.single_le_sum (fun i _ ↦ hq.nonneg (Sum.inl i))
      (Finset.mem_univ (order 0))
  have hh (i : Fin (d+1)) : 0 ≤ h i := div_nonneg (hq.nonneg _) hA.le
  have hsame : (fun i ↦ collapsed q (Sum.inl (order i))) = fun i ↦ A * h i := by
    funext i
    change q (Sum.inl (order i)) = A * (q (Sum.inl (order i)) / A)
    field_simp
  have hS : 32*ε < headProfile n (fun i ↦ collapsed q (Sum.inl (order i))) := by
    rw [hsame, headProfile_scale (Nat.cast_pos.mpr hn) hA hh]
    exact hfar
  have hcol := collapsed_isLaw hq
  obtain ⟨alts,hp,ht,hmark,hdef,hprior⟩ :=
    exists_marker_paired_prior order (collapsed q) hn hcol.nonneg hcol.total hpos horder hS
  let S := Fin ((d+1)/2) → Bool
  let c := (Fintype.card S : ℝ)
  let weights : S → ℝ := fun _ ↦ 1/c
  have hc : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  have hweights : IsLaw weights := ⟨fun _ ↦ by positivity, by
    dsimp [weights]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change c * (1/c) = 1
    field_simp⟩
  refine ⟨weights,alts,hweights,fun s ↦ ⟨hp s,ht s⟩,hmark,hdef,?_⟩
  have heq : mixLaw weights (fun s ↦ pilotLaw (I := Fin n) (alts s)) =
      mixture (fun s ↦ iidMass n (alts s)) := by
    funext x
    unfold mixLaw mixture
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    change 1/c * iidMass n (alts s) x = iidMass n (alts s) x / c
    ring
  rw [heq]
  exact hprior

/-- Combine the source-profile paired head prior with the original regular cutoff lower test. -/
theorem no_good_test_of_regular_cut_and_head {d n : ℕ} (order : Fin (d+1) ≃ H)
    (hn : 0 < n) {q : H ⊕ T → ℝ} (hq : IsLaw q)
    (hw : 0 < ∑ t : T, q (Sum.inr t))
    (hpos : ∀ i, 0 < q (Sum.inl (order i)))
    (horder : Antitone (fun i ↦ q (Sum.inl (order i))))
    {e x τ ρ : ℝ} (hx : 0 < x) (hτ : 0 < τ) (hρ : ρ ≤ 1/64)
    (hfrozen : (∑ t ∈ Finset.univ.filter (fun t : T => τ ≤ q (Sum.inr t)),
      q (Sum.inr t)) ≤ ρ*x)
    (hlight : (n : ℝ) * Real.sqrt x *
      (∑ t ∈ Finset.univ.filter (fun t : T => q (Sum.inr t) < τ),
        q (Sum.inr t) * Real.sqrt (q (Sum.inr t))) ≤ ρ*x)
    (hgeom : 2*τ ≤ x/32)
    (hfar : 32*(e - (∑ t : T, q (Sum.inr t)) + x) <
      headMass q * headProfile ((n : ℝ) * headMass q) (orderedConditional order q)) :
    ¬ ∃ f, GoodTest q e n f := by
  obtain ⟨weights,alts,hweights,halts,_,hdef,hprior⟩ :=
    exists_regular_head_prior order hq hn hpos horder hfar
  exact no_good_test_of_regular_cut hn hq hw hx hτ hρ hfrozen hlight hgeom hweights
    halts (fun s _ ↦ hdef s) hprior

end CanonneHeadEnvelope
