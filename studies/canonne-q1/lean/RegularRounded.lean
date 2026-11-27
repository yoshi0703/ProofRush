import RegularMarker
import NearOneBins

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {H T : Type*} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]

/-- Rounded regular pilot lower bound, with only scalar pilot charges supplied. -/
theorem no_good_test_of_regular_rounded_marker
    {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] {n : ℕ}
    (hn : 0 < n) {q fresh : H ⊕ T → ℝ} (hq : IsLaw q) (hfresh : IsLaw fresh)
    (hw : 0 < ∑ t : T, q (Sum.inr t))
    {b u : B → ℝ} {r : B → H ⊕ T → ℝ}
    (hb : ∀ j, 0 < b j) (hu : ∀ j, 0 < u j) (hbsum : ∑ j, b j ≤ 1)
    (hr : ∀ j, IsLaw (r j)) (href : q = bandedLabel b fresh r)
    (hrhead : ∀ j h, r j (Sum.inl h) = 0)
    (hrtop : ∀ j a, 0 < r j a → q a ≤ u j)
    (frozen : Finset T)
    (hfrozen : ∀ t ∉ frozen, (1 - ∑ j, b j) * fresh (Sum.inr t) = 0)
    {e x ρ : ℝ} (hx : 0 < x) (hρ : ρ ≤ 1/64)
    (hfrozenMass : (∑ t ∈ frozen, q (Sum.inr t)) ≤ ρ*x)
    (hlightMoment : (n : ℝ) * Real.sqrt x * (∑ j, b j * Real.sqrt (u j)) ≤ 2*ρ*x)
    (hgeom : (∑ j, u j) ≤ x/32)
    {weights : I → ℝ} (hweights : IsLaw weights)
    {alts : I → H ⊕ Unit → ℝ} (halts : ∀ i, IsLaw (alts i))
    (hdef : ∀ i, 0 < weights i →
      e - (∑ t : T, q (Sum.inr t)) + x < trueHeadDeficit q (alts i))
    (hprior : totalVariation (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw (collapsed q)) ≤ 1/8) :
    ¬ ∃ f, GoodTest q e n f := by
  let c := (n : ℝ) * Real.sqrt x
  let k (j : B) := CanonneColoredPilot.pilotCount c (b j) (u j)
  have hc : 0 < c := mul_pos (by exact_mod_cast hn) (Real.sqrt_pos.2 hx)
  have hk (j : B) : 0 < k j := pilotCount_pos hc (hb j) (hu j)
  have hslots : (∑ j, (k j : ℝ) * u j) ≤ 2*ρ*x + x/32 := by
    have hround := CanonneNearOne.rounded_pilot_cost_le
      (δ := x) (n := (n : ℝ)) (by positivity) (fun j => (hb j).le) hu
    change (∑ j, (k j : ℝ) * u j) ≤
      (n : ℝ) * Real.sqrt x * (∑ j, b j * Real.sqrt (u j)) + ∑ j, u j at hround
    linarith
  have hbudgetStrong : (∑ t ∈ frozen, q (Sum.inr t)) + (∑ j, (k j : ℝ) * u j) ≤ x := by
    have hρx := mul_le_mul_of_nonneg_right hρ hx.le
    nlinarith only [hρx, hslots, hfrozenMass, hx]
  let M := ∑ j, b j * Real.sqrt (u j)
  have hM : 0 ≤ M :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hb j).le (Real.sqrt_nonneg _))
  have hcollisionSum : (∑ j, (b j)^2/k j) ≤ M/c := by
    unfold M
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    simpa only [one_mul, mul_one, one_pow, one_div, k, mul_comm] using
      (collision_cost_upper (s := 1) hc (hb j) (hu j))
  have hcollision : (n.choose 2 : ℝ) * (∑ j, (b j)^2/k j) ≤ 2*ρ := by
    have hcast : (n.choose 2 : ℝ) ≤ (n : ℝ)^2 := by
      exact_mod_cast Nat.choose_le_pow n 2
    have heq : (n : ℝ)^2 * (M/c) = (c*M)/x := by
      have hroot := Real.sqrt_pos.2 hx
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      change (n : ℝ)^2 * (M / ((n : ℝ) * Real.sqrt x)) =
        (((n : ℝ) * Real.sqrt x) * M) / x
      field_simp
      nlinarith [Real.sq_sqrt hx.le]
    calc
      _ ≤ (n.choose 2 : ℝ) * (M/c) :=
        mul_le_mul_of_nonneg_left hcollisionSum (Nat.cast_nonneg _)
      _ ≤ (n : ℝ)^2 * (M/c) :=
        mul_le_mul_of_nonneg_right hcast (div_nonneg hM hc.le)
      _ = (c*M)/x := heq
      _ ≤ _ := (div_le_iff₀ hx).mpr hlightMoment
  exact no_good_test_of_regular_colored_marker hq hfresh hw (fun j => (hb j).le) hk hbsum
    hr href hrhead hrtop frozen hfrozen hbudgetStrong hweights halts hdef hprior (by linarith)

end
end CanonneRegularTransfer
