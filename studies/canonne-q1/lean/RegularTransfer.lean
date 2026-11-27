import NearOneTesting

namespace CanonneRegularTransfer

open CanonneDiffuse CanonneHeadTransfer CanonneColoredPilot CanonneNearOneTesting
open scoped BigOperators
noncomputable section

variable {R A Ω I : Type*} [Fintype R] [Fintype A] [Fintype Ω] [Fintype I] {n : ℕ}

/-- Apply the same one-label channel at each coordinate, conditional on a
fixed tape. The input and output sequences are ordered. -/
def orderedChannel (K : R → A → ℝ) (ys : Fin n → R) : (Fin n → A) → ℝ :=
  independentLaw (fun i => K (ys i))

omit [Fintype R] in
theorem orderedChannel_isLaw {K : R → A → ℝ} (hK : ∀ r, IsLaw (K r))
    (ys : Fin n → R) : IsLaw (orderedChannel K ys) :=
  independentLaw_isLaw (fun i => hK (ys i))

omit [Fintype A] in
theorem iid_through_ordered_channel (s : R → ℝ) (K : R → A → ℝ) :
    mixLaw (pilotLaw (I := Fin n) s) (orderedChannel K) =
      pilotLaw (mixLaw s K) := by
  funext out
  unfold mixLaw orderedChannel independentLaw pilotLaw
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => s a * K a (out i))).symm

/-- A tape is drawn once per experiment, and all coordinates use its channel.
The same law of tapes can be applied to arbitrary reduced sample laws. -/
def commonChannel (tape : Ω → ℝ) (K : Ω → R → A → ℝ)
    (ys : Fin n → R) : (Fin n → A) → ℝ :=
  mixLaw tape (fun z => orderedChannel (K z) ys)

omit [Fintype R] in
theorem commonChannel_isLaw {tape : Ω → ℝ} (ht : IsLaw tape)
    {K : Ω → R → A → ℝ} (hK : ∀ z r, IsLaw (K z r)) (ys : Fin n → R) :
    IsLaw (commonChannel tape K ys) :=
  mixLaw_isLaw ht _ (fun z => orderedChannel_isLaw (hK z) ys)

theorem mix_commutes {X : Type*} [Fintype X] (p : I → ℝ) (q : Ω → ℝ)
    (f : I → Ω → X → ℝ) :
    mixLaw p (fun i => mixLaw q (f i)) =
      mixLaw q (fun j => mixLaw p (fun i => f i j)) := by
  funext x
  unfold mixLaw
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem mix_associative {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (p : X → ℝ) (K : X → Y → ℝ) (L : Y → Z → ℝ) :
    mixLaw (mixLaw p K) L = mixLaw p (fun x => mixLaw (K x) L) := by
  funext z
  unfold mixLaw
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem common_channel_on_iid (s : R → ℝ) (tape : Ω → ℝ) (K : Ω → R → A → ℝ) :
    mixLaw (pilotLaw (I := Fin n) s) (commonChannel tape K) =
      mixLaw tape (fun z => pilotLaw (mixLaw s (K z))) := by
  unfold commonChannel
  rw [mix_commutes]
  simp only [iid_through_ordered_channel]

theorem randomized_channel_test {X Y : Type*} [Fintype X] [Fintype Y]
    {K : X → Y → ℝ} (hK : ∀ x, IsLaw (K x)) {f : Y → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    ∀ x, 0 ≤ rejection (K x) f ∧ rejection (K x) f ≤ 1 := by
  intro x
  refine ⟨Finset.sum_nonneg (fun y _ => mul_nonneg ((hK x).nonneg y) (hf y).1), ?_⟩
  rw [← (hK x).total]
  exact Finset.sum_le_sum fun y _ => by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf y).2 ((hK x).nonneg y)

theorem rejection_bound_for_common_channel {X Y : Type*}
    [Fintype X] [Fintype Y] {p q : X → ℝ} (hp : IsLaw p) (hq : IsLaw q)
    {K : X → Y → ℝ} (hK : ∀ x, IsLaw (K x)) {f : Y → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    rejection (mixLaw p K) f - rejection (mixLaw q K) f ≤ totalVariation p q := by
  rw [rejection_mix, rejection_mix, tv_comm]
  exact rejection_sub_le_tv hp hq (randomized_channel_test hK hf)

/-- A full test would imply a reduced test at the same sample budget. Only the
predictive reduced prior needs to be close to its reduced null. The change in
marker mass of any individual prior law can be arbitrary, since the tape
channel is identical for the two input experiments. -/
theorem no_good_test_of_common_channel {q : A → ℝ} (hq : IsLaw q)
    {qred : R → ℝ} (hred : IsLaw qred)
    {weights : I → ℝ} (hweights : IsLaw weights)
    {alts : I → R → ℝ} (halts : ∀ i, IsLaw (alts i))
    {tape : Ω → ℝ} (htape : IsLaw tape) {K : Ω → R → A → ℝ}
    (hK : ∀ z r, IsLaw (K z r)) {e gateround priorround : ℝ}
    (hgap : gateround + priorround < 1/3)
    (hnull : totalVariation
      (mixLaw tape (fun z => pilotLaw (I := Fin n) (mixLaw qred (K z))))
      (pilotLaw q) ≤ gateround)
    (hprior : totalVariation
      (mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i)))
      (pilotLaw qred) ≤ priorround)
    (hfar : ∀ i z, 0 < weights i → 0 < tape z →
      e < totalVariation (mixLaw (alts i) (K z)) q) :
    ¬ ∃ f, GoodTest q e n f := by
  let C := commonChannel (n := n) tape K
  let P := mixLaw weights (fun i => pilotLaw (I := Fin n) (alts i))
  let Q := pilotLaw (I := Fin n) qred
  have hC (ys : Fin n → R) : IsLaw (C ys) := commonChannel_isLaw htape hK ys
  have hP : IsLaw P := mixLaw_isLaw hweights _ (fun i => pilotLaw_isLaw (halts i))
  have hQ : IsLaw Q := pilotLaw_isLaw hred
  intro ⟨f, hf, hqtest, hfarTest⟩
  have h1 := rejection_bound_for_common_channel hP hQ hC hf
  have h2 := rejection_sub_le_tv (mixLaw_isLaw hQ C hC) (pilotLaw_isLaw hq) hf
  rw [tv_comm] at h2
  have h2' : totalVariation (mixLaw Q C) (pilotLaw q) ≤ gateround := by
    change totalVariation (mixLaw (pilotLaw qred) (commonChannel tape K)) (pilotLaw q) ≤ gateround
    rwa [common_channel_on_iid]
  have hprior' : totalVariation P Q ≤ priorround := hprior
  have hbig : 2/3 ≤ rejection (mixLaw P C) f := by
    rw [show mixLaw P C = mixLaw weights (fun i => mixLaw
      (pilotLaw (I := Fin n) (alts i)) C) from mix_associative _ _ _]
    rw [rejection_mix]
    calc
      _ = (∑ i, weights i) * (2/3) := by rw [hweights.total, one_mul]
      _ = ∑ i, weights i * (2/3) := Finset.sum_mul _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weights i = 0
        · simp [hi]
        · apply mul_le_mul_of_nonneg_left _ (hweights.nonneg i)
          change _ ≤ rejection (mixLaw (pilotLaw (I := Fin n) (alts i)) (commonChannel tape K)) f
          rw [common_channel_on_iid, rejection_mix]
          calc
            _ = (∑ z, tape z) * (2/3) := by rw [htape.total, one_mul]
            _ = ∑ z, tape z * (2/3) := Finset.sum_mul _ _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro z _
              by_cases hz : tape z = 0
              · simp [hz]
              · have hp := mixLaw_isLaw (halts i) (K z) (hK z)
                exact mul_le_mul_of_nonneg_left (hfarTest _ hp
                  (hfar i z (lt_of_le_of_ne (hweights.nonneg i) (Ne.symm hi))
                    (lt_of_le_of_ne (htape.nonneg z) (Ne.symm hz)))) (htape.nonneg z)
  linarith

end
end CanonneRegularTransfer
