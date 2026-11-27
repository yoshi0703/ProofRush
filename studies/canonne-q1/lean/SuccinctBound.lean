import CanonicalTailFormula
import FiniteResolution

open CanonneDiffuse
open CanonneRefinement (nearMoment)
open CanonneHeadEnvelope (CanonicalSplit cutoffCandidates cutoffCandidates_nonempty cutoffCandidates_full exists_canonical_split)
open scoped BigOperators

namespace CanonneQuantile

/-- A rate above the reciprocal of a positive atom lower bound saturates the whole tail. -/
theorem tail_root_eq_sqrt_of_atom_lower {T : Type*} [Fintype T] (q : T → ℝ)
    (hq : ∀ i, 0 ≤ q i) {n p : ℝ} (hn : 0 ≤ n) (hp : 0 < p)
    (hmin : ∀ i, q i = 0 ∨ p ≤ q i) (hscale : 1/p ≤ n) :
    root q hq n hn = Real.sqrt (∑ i, q i) := by
  let w := ∑ i, q i
  let y := Real.sqrt w
  have hw : 0 ≤ w := Finset.sum_nonneg fun i _ ↦ hq i
  apply (exists_unique_tail_root q hq hn).unique (root_spec q hq hn)
  refine ⟨Real.sqrt_nonneg _,?_⟩
  rcases hw.eq_or_lt with hzero | hwpos
  · have hqz (i : T) : q i = 0 := by
      have hi : q i ≤ w := Finset.single_le_sum (fun j _ ↦ hq j) (Finset.mem_univ i)
      rw [← hzero] at hi
      exact hi.antisymm (hq i)
    simp [tail,hqz]
  · have hy : 0 < y := Real.sqrt_pos.mpr hwpos
    have hnp : 1 ≤ n*p := (div_le_iff₀ hp).mp hscale
    have hterm (i : T) : min (q i / y) (n*q i*Real.sqrt (q i)) = q i / y := by
      rcases hmin i with hzero | hi
      · simp [hzero]
      · apply min_eq_left
        apply (div_le_iff₀ hy).mpr
        have hiw : q i ≤ w := Finset.single_le_sum (fun j _ ↦ hq j) (Finset.mem_univ i)
        have hpw : Real.sqrt p ≤ y := Real.sqrt_le_sqrt (hi.trans hiw)
        have hpi : Real.sqrt p ≤ Real.sqrt (q i) := Real.sqrt_le_sqrt hi
        have hmul : p ≤ y * Real.sqrt (q i) := by
          rw [← Real.sq_sqrt hp.le, pow_two]
          exact mul_le_mul hpw hpi (Real.sqrt_nonneg _) hy.le
        have hsat := hnp.trans (mul_le_mul_of_nonneg_left hmul hn)
        calc
          q i = 1*q i := (one_mul _).symm
          _ ≤ (n*(y*Real.sqrt (q i)))*q i := mul_le_mul_of_nonneg_right hsat (hq i)
          _ = _ := by ring
    rw [tail_eq_clipped q hq hn hy]
    simp_rw [hterm]
    rw [← Finset.sum_div]
    change w/y = y
    apply (div_eq_iff hy.ne').mpr
    change w = Real.sqrt w * Real.sqrt w
    rw [← pow_two, Real.sq_sqrt hw]

variable {A : Type*} [Fintype A] {q : A → ℝ} {e : ℝ}

theorem canonical_slack_eq_radius_of_atom_lower (S : CanonicalSplit q e) (hq : IsLaw q)
    {n p : ℝ} (hn : 0 ≤ n) (hp : 0 < p) (hmin : ∀ a, q a = 0 ∨ p ≤ q a)
    (hscale : 1/p ≤ n) :
    slack (fun i ↦ q (S.tail i)) (fun i ↦ hq.nonneg (S.tail i)) (e-S.tailMass) n hn = e := by
  unfold slack
  rw [tail_root_eq_sqrt_of_atom_lower _ _ hn hp (fun i ↦ hmin (S.tail i)) hscale]
  change e-S.tailMass + (Real.sqrt S.tailMass)^2 = e
  rw [Real.sq_sqrt (S.tailMass_nonneg hq)]
  ring

private theorem unit_bulk_le_size {W k : ℝ} (hW : 0 ≤ W) (hk : 1 ≤ k) (hWk : W ≤ k) :
    bulk W 1 ≤ k := by
  apply (pow_le_pow_iff_left₀ (bulk_nonneg _ _) (by linarith : 0 ≤ k)
    (by decide : (4 : ℕ) ≠ 0)).mp
  rw [bulk_fourth hW]
  simp only [one_pow, div_one]
  calc
    W^3 ≤ k^3 := pow_le_pow_left₀ hW hWk 3
    _ = k^3*1 := by ring
    _ ≤ k^3*k := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = k^4 := by ring

theorem canonical_cost_le_size (S : CanonicalSplit q e) (hq : IsLaw q) {n : ℝ}
    (hn : 1 ≤ n) :
    cost (fun i : Fin S.headPred ↦ (q (S.head i.succ))^((1:ℝ)/3))
      (cutoffCandidates S.headPred) (cutoffCandidates_nonempty _)
      (S.tailMass*(1-S.tailMass)) n ≤ ((S.headPred : ℝ)+3)/Real.sqrt n := by
  let weights : Fin S.headPred → ℝ := fun i ↦ (q (S.head i.succ))^((1:ℝ)/3)
  let W := ∑ i, (weights i)^2
  let k := (S.headPred : ℝ)+1
  let w := S.tailMass
  let r := Real.sqrt n
  have hn₀ : 0 < n := zero_lt_one.trans_le hn
  have hr1 : 1 ≤ r := by simpa [r] using Real.sqrt_le_sqrt hn
  have hrp : 0 < r := zero_lt_one.trans_le hr1
  have hw0 : 0 ≤ w := S.tailMass_nonneg hq
  have hw1 : w ≤ 1 := by
    have hs := S.headMass_tailMass.trans hq.total
    have hh : 0 ≤ S.headMass := Finset.sum_nonneg fun _ _ ↦ hq.nonneg _
    linarith
  have hv : Real.sqrt (w*(1-w)) ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨zero_le_one,by nlinarith [sq_nonneg w]⟩
  have hW₀ : 0 ≤ W := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hWk : W ≤ k := by
    have hweights (i : Fin S.headPred) : (weights i)^2 ≤ 1 := by
      have h₀ : 0 ≤ weights i := Real.rpow_nonneg (hq.nonneg _) _
      have h₁ : weights i ≤ 1 := by
        simpa [weights] using Real.rpow_le_rpow (hq.nonneg (S.head i.succ))
          (atom_le_one hq _) (by norm_num : 0 ≤ (1:ℝ)/3)
      simpa using pow_le_pow_left₀ h₀ h₁ 2
    have he : W ≤ ∑ _i : Fin S.headPred, (1:ℝ) := Finset.sum_le_sum (fun i _ ↦ hweights i)
    simpa [k] using he.trans (by simp)
  have hB : bulk W n ≤ k/r := by
    have he : bulk W n = bulk W 1 / r := by
      have h := bulk_dilate hW₀ (by norm_num : (0:ℝ)<1) hrp
      simpa [r,Real.sq_sqrt hn₀.le] using h
    rw [he]
    exact div_le_div_of_nonneg_right (unit_bulk_le_size hW₀ (by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) S.headPred]) hWk) hrp.le
  have hP : headProfile weights (cutoffCandidates S.headPred) (cutoffCandidates_nonempty _) n ≤ k/r := by
    refine (Finset.inf'_le (fun U ↦ cutCost weights U n) (cutoffCandidates_full _)).trans ?_
    simpa [cutCost,W] using hB
  have hfloor : 1/n ≤ 1/r := by
    apply div_le_div_of_nonneg_left zero_le_one hrp
    have ht : r ≤ r^2 := by nlinarith [mul_le_mul_of_nonneg_left hr1 hrp.le]
    exact ht.trans_eq (Real.sq_sqrt hn₀.le)
  have htag : Real.sqrt (w*(1-w))/r ≤ 1/r := div_le_div_of_nonneg_right hv hrp.le
  change Real.sqrt (w*(1-w))/r + 1/n +
    headProfile weights (cutoffCandidates S.headPred) (cutoffCandidates_nonempty _) n
      ≤ ((S.headPred : ℝ)+3)/r
  calc
    _ ≤ 1/r+1/r+k/r := add_le_add (add_le_add htag hfloor) hP
    _ = _ := by unfold k; ring

/-- Explicit finite sufficient sample scale for the regular arithmetic criterion. -/
theorem regular_crossing_at_polynomial_scale (S : CanonicalSplit q e) (hq : IsLaw q) (he : 0 < e)
    {p : ℝ} (hp : 0 < p) (hmin : ∀ a, q a = 0 ∨ p ≤ q a) (j : ℕ)
    (hscale : 1/p ≤ (2:ℝ)^j)
    (hcost : (((S.headPred:ℝ)+3)/(strongFactor*e))^2 ≤ (2:ℝ)^j) :
    crossingPredicate S hq j := by
  let n := (2:ℝ)^j
  have hn : 1 ≤ n := one_le_pow₀ (by norm_num)
  have hS := canonical_slack_eq_radius_of_atom_lower S hq (by positivity : 0 ≤ n)
    hp hmin hscale
  have hc : 0 < strongFactor*e := mul_pos (by norm_num [strongFactor]) he
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.mpr (zero_lt_one.trans_le hn)
  have hB : ((S.headPred:ℝ)+3)/Real.sqrt n ≤ strongFactor*e := by
    apply (div_le_iff₀ hr).mpr
    have h := Real.le_sqrt_of_sq_le hcost
    have hm := (div_le_iff₀ hc).mp h
    linarith only [hm]
  unfold crossingPredicate crosses
  change _ ≤ strongFactor * slack _ _ _ n _
  rw [hS]
  exact (canonical_cost_le_size S hq hn).trans hB

/-- With binary lower bounds on masses and radius, the number of dyadic comparisons is linear
in the three supplied bit bounds. The constant 22 covers the fixed strong-factor threshold. -/
theorem regular_crossing_at_bit_budget (S : CanonicalSplit q e) (hq : IsLaw q) (he : 0 < e)
    (P E K : ℕ) (hmin : ∀ a, q a = 0 ∨ 1/(2:ℝ)^P ≤ q a)
    (hebit : 1/(2:ℝ)^E ≤ e) (hsize : (S.headPred:ℝ)+3 ≤ (2:ℝ)^K) :
    crossingPredicate S hq (max P (2*(K+E+22))) := by
  let J := max P (2*(K+E+22))
  have hpp : 0 < 1/(2:ℝ)^P := by positivity
  have hp : 1/(1/(2:ℝ)^P) ≤ (2:ℝ)^J := by
    simp only [one_div_one_div]
    exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  apply regular_crossing_at_polynomial_scale S hq he hpp hmin J hp
  have hCe : 0 < strongFactor*e := mul_pos (by norm_num [strongFactor]) he
  have hB : 1/(2:ℝ)^(E+22) ≤ strongFactor*e := by
    rw [pow_add]
    calc
      _ = (1/(2:ℝ)^22) * (1/(2:ℝ)^E) := by ring
      _ ≤ strongFactor*e := mul_le_mul (by norm_num [strongFactor]) hebit (by positivity)
        (by norm_num [strongFactor])
  have ht : ((S.headPred:ℝ)+3)/(strongFactor*e) ≤ (2:ℝ)^(K+E+22) := by
    apply (div_le_iff₀ hCe).mpr
    refine hsize.trans ?_
    calc
      _ = (2:ℝ)^(K+E+22) * (1/(2:ℝ)^(E+22)) := by
        rw [show K+E+22=K+(E+22) by omega, pow_add]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
  calc
    _ ≤ ((2:ℝ)^(K+E+22))^2 := pow_le_pow_left₀ (by positivity) ht 2
    _ = (2:ℝ)^(2*(K+E+22)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2:ℝ)^J := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)

end CanonneQuantile

namespace CanonneQuantile

variable {A : Type*} [Fintype A] {q : A → ℝ} {e : ℝ}

/-- The crossing predicate after replacing the implicit root by finitely many radicals. -/
noncomputable def explicitCrossing (S : CanonicalSplit q e) (j : ℕ) : Prop :=
  let n := (2:ℝ)^j
  Real.sqrt (S.tailMass*(1-S.tailMass)) / Real.sqrt n + 1/n +
      CanonneHeadEnvelope.headProfile n (fun i ↦ q (S.head i)) ≤
    strongFactor * (e-S.tailMass +
      (tailPrefixQuadraticMinimum (fun i ↦ q (S.tail i)) n)^2)

theorem crossing_iff_explicit [DecidableEq A] (S : CanonicalSplit q e) (hq : IsLaw q) (j : ℕ) :
    crossingPredicate S hq j ↔ explicitCrossing S j := by
  let n := (2:ℝ)^j
  have hn : 0 < n := by dsimp [n]; positivity
  have hr := (S.tail_root_eq hq hn.le).symm.trans (S.tail_root_eq_finite_formula hq hn.le)
  have hP := CanonneHeadEnvelope.headProfile_eq_quantile
    (q := fun i ↦ q (S.head i)) hn (fun i ↦ hq.nonneg _)
  unfold crossingPredicate crosses explicitCrossing cost slack
  dsimp only
  rw [← hP, hr]

/-- Scan at most J+1 dyadic indices. The value is zero for an empty scan. -/
noncomputable def boundedFirstDyadic (P : ℕ → Prop) (J : ℕ) : ℕ := by
  classical
  let C := (Finset.range (J+1)).filter P
  exact if h : C.Nonempty then 2^(C.min' h) else 0

theorem firstDyadic_eq_bounded (P : ℕ → Prop) {J : ℕ} (h : P J) :
    firstDyadic P = boundedFirstDyadic P J := by
  classical
  let C := (Finset.range (J+1)).filter P
  have hmem (i : ℕ) (hi : i ≤ J) (hp : P i) : i ∈ C :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩
  have hC : C.Nonempty := ⟨J,hmem J le_rfl h⟩
  obtain ⟨j,hj,hvalue,hmin⟩ := firstDyadic_spec P ⟨J,h⟩
  have hjC := hmem j (hmin J h) hj
  have hEq : j = C.min' hC := le_antisymm
    (hmin _ (Finset.mem_filter.mp (Finset.min'_mem C hC)).2)
    (Finset.min'_le C j hjC)
  unfold boundedFirstDyadic
  change firstDyadic P = if h' : C.Nonempty then 2^C.min' h' else 0
  rw [dite_eq_left hC,hvalue,hEq]

theorem firstDyadic_congr {P Q : ℕ → Prop} (h : ∀ i, P i ↔ Q i) :
    firstDyadic P = firstDyadic Q := by
  have he : P = Q := funext (fun i ↦ propext (h i))
  rw [he]

theorem canonical_search_bound [DecidableEq A] (S : CanonicalSplit q e) (hq : IsLaw q)
    (he : 0 < e) (P E K : ℕ) (hmin : ∀ a, q a = 0 ∨ 1/(2:ℝ)^P ≤ q a)
    (hebit : 1/(2:ℝ)^E ≤ e) (hsize : (S.headPred:ℝ)+3 ≤ (2:ℝ)^K) :
    let J := max P (2*(K+E+22))
    regularRate S hq = boundedFirstDyadic (explicitCrossing S) J := by
  intro J
  have hc := regular_crossing_at_bit_budget S hq he P E K hmin hebit hsize
  rw [regularRate, firstDyadic_congr (crossing_iff_explicit S hq)]
  exact firstDyadic_eq_bounded _ ((crossing_iff_explicit S hq J).mp hc)

theorem canonical_size_encoding (S : CanonicalSplit q e) :
    (S.headPred:ℝ)+3 ≤ (2:ℝ)^(Fintype.card A+3) := by
  have h := Fintype.card_congr S.label
  simp only [Fintype.card_sum,Fintype.card_fin] at h
  have hN : S.headPred+3 ≤ Fintype.card A+3 := by omega
  exact_mod_cast hN.trans (Nat.lt_two_pow_self : _ < 2^(Fintype.card A+3)).le

theorem bit_lower_of_positive_fraction {num den B : ℕ} (hn : 0 < num)
    (hd : 0 < den) (hb : den ≤ 2^B) :
    1/(2:ℝ)^B ≤ (num:ℝ)/(den:ℝ) := by
  have hden : 0 < (den:ℝ) := by exact_mod_cast hd
  have h₂ : (den:ℝ) ≤ (2:ℝ)^B := by exact_mod_cast hb
  have h₁ : (1:ℝ) ≤ (num:ℝ) := by exact_mod_cast hn
  exact (one_div_le_one_div_of_le hden h₂).trans
    (div_le_div_of_nonneg_right h₁ hden.le)

variable [DecidableEq A]

/-- The main rate expressed by a fixed finite scan on the sorted arithmetic data. -/
noncomputable def explicitFiniteRate (q : A → ℝ) (hq : IsLaw q) (e : ℝ) (he : 0 < e) (J : ℕ) :
    ℕ := by
  classical
  exact if ha : ∃ a, e < 1-q a then
    if 16*(1-e) ≤ nearMoment q (1-e) then directRate q (1-e)
    else
      let he1 : e < 1 := by
        obtain ⟨a,ha⟩ := ha
        linarith [hq.nonneg a]
      boundedFirstDyadic (explicitCrossing (exists_canonical_split q hq.total he.le he1).some) J
  else 0

theorem finiteRate_eq_explicit (q : A → ℝ) (hq : IsLaw q) (e : ℝ) (he : 0 < e)
    (P E : ℕ) (hmin : ∀ a, q a = 0 ∨ 1/(2:ℝ)^P ≤ q a) (hebit : 1/(2:ℝ)^E ≤ e) :
    finiteRate q hq e he =
      explicitFiniteRate q hq e he (max P (2*(Fintype.card A+3+E+22))) := by
  classical
  by_cases halt : ∃ a, e < 1-q a
  · have he1 : e < 1 := by
      obtain ⟨a,ha⟩ := halt
      linarith [hq.nonneg a]
    by_cases hnear : 16*(1-e) ≤ nearMoment q (1-e)
    · simp [finiteRate,explicitFiniteRate,halt,hnear]
    · let S := (exists_canonical_split q hq.total he.le he1).some
      have hs := canonical_search_bound S hq he P E (Fintype.card A+3) hmin hebit
        (canonical_size_encoding S)
      simpa [finiteRate,explicitFiniteRate,halt,hnear,S] using hs
  · simp [finiteRate,explicitFiniteRate,halt]

/-- For explicit nonnegative rational inputs, use the common denominator bit bounds on each
component. The scan is over at most max(P,2(card A+3+E+22))+1 indices. -/
theorem finiteRate_eq_explicit_of_rational_input (q : A → ℝ) (hq : IsLaw q) (e : ℝ)
    (he : 0 < e) (P E : ℕ)
    (hqbits : ∀ a, q a = 0 ∨ ∃ num den : ℕ, 0 < num ∧ 0 < den ∧
      den ≤ 2^P ∧ q a = (num:ℝ)/(den:ℝ))
    (hebits : ∃ num den : ℕ, 0 < num ∧ 0 < den ∧ den ≤ 2^E ∧ e = (num:ℝ)/(den:ℝ)) :
    finiteRate q hq e he =
      explicitFiniteRate q hq e he (max P (2*(Fintype.card A+3+E+22))) := by
  apply finiteRate_eq_explicit q hq e he P E
  · intro a
    rcases hqbits a with hz | ⟨num,den,hnum,hden,hbit,heq⟩
    · exact Or.inl hz
    · rw [heq]
      exact Or.inr (bit_lower_of_positive_fraction hnum hden hbit)
  · obtain ⟨num,den,hnum,hden,hbit,rfl⟩ := hebits
    exact bit_lower_of_positive_fraction hnum hden hbit

end CanonneQuantile
