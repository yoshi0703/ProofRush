import RegularUpperGlue

namespace CanonneQuantile

open CanonneDiffuse CanonneHeadTransfer
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

def retainedDistance (K : Finset A) (p q : A → ℝ) : ℝ :=
  ∑ i ∈ K, |p i-q i|

/-- The remaining labels can be paid for by their null and alternative
masses, even when all observations are unconditioned full samples. -/
theorem off_distance_le_retained_plus_light (T : Finset A) (a : A)
    (K : Finset A) (hK : K ⊆ Tᶜ.erase a) {p q : A → ℝ} (hp : IsLaw p) (hq : IsLaw q) :
    headOffDistance T a p q ≤
      retainedDistance K p q+mass p (Tᶜ.erase a \ K)+mass q (Tᶜ.erase a \ K) := by
  let L := Tᶜ.erase a \ K
  have b : retainedDistance L p q ≤ mass p L+mass q L := by
    unfold retainedDistance mass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact (abs_sub (p i) (q i)).trans_eq (by
      rw [abs_of_nonneg (hp.nonneg i), abs_of_nonneg (hq.nonneg i)])
  have s : retainedDistance L p q+retainedDistance K p q = headOffDistance T a p q :=
    Finset.sum_sdiff hK
  change headOffDistance T a p q ≤ retainedDistance K p q+mass p L+mass q L
  linarith

/-- A light-set test augments a retained-label test to cover all off-largest
head labels. Both components use ordinary samples on the original alphabet. -/
theorem shape_test_with_light (q : A → ℝ) (hq : IsLaw q) (T K : Finset A) (a : A)
    (hK : K ⊆ Tᶜ.erase a) {t n : ℕ} (hn : 0 < n)
    {d dLight : ℝ} (hLight : mass q (Tᶜ.erase a \ K) ≤ dLight)
    {retained : (Fin t → A) → ℝ}
    (rUnit : ∀ z, 0 ≤ retained z ∧ retained z ≤ 1)
    (rNull : tailRejection q retained ≤ 1/100)
    (rAlt : ∀ p : A → ℝ, IsLaw p → d < retainedDistance K p q →
        99/100 ≤ tailRejection p retained) :
    ∃ f : (Fin (t+n) → A) → ℝ, (∀ z, 0 ≤ f z ∧ f z ≤ 1) ∧
      tailRejection q f ≤ 1/50 ∧
      ∀ p : A → ℝ, IsLaw p →
        d+4097*dLight+4096/(n : ℝ) < headOffDistance T a p q →
        99/100 ≤ tailRejection p f := by
  classical
  let L := Tᶜ.erase a \ K
  let E := groupMassReject (n := n) q L
  let g (z : Fin n → A) : ℝ := if E z then 1 else 0
  let f := batchOr retained g
  have gUnit (z) : 0 ≤ g z ∧ g z ≤ 1 := by by_cases h : E z <;> simp [g,h]
  have gNull : tailRejection q g ≤ 1/100 := by
    rw [show tailRejection q g = eventMass (pilotLaw q) E from rejection_indicator q E]
    exact group_gate_null q hq L
  refine ⟨f, batchOr_unit rUnit gUnit, ?_, ?_⟩
  · have both := (batchOr_bounds hq rUnit gUnit).2.2
    change tailRejection q f ≤ tailRejection q retained+tailRejection q g at both
    linarith
  · intro p hp hfar
    have both := batchOr_bounds hp rUnit gUnit
    by_cases hR : d < retainedDistance K p q
    · exact (rAlt p hp hR).trans both.1
    · have b := off_distance_le_retained_plus_light T a K hK hp hq
      have hshift : 4096*(mass q L+1/(n : ℝ)) < mass p L := by
        change mass q L ≤ dLight at hLight
        change headOffDistance T a p q ≤ retainedDistance K p q+mass p L+mass q L at b
        have distribute : (4096 : ℝ)*(mass q L+1/(n : ℝ)) =
            4096*mass q L+4096/(n : ℝ) := by ring
        rw [distribute]
        linarith [le_of_not_gt hR]
      have miss := group_gate_light_power hn q hq L hp hshift
      have comp := eventMass_complement (pilotLaw_isLaw hp) E
      have hpow : 99/100 ≤ tailRejection p g := by
        rw [show tailRejection p g = eventMass (pilotLaw p) E from rejection_indicator p E]
        linarith
      exact hpow.trans both.2.1

/-- A deterministic strong crossing gives the regular upper bound once
the ordinary off-largest head test is supplied. The positive root is the
square root of the tail overlap scale in the mathematical statement. -/
theorem regular_upper_of_root_crossing (q : A → ℝ) (hq : IsLaw q) (T : Finset A)
    {a : A} (ha : a ∉ T) {n m : ℕ} (hn : 0 < n) {e r : ℝ}
    (hΔ : mass q T ≤ e) (hr : 0 ≤ r)
    (strong : 256*(1024*groupScale q T n/(n : ℝ)+r) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2)
    {shape : (Fin m → A) → ℝ}
    (shUnit : ∀ z, 0 ≤ shape z ∧ shape z ≤ 1) (shNull : tailRejection q shape ≤ 1/10)
    (shAlt : ∀ p : A → ℝ, IsLaw p → r < headOffDistance T a p q →
      9/10 ≤ tailRejection p shape) :
    ∃ j ≤ 3073*n+m, ∃ f, groupedIdentityTest q e j f := by
  let y := root (tailMask T q) (tailMask_nonneg T hq) (n : ℝ) (Nat.cast_nonneg n)
  let Δ := e-mass q T
  let G := 1024*groupScale q T n/(n : ℝ)+r
  change 256*G ≤ Δ+y^2 at strong
  have hd : 0 ≤ Δ := sub_nonneg.mpr hΔ
  have hy : 0 ≤ y := (root_spec (tailMask T q) (tailMask_nonneg T hq) (Nat.cast_nonneg n)).1
  by_cases small : y^2 ≤ Δ
  · have hgap : G ≤ Δ := by linarith
    refine ⟨n+m, by omega, ?_⟩
    exact regular_upper_head_only q hq T ha hn hgap shUnit shNull shAlt
  · let x := (y/16)^2
    have H : y^2 = 256*x := by dsimp [x]; ring
    have hx : 0 < x := by
      have hysq : 0 < y^2 := lt_of_le_of_lt hd (lt_of_not_ge small)
      have he : 0 < y := by
        by_contra! hn0
        have hy0 : y = 0 := le_antisymm hn0 hy
        simp [hy0] at hysq
      exact sq_pos_of_pos (div_pos he (by norm_num))
    have forward : 16*Real.sqrt x ≤ y := by
      change 16*Real.sqrt ((y/16)^2) ≤ y
      rw [Real.sqrt_sq (div_nonneg hy (by norm_num))]
      linarith
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    have L : 1 ≤ groupScale q T n := by
      unfold groupScale
      linarith [Real.sqrt_nonneg ((n : ℝ)*(mass q T*(1-mass q T)))]
    have bigG : 1024/(n : ℝ) ≤ G := by
      have h := mul_le_mul_of_nonneg_left L (show 0 ≤ (1024 : ℝ) by norm_num)
      have hh := div_le_div_of_nonneg_right h hn'.le
      dsimp [G]
      linarith
    have nx : 1 ≤ (n : ℝ)*x := by
      have a₀ : 256*(1024/(n : ℝ)) ≤ 2*y^2 := by linarith
      have a₁ := mul_le_mul_of_nonneg_left a₀ hn'.le
      have cancel : (n : ℝ)*(256*(1024/(n : ℝ))) = 262144 := by
        field_simp [hn'.ne']
        norm_num
      rw [cancel, H] at a₁
      nlinarith
    have criterion_large := criterion_at_forward_scale (tailMask T q) (tailMask_nonneg T hq)
      hn' hx forward
    have sep : G ≤ Δ+x := by linarith
    exact regular_upper_with_criterion q hq T ha hn hx nx criterion_large sep shUnit shNull shAlt

/-- The same deterministic crossing with a retained-label statistic
plus the automatic light-set test. -/
theorem regular_upper_from_retained_crossing (q : A → ℝ) (hq : IsLaw q) (T K : Finset A)
    {a : A} (ha : a ∉ T) (hK : K ⊆ Tᶜ.erase a)
    {n t : ℕ} (hn : 0 < n) {e d dLight : ℝ}
    (hd : 0 ≤ d) (hΔ : mass q T ≤ e) (hLight : mass q (Tᶜ.erase a \ K) ≤ dLight)
    (strong : 256*(1024*groupScale q T n/(n : ℝ) + (d+4097*dLight+4096/(n : ℝ))) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2)
    {retained : (Fin t → A) → ℝ}
    (rUnit : ∀ z, 0 ≤ retained z ∧ retained z ≤ 1)
    (rNull : tailRejection q retained ≤ 1/100)
    (rAlt : ∀ p : A → ℝ, IsLaw p → d < retainedDistance K p q →
      99/100 ≤ tailRejection p retained) :
    ∃ j ≤ 3074*n+t, ∃ f, groupedIdentityTest q e j f := by
  have light_nonneg := (law_mass_bounds (Tᶜ.erase a \ K) hq).1.trans hLight
  have hr : 0 ≤ d+4097*dLight+4096/(n : ℝ) := by positivity
  obtain ⟨shape, hu, hnull, hpow⟩ := shape_test_with_light q hq T K a hK hn
    hLight rUnit rNull rAlt
  obtain ⟨j, hj, f, hf⟩ := regular_upper_of_root_crossing q hq T ha hn hΔ hr strong hu
    (hnull.trans (by norm_num)) (fun p hp h => (by norm_num : (9/10 : ℝ) ≤ 99/100).trans (hpow p hp h))
  exact ⟨j, by omega, f, hf⟩

omit [Fintype A] in

theorem nested_omitted_mass (q : A → ℝ) (O R K : Finset A)
    (hK : K ⊆ R) (hR : R ⊆ O) :
    mass q (O \ K) = mass q (O \ R)+mass q (R \ K) := by
  have sub : R \ K ⊆ O \ K := by
    intro a ha
    obtain ⟨h, hk⟩ := Finset.mem_sdiff.mp ha
    exact Finset.mem_sdiff.mpr ⟨hR h, hk⟩
  have eq : (O \ K) \ (R \ K) = O \ R := by
    ext a
    simp only [Finset.mem_sdiff]
    have imply : a ∈ K → a ∈ R := fun h => hK h
    tauto
  unfold mass
  rw [← Finset.sum_sdiff sub, eq]

/-- Use a retained test in a candidate head prefix R. Trimming within R
can cost at most B additional omitted mass. A strong crossing computed
from the candidate bulk B and its original omitted mass suffices. -/
theorem regular_upper_from_prefix_test (q : A → ℝ) (hq : IsLaw q)
    (T R K : Finset A) {a : A} (ha : a ∉ T) (hKR : K ⊆ R) (hR : R ⊆ Tᶜ.erase a)
    {n t : ℕ} (hn : 0 < n) {e B : ℝ} (hΔ : mass q T ≤ e) (hB : 0 ≤ B)
    (trim : mass q (R \ K) ≤ B)
    (strong : 4000000*(groupScale q T n/(n : ℝ)+B+mass q (Tᶜ.erase a \ R)) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2)
    {retained : (Fin t → A) → ℝ}
    (rUnit : ∀ z, 0 ≤ retained z ∧ retained z ≤ 1)
    (rNull : tailRejection q retained ≤ 1/100)
    (rAlt : ∀ p : A → ℝ, IsLaw p → 10000*B < retainedDistance K p q →
      99/100 ≤ tailRejection p retained) :
    ∃ j ≤ 3074*n+t, ∃ f, groupedIdentityTest q e j f := by
  let O := Tᶜ.erase a
  let U := mass q (O \ R)
  let L := groupScale q T n/(n : ℝ)
  have nonneg_U : 0 ≤ U := (law_mass_bounds (O \ R) hq).1
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have pos_L : 0 ≤ L := by unfold L groupScale; positivity
  have inv_le : 1 / (n : ℝ) ≤ L := by
    have one : 1 ≤ groupScale q T n := by
      unfold groupScale
      linarith [Real.sqrt_nonneg ((n : ℝ)*(mass q T*(1-mass q T)))]
    exact div_le_div_of_nonneg_right one hn'.le
  have hLight : mass q (O \ K) ≤ U+B := by
    rw [nested_omitted_mass q O R K hKR hR]
    exact add_le_add (le_rfl : U ≤ U) trim
  have hstrong : 256*(1024*groupScale q T n/(n : ℝ)+(10000*B+4097*(U+B)+4096/(n : ℝ))) ≤
      e-mass q T+(root (tailMask T q) (tailMask_nonneg T hq)
        (n : ℝ) (Nat.cast_nonneg n))^2 := by
    change 4000000*(L+B+U) ≤ _ at strong
    have equiv : 1024*groupScale q T n/(n : ℝ) = 1024*L := by dsimp [L]; ring
    have div : (4096 : ℝ)/(n : ℝ) = 4096*(1/(n : ℝ)) := by ring
    rw [equiv, div]
    linarith
  exact regular_upper_from_retained_crossing q hq T K ha (hKR.trans hR) hn
    (by positivity) hΔ hLight hstrong rUnit rNull rAlt

end
end CanonneQuantile
