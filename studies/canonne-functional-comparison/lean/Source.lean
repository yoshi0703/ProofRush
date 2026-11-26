import Cutoff
import Results
import Mathlib.Tactic.FieldSimp

namespace Canonne

noncomputable section

/-- The direct comparison at two radii, using the canonical least cutoff at
    each radius. -/
theorem canonical_two_radius {p : ℕ → ℝ} {s e : ℝ} (hp : Law p)
    (hs : 0 < s) (hse : s < e) (he : e < 1) :
    phi p e hp (lt_trans hs hse) ≤ inverseK p e ∧ inverseK p e ≤
      Real.sqrt (1 + (phi p s hp hs / (4 * (e - s))) ^ 2) :=
  two_radius hp hs hse he (cutIndex_isCut hp hs) (cutIndex_isCut hp (lt_trans hs hse))

/-- Equation (4) of Canonne's MathOverflow question 332062, with explicit
    constants and all three radii as stated there. -/
theorem source_equation_four {p : ℕ → ℝ} {e : ℝ} (hp : Law p)
    (he : 0 < e) (hesmall : e < 1/9) :
    max 1 (phi p (9 * e) hp (by positivity)) ≤ max 1 (inverseK p e) ∧
      max 1 (inverseK p e) ≤ (39/31 : ℝ) * max 1 (phi p (e / 32) hp (by positivity) / e) := by
  have hs : 0 < e / 32 := by positivity
  have hse : e / 32 < e := by linarith
  have heless : e < 1 := by linarith
  obtain ⟨lower, upper⟩ := canonical_two_radius hp hs hse heless
  constructor
  · have hlarge : 0 < 9 * e := by positivity
    have hmono : e ≤ 9 * e := by linarith
    have hϕ : phi p (9 * e) hp hlarge ≤ inverseK p e :=
      (phi_antitone hp he hlarge hmono).trans lower
    exact max_le (le_max_left _ _) (hϕ.trans (le_max_right _ _))
  · let x := phi p (e / 32) hp hs / e
    change max 1 (inverseK p e) ≤ (39/31 : ℝ) * max 1 x
    have hx : 0 ≤ x := div_nonneg (phi_nonneg hp hs) he.le
    have hlin : 0 ≤ 1 + (8/31 : ℝ) * x := by positivity
    have hre : phi p (e / 32) hp hs / (4 * (e - e / 32)) = (8/31 : ℝ) * x := by
      dsimp [x]
      field_simp
      ring
    rw [hre] at upper
    have hroot : Real.sqrt (1 + ((8/31 : ℝ) * x)^2) ≤ 1 + (8/31 : ℝ) * x := by
      apply (Real.sqrt_le_left hlin).2
      nlinarith only [hx]
    calc
      max 1 (inverseK p e) ≤ 1 + (8/31 : ℝ) * x :=
        max_le (by linarith only [hx]) (upper.trans hroot)
      _ ≤ (39/31 : ℝ) * max 1 x := by
        linarith only [le_max_left (1 : ℝ) x, le_max_right (1 : ℝ) x]

/-- The literal positive-parameter version of the same inverse-level
    inequality. -/
theorem source_equation_four_positive {p : ℕ → ℝ} {e : ℝ} (hp : Law p)
    (he : 0 < e) (hesmall : e < 1/9) :
    let psi := sInf {t : ℝ | 0 < t ∧ 1 - e ≤ peetre p t}
    max 1 (phi p (9 * e) hp (by positivity)) ≤ max 1 psi ∧
      max 1 psi ≤ (39/31 : ℝ) * max 1 (phi p (e / 32) hp (by positivity) / e) := by
  dsimp only
  rw [← inverseK_eq_positive_level hp (show e < 1 by linarith)]
  exact source_equation_four hp he hesmall

private def pointAtom (i : ℕ) : ℝ := if i = 0 then 1 else 0

private theorem pointAtom_law : Law pointAtom := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [pointAtom, apply_ite]
  · intro i j hij
    by_cases hj : j = 0
    · have hi : i = 0 := Nat.eq_zero_of_le_zero (hj ▸ hij)
      simp [pointAtom, hi, hj]
    · simp [pointAtom, hj, apply_ite]
  · have h : HasSum (fun i : ℕ => if i = 0 then (1 : ℝ) else 0) 1 :=
      hasSum_ite_eq 0 1
    exact h

private theorem pointAtom_capture (z : ℕ → ℝ) :
    (∑' i, pointAtom i * z i) = z 0 := by
  rw [tsum_eq_single 0 (fun i hi => by simp [pointAtom, hi])]
  simp [pointAtom]

/-- Pinelis' point-mass example gives zero truncated quasinorm but a
    positive inverse, so a bare multiplicative upper bound must fail. -/
theorem point_atom_example {e : ℝ} (he : 0 < e) (he' : e < 1) :
    ∃ p : ℕ → ℝ, ∃ hp : Law p, phi p e hp he = 0 ∧ inverseK p e = 1-e := by
  have hc : cutIndex pointAtom_law he = 0 := by
    apply Nat.eq_zero_of_le_zero (cutIndex_le_of_capture pointAtom_law he ?_)
    simpa [pointAtom] using (sub_le_self (1 : ℝ) he.le)
  have hphi : phi pointAtom e pointAtom_law he = 0 := by
    rw [phi, hc]
    simp [phiAt, powerSum, Real.zero_rpow (by norm_num : (3/2 : ℝ) ≠ 0)]
  let z : ℕ → ℝ := fun i => if i = 0 then 1-e else 0
  have hs : Summable (fun i => z i ^ 2) :=
    summable_of_ne_finset_zero (s := {0}) (fun i hi => by
      simp [z, Finset.notMem_singleton.mp hi])
  have hnonneg : 0 ≤ 1-e := sub_nonneg.mpr he'.le
  have zfeas : Feasible pointAtom e z := by
    refine ⟨?_, ?_, hs, ?_⟩
    · intro i
      simp [z, apply_ite, hnonneg]
    · intro i
      by_cases hi : i = 0
      · simpa [z, hi] using (sub_le_self (1 : ℝ) he.le)
      · simp [z, hi]
    · rw [pointAtom_capture]
      simp [z]
  have henergy : ell2 z = 1-e := by
    unfold ell2
    rw [tsum_eq_single 0 (fun i hi => by simp [z, hi])]
    simpa [z] using Real.sqrt_sq hnonneg
  have upper := inverseK_le_ell2 pointAtom_law zfeas
  rw [henergy] at upper
  obtain ⟨w, wf, wh, _⟩ := inverse_attained pointAtom_law he he'
  have left := wf.capture
  rw [pointAtom_capture] at left
  have right : w 0 ≤ ell2 w := by
    unfold ell2
    have h := Real.sqrt_le_sqrt (wf.energy.le_tsum 0 (fun i _ => sq_nonneg (w i)))
    rwa [Real.sqrt_sq (wf.nonneg 0)] at h
  exact ⟨pointAtom, pointAtom_law, hphi, le_antisymm upper (wh ▸ left.trans right)⟩

end

end Canonne
