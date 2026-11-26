import GroupedRoots
import GridSigns
import RootWindows

/-! Convert a strict univariate sign profile on a Hamming grid to one root in
exactly each sign-changing gap. The input is a univariate degree-T threshold;
no unproved multivariate symmetrization is assumed. -/
namespace AttentionProfileRoots
open scoped BigOperators
open Polynomial AttentionGrid AttentionWindows
noncomputable section

variable {n : Nat}

def switches (n : Nat) (p : Polynomial ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => p.eval (grid n i.val) * p.eval (grid n (i.val+1)) < 0

def root (n : Nat) (i : Fin n) : ℝ := halfGrid n i.val

def switchPoly (n : Nat) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∏ i ∈ switches n p, (X - C (root n i))

theorem grid_succ_lt {n : Nat} (hn : 0<n) (i : Fin n) : grid n i.val < grid n (i.val+1) := by
  unfold grid
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  apply (div_lt_div_iff_of_pos_right hn').2
  push_cast
  linarith

theorem root_between {n : Nat} (hn : 0<n) (i : Fin n) :
    grid n i.val < root n i ∧ root n i < grid n (i.val+1) := by
  exact ⟨grid_lt_halfGrid hn i.val,halfGrid_lt_grid hn (grid_succ_lt hn i)⟩

theorem switchPoly_nonzero_grid {n : Nat} (hn : 0<n) (p : Polynomial ℝ) (k : Nat) :
    (switchPoly n p).eval (grid n k) ≠ 0 := by
  simp only [switchPoly, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr (halfGrid_not_grid hn i.val k)

theorem grid_mono {n a b : Nat} (hn : 0<n) (hab : a ≤ b) : grid n a ≤ grid n b := by
  unfold grid
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0:ℝ)<n)).2
  exact_mod_cast hab

theorem grid_strict {n a b : Nat} (hn : 0<n) (hab : a < b) : grid n a < grid n b := by
  unfold grid
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hn : (0:ℝ)<n)).2
  exact_mod_cast hab

theorem other_factor_pos {n : Nat} (hn : 0<n) (i j : Fin n) (hne : i ≠ j) :
    0 < (grid n i.val - root n j) * (grid n (i.val+1) - root n j) := by
  rcases lt_or_gt_of_ne hne with before | after
  · have ij : i.val+1 ≤ j.val := by omega
    have hright : grid n (i.val+1) < root n j := (grid_mono hn ij).trans_lt (root_between hn j).1
    have hleft : grid n i.val < root n j := (grid_succ_lt hn i).trans hright
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hleft) (sub_neg.mpr hright)
  · have ji : j.val < i.val := after
    have hleft : root n j < grid n i.val := halfGrid_lt_grid hn (grid_strict hn ji)
    have hright : root n j < grid n (i.val+1) := hleft.trans (grid_succ_lt hn i)
    exact mul_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)

theorem own_factor_neg {n : Nat} (hn : 0<n) (i : Fin n) :
    (grid n i.val - root n i) * (grid n (i.val+1) - root n i) < 0 :=
  mul_neg_of_neg_of_pos (sub_neg.mpr (root_between hn i).1) (sub_pos.mpr (root_between hn i).2)

theorem switchPoly_pair_sign {n : Nat} (hn : 0<n) (p : Polynomial ℝ) (i : Fin n) :
    ((switchPoly n p).eval (grid n i.val) * (switchPoly n p).eval (grid n (i.val+1)) < 0) ↔
      i ∈ switches n p := by
  simp only [switchPoly, eval_prod, eval_sub, eval_X, eval_C, ← Finset.prod_mul_distrib]
  by_cases member : i ∈ switches n p
  · rw [← Finset.mul_prod_erase _ _ member]
    have pos : 0 < ∏ j ∈ (switches n p).erase i,
        (grid n i.val - root n j) * (grid n (i.val+1) - root n j) := by
      apply Finset.prod_pos
      intro j hj
      exact other_factor_pos hn i j ((Finset.mem_erase.mp hj).1.symm)
    simp only [member, iff_true]
    exact mul_neg_of_neg_of_pos (own_factor_neg hn i) pos
  · have pos : 0 < ∏ j ∈ switches n p,
        (grid n i.val - root n j) * (grid n (i.val+1) - root n j) := by
      apply Finset.prod_pos
      intro j hj
      have ne : i ≠ j := fun e => member (e ▸ hj)
      exact other_factor_pos hn i j ne
    simp [member,not_lt_of_ge pos.le]

theorem sign_propagation (a b c d : ℝ) (start : 0<a*c)
    (left : a*b<0 ↔ c*d<0) (ab : a*b ≠ 0) (cd : c*d ≠ 0) : 0<b*d := by
  by_cases h : a*b<0
  · have h' := left.mp h
    have pos := mul_pos_of_neg_of_neg h h'
    have product : 0 < (a*c)*(b*d) := by nlinarith
    exact (mul_pos_iff_of_pos_left start).mp product
  · have h' : 0<a*b := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm ab)
    have hc : ¬ c*d<0 := fun hc => h (left.mpr hc)
    have hcd : 0<c*d := lt_of_le_of_ne (le_of_not_gt hc) (Ne.symm cd)
    have pos := mul_pos h' hcd
    have product : 0 < (a*c)*(b*d) := by nlinarith
    exact (mul_pos_iff_of_pos_left start).mp product

def aligned (n : Nat) (p : Polynomial ℝ) : Polynomial ℝ :=
  C (p.eval (grid n 0) * (switchPoly n p).eval (grid n 0)) * switchPoly n p

theorem aligned_agrees {n : Nat} (hn : 0<n) (p : Polynomial ℝ)
    (strict : ∀ k ≤ n, p.eval (grid n k) ≠ 0) :
    ∀ k ≤ n, 0 < p.eval (grid n k) * (aligned n p).eval (grid n k) := by
  have g0 : (switchPoly n p).eval (grid n 0) ≠ 0 := switchPoly_nonzero_grid hn p 0
  have p0 : p.eval (grid n 0) ≠ 0 := strict 0 (by omega)
  let c := p.eval (grid n 0) * (switchPoly n p).eval (grid n 0)
  have cn : c ≠ 0 := mul_ne_zero p0 g0
  have squarePos : 0 < c*c := mul_self_pos.mpr cn
  have evalA (k : Nat) : (aligned n p).eval (grid n k) = c * (switchPoly n p).eval (grid n k) := by
    simp [aligned,c]
  have flip (i : Fin n) :
      (p.eval (grid n i.val) * p.eval (grid n (i.val+1)) < 0) ↔
      ((aligned n p).eval (grid n i.val) * (aligned n p).eval (grid n (i.val+1)) < 0) := by
    rw [evalA,evalA]
    have eq : (c*(switchPoly n p).eval (grid n i.val)) *
        (c*(switchPoly n p).eval (grid n (i.val+1))) =
        (c*c)*((switchPoly n p).eval (grid n i.val)*(switchPoly n p).eval (grid n (i.val+1))) := by ring
    rw [eq]
    have hsign (x : ℝ) : (c*c)*x < 0 ↔ x < 0 := by
      constructor <;> intro h <;> nlinarith
    rw [hsign, switchPoly_pair_sign hn p i]
    simp [switches]
  intro k hk
  induction k with
  | zero =>
    rw [evalA]
    dsimp [c]
    have sq := mul_self_pos.mpr (mul_ne_zero p0 g0)
    nlinarith
  | succ k ih =>
    have before : k<n := by omega
    let i : Fin n := ⟨k,before⟩
    have start := ih (by omega)
    have pn : p.eval (grid n k)*p.eval (grid n (k+1)) ≠ 0 :=
      mul_ne_zero (strict k (by omega)) (strict (k+1) (by omega))
    have gn : (aligned n p).eval (grid n k)*(aligned n p).eval (grid n (k+1)) ≠ 0 := by
      rw [evalA,evalA]
      exact mul_ne_zero (mul_ne_zero cn (switchPoly_nonzero_grid hn p k))
        (mul_ne_zero cn (switchPoly_nonzero_grid hn p (k+1)))
    exact sign_propagation _ _ _ _ start (flip i) pn gn

theorem root_in_switch {n : Nat} (hn : 0<n) (p : Polynomial ℝ)
    (strict : ∀ k ≤ n, p.eval (grid n k) ≠ 0) (i : Fin n) (hi : i ∈ switches n p) :
    ∃ z, grid n i.val < z ∧ z < grid n (i.val+1) ∧ p.eval z = 0 := by
  have jump : p.eval (grid n i.val) * p.eval (grid n (i.val+1)) < 0 := by simpa [switches] using hi
  obtain ⟨z, hz, zero⟩ := root_in_interval p (grid_succ_lt hn i).le jump
  have leftne : z ≠ grid n i.val := by
    intro e
    apply strict i.val (by omega)
    simpa [e] using zero
  have rightne : z ≠ grid n (i.val+1) := by
    intro e
    apply strict (i.val+1) (by omega)
    simpa [e] using zero
  exact ⟨z,lt_of_le_of_ne hz.1 (Ne.symm leftne),lt_of_le_of_ne hz.2 rightne,zero⟩

theorem switches_degree {n : Nat} (hn : 0<n) (p : Polynomial ℝ)
    (strict : ∀ k ≤ n, p.eval (grid n k) ≠ 0) :
    (switches n p).card ≤ p.natDegree := by
  let S := {i : Fin n // i ∈ switches n p}
  have existsRoots : ∀ i : S, ∃ z, grid n i.val.val < z ∧
      z < grid n (i.val.val+1) ∧ p.eval z = 0 :=
    fun i => root_in_switch hn p strict i.val i.property
  choose z left right zero using existsRoots
  have inj : Function.Injective z := by
    intro i j same
    by_contra ne
    have ij : i.val ≠ j.val := by
      intro eq
      exact ne (Subtype.ext eq)
    rcases lt_or_gt_of_ne ij with h | h
    · have order : i.val.val+1 ≤ j.val.val := by omega
      have sep := (right i).trans_le (grid_mono hn order)
      linarith [left j]
    · have order : j.val.val+1 ≤ i.val.val := by omega
      have sep := (right j).trans_le (grid_mono hn order)
      linarith [left i]
  by_contra! tooMany
  have card : p.natDegree < Fintype.card S := by simpa [S] using tooMany
  have zeroPoly := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p inj zero card
  have nonzero := strict 0 (by omega)
  exact nonzero (by simp [zeroPoly])

def switchEnum (n : Nat) (p : Polynomial ℝ) : Fin (switches n p).card ≃ {i // i ∈ switches n p} :=
  (finCongr (Fintype.card_coe (switches n p)).symm).trans (Fintype.equivFin _).symm

def switchRoots (n : Nat) (p : Polynomial ℝ) : Fin (switches n p).card → ℝ :=
  fun i => root n (switchEnum n p i).val

theorem aligned_factored (n : Nat) (p : Polynomial ℝ) :
    aligned n p = C (p.eval (grid n 0) * (switchPoly n p).eval (grid n 0)) *
      ∏ i, AttentionGroupedRoots.factor (switchRoots n p) i := by
  unfold aligned switchPoly
  congr 1
  rw [Finset.prod_subtype (switches n p) (fun _ => Iff.rfl)]
  symm
  exact (switchEnum n p).prod_comp (fun j => X - C (root n j.val))

/-- A strict polynomial threshold on the n+1 Hamming grid values is realized
by H softmax heads with at most D channels and a fixed readout shared by all
bit vectors. The strict sign of every grid value is preserved. -/
theorem threshold_attention {H D n : Nat} (positive : 0<H) (hn : 0<n)
    (p : Polynomial ℝ) (degree : p.natDegree ≤ H*D)
    (strict : ∀ k ≤ n, p.eval (grid n k) ≠ 0) :
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin D → ℝ)
      (g : MvPolynomial (Fin D) ℝ),
      (∀ h, 0 < r h) ∧ g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
      ∀ bits : Fin n → Bool,
        (0 < MvPolynomial.eval (fun i => AttentionModel.heads r v0 v1 i (AttentionUpper.bitWeight bits)) g ↔
          0 < p.eval (AttentionUpper.bitWeight bits)) := by
  let S := switches n p
  have fits : S.card ≤ H*D := (switches_degree hn p strict).trans degree
  let roots := switchRoots n p
  let c := p.eval (grid n 0) * (switchPoly n p).eval (grid n 0)
  obtain ⟨r,v0,v1,g,hr,hom,deg,all⟩ :=
    AttentionGroupedRoots.grouped_attention positive fits roots c
  refine ⟨r,v0,v1,g,hr,hom,deg,?_⟩
  intro bits
  let k := (Finset.univ.filter fun i : Fin n => bits i).card
  have hkn : k ≤ n := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have weight : AttentionUpper.bitWeight bits = grid n k := by
    unfold AttentionUpper.bitWeight grid k
    congr 1
    simp
  rw [weight, all (grid n k) (by unfold grid; positivity)]
  have agreement := aligned_agrees hn p strict k hkn
  have equal : (C c * ∏ i, AttentionGroupedRoots.factor roots i) = aligned n p := by
    simpa [c,roots] using (aligned_factored n p).symm
  rw [equal]
  constructor <;> intro h <;> nlinarith

/-- A symmetric Boolean target presented by a univariate polynomial threshold
on normalized Hamming weights. This definition does not assert that arbitrary
multivariate thresholds have already been symmetrized. -/
def UnivariateThreshold (n T : Nat) (profile : Fin (n+1) → Bool) : Prop :=
  ∃ p : Polynomial ℝ, p.natDegree ≤ T ∧
    (∀ k ≤ n, p.eval (grid n k) ≠ 0) ∧
    ∀ k : Fin (n+1), profile k = true ↔ 0 < p.eval (grid n k.val)

def hamming {n : Nat} (bits : Fin n → Bool) : Fin (n+1) :=
  ⟨(Finset.univ.filter fun i : Fin n => bits i).card,
    Nat.lt_succ_of_le ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))⟩

theorem bitWeight_grid {n : Nat} (bits : Fin n → Bool) :
    AttentionUpper.bitWeight bits = grid n (hamming bits).val := by
  unfold AttentionUpper.bitWeight grid hamming
  congr 1
  simp

theorem univariate_profile_attention {H D n T : Nat} (positive : 0<H) (hn : 0<n)
    (capacity : T ≤ H*D) (profile : Fin (n+1) → Bool)
    (threshold : UnivariateThreshold n T profile) :
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin D → ℝ)
      (g : MvPolynomial (Fin D) ℝ),
      (∀ h, 0 < r h) ∧ g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
      ∀ bits : Fin n → Bool,
        (0 < MvPolynomial.eval (fun i => AttentionModel.heads r v0 v1 i (AttentionUpper.bitWeight bits)) g ↔
          profile (hamming bits) = true) := by
  obtain ⟨p,degree,strict,correct⟩ := threshold
  obtain ⟨r,v0,v1,g,hr,hom,deg,all⟩ := threshold_attention positive hn p (degree.trans capacity) strict
  refine ⟨r,v0,v1,g,hr,hom,deg,?_⟩
  intro bits
  rw [all bits, bitWeight_grid]
  exact (correct (hamming bits)).symm

#print axioms univariate_profile_attention
#print axioms threshold_attention

end
end AttentionProfileRoots
