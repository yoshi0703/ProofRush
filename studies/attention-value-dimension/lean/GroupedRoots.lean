import ConstructiveUpper

/-! Exact real-root factorization upper bound. Roots may repeat; each index is
assigned to one head-sized group, and one fixed product readout works on all
inputs for that target. -/
namespace AttentionGroupedRoots
open scoped BigOperators
open Polynomial AttentionModel AttentionInterpolation AttentionWindows
noncomputable section

variable {H D N : Nat}

def bucket (positive : 0 < H) (fits : N ≤ H*D) (i : Fin N) : Fin D :=
  ⟨i.val/H, (Nat.div_lt_iff_lt_mul positive).2 (by nlinarith [i.isLt])⟩

def group (positive : 0 < H) (fits : N ≤ H*D) (j : Fin D) : Finset (Fin N) :=
  Finset.univ.filter (fun i => bucket positive fits i = j)

theorem group_card (positive : 0 < H) (fits : N ≤ H*D) (j : Fin D) :
    (group positive fits j).card ≤ H := by
  let index : Fin N → Fin H := fun i => ⟨i.val%H, Nat.mod_lt _ positive⟩
  have inject : Set.InjOn index (group positive fits j) := by
    intro a ha b hb same
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hd : a.val/H = b.val/H := by
      have e : bucket positive fits a = bucket positive fits b := ha'.trans hb'.symm
      exact congrArg Fin.val e
    have hm : a.val%H = b.val%H := congrArg Fin.val same
    have ea := Nat.div_add_mod a.val H
    have eb := Nat.div_add_mod b.val H
    apply Fin.ext
    calc
      a.val = H*(a.val/H)+a.val%H := ea.symm
      _ = H*(b.val/H)+b.val%H := by rw [hd,hm]
      _ = b.val := eb
  have h := Finset.card_le_card_of_injOn index (s:=group positive fits j) (t:=Finset.univ)
    (fun _ _ => Finset.mem_univ _) inject
  simpa using h

def factor (root : Fin N → ℝ) (i : Fin N) : Polynomial ℝ := X - C (root i)

def feature (positive : 0 < H) (fits : N ≤ H*D) (root : Fin N → ℝ) (j : Fin D) : Polynomial ℝ :=
  ∏ i ∈ group positive fits j, factor root i

theorem feature_degree (positive : 0 < H) (fits : N ≤ H*D) (root : Fin N → ℝ) (j : Fin D) :
    (feature positive fits root j).natDegree ≤ H := by
  unfold feature
  calc
    _ ≤ ∑ i ∈ group positive fits j, (factor root i).natDegree := Polynomial.natDegree_prod_le _ _
    _ = (group positive fits j).card := by simp [factor]
    _ ≤ H := group_card positive fits j

theorem features_product (positive : 0 < H) (fits : N ≤ H*D) (root : Fin N → ℝ) :
    (∏ j, feature positive fits root j) = ∏ i, factor root i := by
  exact Finset.prod_fiberwise Finset.univ (bucket positive fits) (factor root)

def productReadout (c : ℝ) : MvPolynomial (Fin D) ℝ :=
  MvPolynomial.C c * ∏ j, MvPolynomial.X j

theorem productReadout_hom (c : ℝ) : (productReadout (D:=D) c).IsHomogeneous D := by
  unfold productReadout
  have prodHom : (∏ j : Fin D, MvPolynomial.X j : MvPolynomial (Fin D) ℝ).IsHomogeneous D := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun j : Fin D => (MvPolynomial.X j : MvPolynomial (Fin D) ℝ))
      (fun _ => 1) (fun j _ => MvPolynomial.isHomogeneous_X ℝ j)
  simpa using (MvPolynomial.isHomogeneous_C (Fin D) c).mul prodHom

theorem exact_polynomial (positive : 0 < H) (fits : N ≤ H*D) (root : Fin N → ℝ) (c : ℝ) :
    MvPolynomial.aeval (feature positive fits root) (productReadout (D:=D) c) =
      C c * ∏ i, factor root i := by
  simp [productReadout, map_mul, map_prod, MvPolynomial.aeval_X, features_product]

/-- The original H-head softmax layer and a single degree-D product readout
exactly sign-represent the given real-root polynomial for every t≥0. -/
theorem grouped_attention (positive : 0 < H) (fits : N ≤ H*D)
    (root : Fin N → ℝ) (c : ℝ) :
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin D → ℝ)
      (g : MvPolynomial (Fin D) ℝ),
      (∀ h, 0 < r h) ∧ g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
      ∀ t : ℝ, 0 ≤ t →
        (0 < MvPolynomial.eval (fun i => heads r v0 v1 i t) g ↔
          0 < (C c * ∏ i, factor root i).eval t) := by
  let feat := feature positive fits root
  let F : Polynomial ℝ := C c * ∏ i, factor root i
  let s : Fin H → ℝ := fun i => (i.val : ℝ)+1
  have hinj : Function.Injective s := by
    intro i j eq
    have same : (i.val : ℝ) = j.val := by dsimp [s] at eq; linarith
    exact Fin.ext (by exact_mod_cast same)
  have spos : ∀ i, 0 < s i := by intro i; dsimp [s]; positivity
  obtain ⟨r,v0,v1,hr,share⟩ := shared_heads s hinj spos feat
    (feature_degree positive fits root) positive
  let g := productReadout (D:=D) c
  have hom : g.IsHomogeneous D := productReadout_hom c
  have realize : MvPolynomial.aeval feat g = F := exact_polynomial positive fits root c
  refine ⟨r,v0,v1,g,hr,hom,hom.totalDegree_le,?_⟩
  intro t ht
  have den : 0 < (rootPoly s).eval t := by
    simp only [rootPoly, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_pos (fun i _ => add_pos_of_nonneg_of_pos ht (spos i))
  have vector : (fun i => heads r v0 v1 i t) =
      (fun i => (feat i).eval t / (rootPoly s).eval t) := by
    funext i
    exact share i t ht
  let e : Polynomial ℝ →ₐ[ℝ] ℝ := Polynomial.aeval t
  have value := congrArg e realize
  rw [MvPolynomial.comp_aeval_apply] at value
  have base : MvPolynomial.eval (fun i => (feat i).eval t) g = F.eval t := by
    simpa only [e, MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval] using value
  have scale : (fun i => (feat i).eval t / (rootPoly s).eval t) =
      ((rootPoly s).eval t)⁻¹ • (fun i => (feat i).eval t) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [vector, scale, hom.eval_smul, base]
  exact mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr den) D)

theorem grouped_attention_bits (positive : 0 < H) (fits : N ≤ H*D)
    (root : Fin N → ℝ) (c : ℝ) :
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin D → ℝ)
      (g : MvPolynomial (Fin D) ℝ),
      (∀ h, 0 < r h) ∧ g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
      ∀ (n : Nat) (bits : Fin n → Bool), 0 < n →
        (0 < MvPolynomial.eval (fun i => heads r v0 v1 i (AttentionUpper.bitWeight bits)) g ↔
          0 < (C c * ∏ i, factor root i).eval (AttentionUpper.bitWeight bits)) := by
  obtain ⟨r,v0,v1,g,hr,hom,degree,all⟩ := grouped_attention positive fits root c
  exact ⟨r,v0,v1,g,hr,hom,degree,fun _ bits _ =>
    all (AttentionUpper.bitWeight bits) (AttentionUpper.bitWeight_nonneg bits)⟩

#print axioms grouped_attention_bits
#print axioms grouped_attention

end
end AttentionGroupedRoots
