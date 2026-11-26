import Readout
import Radix
import HeadInterpolation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! End-to-end constructive upper representation in a finite value
coordinate type, independent of the softmax interpolation layer. -/
namespace AttentionUpper

open scoped BigOperators

theorem radix_exactBasis {H b p D : Nat} (heads : 0 < H) (base : 0 < b)
    (covers : H ≤ b^p) (adequate : 2*(p*(b-1)) ≤ D+2) :
    ExactBasis (fun x : {j : Nat // j ∈ radixBasis H b p} => x.val) H D := by
  refine ⟨fun x => radixBasis_bounded H b p x.val x.property, ?_⟩
  intro e
  obtain ⟨words, len, sum, included⟩ := radixBasis_cover heads base covers adequate
    (show e.val ≤ H*D from Nat.le_of_lt_succ e.isLt)
  subst D
  let pick : Fin words.length → {j : Nat // j ∈ radixBasis H b p} := fun i =>
    ⟨words[i], included _ (List.getElem_mem i.isLt)⟩
  refine ⟨pick, ?_⟩
  change (∑ i : Fin words.length, words.get i) = e.val
  rw [← Fin.sum_ofFn, List.ofFn_get]
  exact sum

theorem full_exponent_exactBasis (H D : Nat) :
    ExactBasis (fun i : Fin (H+1) => i.val) H D := by
  refine ⟨fun i => Nat.le_of_lt_succ i.isLt, ?_⟩
  have fill (n k : Nat) (bound : k ≤ H*n) :
      ∃ pick : Fin n → Fin (H+1), ∑ j, (pick j).val = k := by
    induction n generalizing k with
    | zero =>
      have eq : k = 0 := by simpa using bound
      exact ⟨Fin.elim0, by simp [eq]⟩
    | succ n ih =>
      let head := min H k
      have few : k-head ≤ H*n := by
        by_cases small : k ≤ H
        · simp [head, Nat.min_eq_right small]
        · simp only [head, Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge small))]
          simp only [Nat.mul_succ] at bound
          omega
      obtain ⟨xs, sum⟩ := ih (k-head) few
      let picked : Fin (H+1) := ⟨head, Nat.lt_succ_of_le (min_le_left ..)⟩
      refine ⟨Fin.cons picked xs, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sum, picked]
      exact Nat.add_sub_of_le (min_le_right ..)
  exact fun e => fill D e.val (Nat.le_of_lt_succ e.isLt)

/-- For each constructive basis in Lemma 14, one finite list of degree-H
feature polynomials works for all degree-at-most-HD targets. -/
theorem radix_shared_representation {H b p D : Nat} (heads : 0 < H) (base : 0 < b)
    (covers : H ≤ b^p) (adequate : 2*(p*(b-1)) ≤ D+2) :
    ∃ d : Nat, 0 < d ∧ d ≤ 2*p+2 ∧ ∃ exponent : Fin d → Nat,
      (∀ i, (features exponent i : Polynomial ℝ).natDegree ≤ H) ∧
      ∀ F : Polynomial ℝ, F.natDegree ≤ H*D →
        ∃ g : MvPolynomial (Fin d) ℝ, g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
          MvPolynomial.aeval (features exponent) g = F := by
  classical
  let Basis := {j : Nat // j ∈ radixBasis H b p}
  let d := Fintype.card Basis
  let index : Basis ≃ Fin d := Fintype.equivFin Basis
  let exponent : Fin d → Nat := fun j => (index.symm j).val
  have exactOld := radix_exactBasis heads base covers adequate
  have exactNew : ExactBasis exponent H D := by
    refine ⟨fun j => exactOld.1 (index.symm j), ?_⟩
    intro e
    obtain ⟨pick, spec⟩ := exactOld.2 e
    refine ⟨index ∘ pick, ?_⟩
    simpa [exponent, Function.comp_def] using spec
  have zeroIn : 0 ∈ radixBasis H b p := by simp [radixBasis, withComplements]
  have present : Nonempty Basis := ⟨⟨0, zeroIn⟩⟩
  refine ⟨d, Fintype.card_pos, ?_, exponent, shared_features exactNew⟩
  simpa [d, Basis] using radixBasis_card_le H b p

/-- One shared H-head layer realizes the same features for every input; for
each target polynomial one fixed homogeneous readout works for all t≥0. -/
theorem radix_shared_attention {H b p D : Nat} (heads : 0 < H) (base : 0 < b)
    (covers : H ≤ b^p) (adequate : 2*(p*(b-1)) ≤ D+2) :
    ∃ d : Nat, 0 < d ∧ d ≤ 2*p+2 ∧
      ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ),
        (∀ h, 0 < r h) ∧
        ∀ F : Polynomial ℝ, F.natDegree ≤ H*D →
          ∃ g : MvPolynomial (Fin d) ℝ, g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
            ∀ t : ℝ, 0 ≤ t →
              (0 < MvPolynomial.eval (fun i => AttentionModel.heads r v0 v1 i t) g ↔ 0 < F.eval t) := by
  obtain ⟨d,hd,dim,exponent,degree,rep⟩ := radix_shared_representation heads base covers adequate
  let s : Fin H → ℝ := fun i => (i.val : ℝ)+1
  have hinj : Function.Injective s := by
    intro i j eq
    have same : (i.val : ℝ) = j.val := by dsimp [s] at eq; linarith
    exact Fin.ext (by exact_mod_cast same)
  have hpos : ∀ i, 0 < s i := by intro i; dsimp [s]; positivity
  obtain ⟨r,v0,v1,positive,shared⟩ := AttentionInterpolation.shared_heads s hinj hpos
    (features exponent) degree heads
  refine ⟨d,hd,dim,r,v0,v1,positive,?_⟩
  intro F hF
  obtain ⟨g,hom,gdeg,realizes⟩ := rep F hF
  refine ⟨g,hom,gdeg,?_⟩
  intro t ht
  have den : 0 < (AttentionWindows.rootPoly s).eval t := by
    simp only [AttentionWindows.rootPoly, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_pos (fun i _ => add_pos_of_nonneg_of_pos ht (hpos i))
  have vector : (fun i => AttentionModel.heads r v0 v1 i t) =
      (fun i => (features exponent i : Polynomial ℝ).eval t / (AttentionWindows.rootPoly s).eval t) := by
    funext i
    exact shared i t ht
  rw [vector]
  exact readout_strict_sign exponent hom realizes den

/-- Normalized Hamming weight; the same heads and readout are shared over
all bit vectors, and no positional information enters the construction. -/
noncomputable def bitWeight {n : Nat} (bits : Fin n → Bool) : ℝ :=
  (∑ i, if bits i then (1 : ℝ) else 0) / n

theorem bitWeight_nonneg {n : Nat} (bits : Fin n → Bool) : 0 ≤ bitWeight bits := by
  unfold bitWeight
  apply div_nonneg _ (Nat.cast_nonneg n)
  apply Finset.sum_nonneg
  intro i _
  split <;> norm_num

theorem bitWeight_le_one {n : Nat} (positive : 0<n) (bits : Fin n → Bool) : bitWeight bits ≤ 1 := by
  unfold bitWeight
  apply (div_le_one (by exact_mod_cast positive : (0 : ℝ) < n)).2
  have h : (∑ i : Fin n, if bits i then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    split <;> norm_num
  simpa using h

theorem radix_shared_attention_bits {H b p D : Nat} (heads : 0 < H) (base : 0 < b)
    (covers : H ≤ b^p) (adequate : 2*(p*(b-1)) ≤ D+2) :
    ∃ d : Nat, 0 < d ∧ d ≤ 2*p+2 ∧
      ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ),
        (∀ h, 0 < r h) ∧
        ∀ F : Polynomial ℝ, F.natDegree ≤ H*D →
          ∃ g : MvPolynomial (Fin d) ℝ, g.IsHomogeneous D ∧ g.totalDegree ≤ D ∧
            ∀ (n : Nat) (bits : Fin n → Bool), 0 < n →
              (0 < MvPolynomial.eval (fun i => AttentionModel.heads r v0 v1 i (bitWeight bits)) g ↔
                0 < F.eval (bitWeight bits)) := by
  obtain ⟨d,hd,dim,r,v0,v1,pos,all⟩ := radix_shared_attention heads base covers adequate
  refine ⟨d,hd,dim,r,v0,v1,pos,?_⟩
  intro F hF
  obtain ⟨g,hom,gdeg,valid⟩ := all F hF
  exact ⟨g,hom,gdeg,fun _ bits _ => valid (bitWeight bits) (bitWeight_nonneg bits)⟩

#print axioms radix_shared_attention_bits

#print axioms radix_shared_attention

#print axioms radix_exactBasis
#print axioms full_exponent_exactBasis
#print axioms radix_shared_representation

end AttentionUpper
