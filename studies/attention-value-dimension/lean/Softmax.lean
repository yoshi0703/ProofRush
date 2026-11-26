import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Normalized binary-token softmax heads and their common rational chart.
The variable t is the normalized Hamming weight. -/
noncomputable section

namespace AttentionModel
open scoped BigOperators
open Polynomial

variable {H d : Nat}

def headDen (r t : ℝ) : ℝ := (1-t) + r*t
def headNum (r v0 v1 t : ℝ) : ℝ := (1-t)*v0 + r*t*v1

def head (r v0 v1 t : ℝ) : ℝ := headNum r v0 v1 t / headDen r t

def commonDen (r : Fin H → ℝ) (t : ℝ) : ℝ :=
  ∏ h, headDen (r h) t

def commonNum (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (i : Fin d) (t : ℝ) : ℝ :=
  ∑ h, headNum (r h) (v0 h i) (v1 h i) t *
    ∏ j ∈ Finset.univ.erase h, headDen (r j) t

def heads (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (i : Fin d) (t : ℝ) : ℝ :=
  ∑ h, head (r h) (v0 h i) (v1 h i) t

theorem headDen_pos (r t : ℝ) (hr : 0 < r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < headDen r t := by
  unfold headDen
  have hrt : 0 ≤ r*t := mul_nonneg (le_of_lt hr) ht0
  by_cases h : t = 0
  · simp [h]
  · have : 0 < r*t := mul_pos hr (lt_of_le_of_ne ht0 (Ne.symm h))
    linarith

theorem commonDen_pos (r : Fin H → ℝ) (t : ℝ)
    (hr : ∀ h, 0 < r h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < commonDen r t := by
  unfold commonDen
  exact Finset.prod_pos (fun h _ => headDen_pos (r h) t (hr h) ht0 ht1)

theorem heads_common (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ)
    (i : Fin d) (t : ℝ) (hn : ∀ h, headDen (r h) t ≠ 0) :
    heads r v0 v1 i t = commonNum r v0 v1 i t / commonDen r t := by
  unfold heads head commonNum commonDen
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  have hp : (∏ j ∈ Finset.univ.erase h, headDen (r j) t) * headDen (r h) t =
      ∏ j, headDen (r j) t := Finset.prod_erase_mul _ _ (Finset.mem_univ h)
  have hb : (∏ j ∈ Finset.univ.erase h, headDen (r j) t) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hn j)
  rw [← hp]
  field_simp [hn h, hb]

def denPoly (r : ℝ) : Polynomial ℝ := 1 + Polynomial.C (r-1) * Polynomial.X

def numPoly (r v0 v1 : ℝ) : Polynomial ℝ :=
  Polynomial.C v0 + Polynomial.C (r*v1-v0) * Polynomial.X

def qPoly (r : Fin H → ℝ) : Polynomial ℝ := ∏ h, denPoly (r h)

def pPoly (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (i : Fin d) : Polynomial ℝ :=
  ∑ h, numPoly (r h) (v0 h i) (v1 h i) * ∏ j ∈ Finset.univ.erase h, denPoly (r j)

theorem eval_denPoly (r t : ℝ) : (denPoly r).eval t = headDen r t := by
  simp [denPoly, headDen]
  ring

theorem eval_numPoly (r v0 v1 t : ℝ) : (numPoly r v0 v1).eval t = headNum r v0 v1 t := by
  simp [numPoly, headNum]
  ring

theorem eval_qPoly (r : Fin H → ℝ) (t : ℝ) : (qPoly r).eval t = commonDen r t := by
  change (Polynomial.evalRingHom t) (qPoly r) = commonDen r t
  simp [qPoly, commonDen, map_prod, eval_denPoly]

theorem eval_pPoly (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (i : Fin d) (t : ℝ) :
    (pPoly r v0 v1 i).eval t = commonNum r v0 v1 i t := by
  change (Polynomial.evalRingHom t) (pPoly r v0 v1 i) = commonNum r v0 v1 i t
  simp [pPoly, commonNum, map_sum, Polynomial.eval_prod, eval_denPoly, eval_numPoly]

theorem q_at_zero (r : Fin H → ℝ) : (qPoly r).eval 0 = 1 := by
  simp [eval_qPoly, commonDen, headDen]

theorem denPoly_degree (r : ℝ) : (denPoly r).natDegree ≤ 1 := by
  unfold denPoly
  have h := Polynomial.natDegree_add_le (1 : Polynomial ℝ) (Polynomial.C (r-1) * Polynomial.X)
  have hm : (Polynomial.C (r-1) * Polynomial.X : Polynomial ℝ).natDegree ≤
      (Polynomial.C (r-1) : Polynomial ℝ).natDegree + (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_one, Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] at h hm
  exact h.trans (max_le (by omega) hm)

theorem numPoly_degree (r v0 v1 : ℝ) : (numPoly r v0 v1).natDegree ≤ 1 := by
  unfold numPoly
  have h := Polynomial.natDegree_add_le (Polynomial.C v0) (Polynomial.C (r*v1-v0) * Polynomial.X)
  have hm : (Polynomial.C (r*v1-v0) * Polynomial.X : Polynomial ℝ).natDegree ≤
      (Polynomial.C (r*v1-v0) : Polynomial ℝ).natDegree + (Polynomial.X : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] at h hm
  exact h.trans (max_le (by omega) hm)

theorem qPoly_degree (r : Fin H → ℝ) : (qPoly r).natDegree ≤ H := by
  unfold qPoly
  calc
    _ ≤ ∑ h : Fin H, (denPoly (r h)).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _h : Fin H, 1 := Finset.sum_le_sum (fun h _ => denPoly_degree (r h))
    _ = H := by simp

theorem pPoly_degree (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (i : Fin d) :
    (pPoly r v0 v1 i).natDegree ≤ H := by
  unfold pPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro h _
  calc
    _ ≤ (numPoly (r h) (v0 h i) (v1 h i)).natDegree +
        (∏ j ∈ Finset.univ.erase h, denPoly (r j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 1 + ∑ _j ∈ Finset.univ.erase h, 1 := by
      gcongr
      · exact numPoly_degree _ _ _
      · exact (Polynomial.natDegree_prod_le _ _).trans
          (Finset.sum_le_sum (fun j _ => denPoly_degree (r j)))
    _ = H := by
      simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ, Finset.card_fin, nsmul_eq_mul, mul_one]
      have hh : 0 < H := Fin.pos h
      norm_cast
      omega

end AttentionModel

end
