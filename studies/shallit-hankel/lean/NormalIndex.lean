import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The next nonsingular Hankel order

A monic recurrence that first fails at a known residual index determines
the next nonsingular leading Hankel minor. No property of a specific word
is used in this file.
-/

namespace ShallitNormalIndex

open scoped BigOperators Matrix
open Matrix

variable {R : Type*} [CommRing R]

/-- The square Hankel matrix of size `n` for a sequence of moments. -/
def hankel (m : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => m ((i : ℕ) + j)

/-- Residual of the monic relation with lower-degree coefficients `c`. -/
def residual (m : ℕ → R) {k : ℕ} (c : Fin k → R) (i : ℕ) : R :=
  m (i + k) + ∑ l : Fin k, c l * m (i + l)

/-- A unit lower triangular change of rows replaces row `k+i` by the
recurrence combination starting at row `i`. -/
def rowTransform {k : ℕ} (c : Fin k → R) (d : ℕ) :
    Matrix (Fin (k + d)) (Fin (k + d)) R :=
  (1 : Matrix (Fin (k + d)) (Fin (k + d)) R) +
    Matrix.of fun (i j : Fin (k + d)) =>
    if k ≤ (i : ℕ) then
      ∑ l : Fin k, if (j : ℕ) = (i : ℕ) - k + l then c l else 0
    else 0

private theorem lowerTerms_zero {k d : ℕ} (c : Fin k → R)
    (i j : Fin (k + d)) (hij : (i : ℕ) ≤ j) :
    (if k ≤ (i : ℕ) then
      ∑ l : Fin k, if (j : ℕ) = (i : ℕ) - k + l then c l else 0
    else 0) = 0 := by
  split_ifs with hi
  · apply Finset.sum_eq_zero
    intro l _
    have hl := l.isLt
    exact ite_eq_right (by omega)
  · rfl

theorem det_rowTransform {k : ℕ} (c : Fin k → R) (d : ℕ) :
    (rowTransform c d).det = 1 := by
  classical
  have ht : (rowTransform c d).IsLowerTriangular := by
    intro i j h
    have hv : (i : ℕ) < j := h
    simp only [rowTransform, Matrix.add_apply, of_apply]
    rw [lowerTerms_zero c i j hv.le, add_zero]
    have hne : i ≠ j := ne_of_lt (show i < j from hv)
    simp [hne]
  rw [det_of_isLowerTriangular _ ht]
  apply Finset.prod_eq_one
  intro i _
  simp [rowTransform, lowerTerms_zero c i i le_rfl]

private theorem sum_selected {k d : ℕ} (m : ℕ → R) (c : Fin k → R)
    (i j : Fin (k + d)) (hi : k ≤ (i : ℕ)) (l : Fin k) :
    (∑ r : Fin (k + d),
        (if (r : ℕ) = (i : ℕ) - k + l then c l else 0) *
          m ((r : ℕ) + j)) =
      c l * m ((i : ℕ) - k + l + j) := by
  let r₀ : Fin (k+d) := ⟨(i : ℕ) - k + l, by
    have hi' := i.isLt
    have hl' := l.isLt
    omega⟩
  rw [Finset.sum_eq_single r₀]
  · simp [r₀]
  · intro r _ hne
    have hv : (r : ℕ) ≠ (i : ℕ) - k + l := by
      intro he
      apply hne
      exact Fin.ext he
    simp [hv]
  · simp

private theorem transform_apply {k d : ℕ} (m : ℕ → R) (c : Fin k → R)
    (i j : Fin (k + d)) :
    (rowTransform c d * hankel m (k + d)) i j =
      if (i : ℕ) < k then m ((i : ℕ) + j)
      else residual m c ((i : ℕ) - k + j) := by
  classical
  unfold rowTransform
  rw [add_mul, one_mul, Matrix.add_apply]
  simp only [hankel, of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases hi : (i : ℕ) < k
  · simp [hi, Nat.not_le_of_lt hi]
  · have hki := Nat.le_of_not_gt hi
    simp only [hki, ite_true, hi, ite_false]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [sum_selected m c i j hki]
    unfold residual
    have hk : (i : ℕ) - k + (j : ℕ) + k = (i : ℕ) + j := by omega
    rw [hk]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [show (i : ℕ) - k + (l : ℕ) + j = (i : ℕ) - k + (j : ℕ) + l by omega]

private theorem det_split {k d : ℕ} (m : ℕ → R) (c : Fin k → R)
    (hz : ∀ i : ℕ, i < k + d - 1 → residual m c i = 0) :
    (hankel m (k + d)).det =
      (hankel m k).det *
        (Matrix.of (fun (i j : Fin d) => residual m c ((i : ℕ) + k + j))).det := by
  classical
  let e : Fin k ⊕ Fin d ≃ Fin (k+d) := finSumFinEquiv
  let M := rowTransform c d * hankel m (k+d)
  let B : Matrix (Fin k) (Fin d) R :=
    Matrix.of fun i j => m ((i : ℕ) + (k + j))
  let D : Matrix (Fin d) (Fin d) R :=
    Matrix.of fun i j => residual m c ((i : ℕ) + k + j)
  have hb : M.submatrix e e = Matrix.fromBlocks (hankel m k) B 0 D := by
    ext i j
    rw [submatrix_apply]
    change (rowTransform c d * hankel m (k+d)) (e i) (e j) =
      Matrix.fromBlocks (hankel m k) B 0 D i j
    rw [transform_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp [e, i.isLt, hankel]
    · simp [e, i.isLt, B]
    · simp only [e, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Fin.val_natAdd, Fin.val_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      change (if k + (i : ℕ) < k then m (k + i + j) else
        residual m c (k + i - k + j)) = 0
      rw [ite_eq_right (show ¬ k + (i : ℕ) < k by omega), Nat.add_sub_cancel_left]
      apply hz
      have hi := i.isLt
      have hj := j.isLt
      omega
    · simp only [e, finSumFinEquiv_apply_right, Fin.val_natAdd,
        Matrix.fromBlocks_apply₂₂, D, Matrix.of_apply]
      change (if k + (i : ℕ) < k then m (k + i + (k + j)) else
        residual m c (k + i - k + (k + j))) = residual m c ((i : ℕ) + k + j)
      rw [ite_eq_right (show ¬ k + (i : ℕ) < k by omega), Nat.add_sub_cancel_left]
      congr 1
      omega
  calc
    (hankel m (k+d)).det = M.det := by
      simp [M, det_mul, det_rowTransform]
    _ = (M.submatrix e e).det := (det_submatrix_equiv_self e M).symm
    _ = (hankel m k).det * D.det := by
      rw [hb, det_fromBlocks_zero₂₁]

private theorem det_anti_ne_zero [IsDomain R] {d : ℕ}
    (M : Matrix (Fin d) (Fin d) R)
    (hz : ∀ i j : Fin d, (i : ℕ) + (j : ℕ) < d - 1 → M i j = 0)
    (hn : ∀ i j : Fin d, (i : ℕ) + (j : ℕ) = d - 1 → M i j ≠ 0) :
    M.det ≠ 0 := by
  classical
  let B := M.submatrix id Fin.revPerm
  have ht : B.IsLowerTriangular := by
    intro i j hij
    exact hz i j.rev (by
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      simp only [Fin.val_rev]
      omega)
  have hnz : B.det ≠ 0 := by
    rw [det_of_isLowerTriangular B ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hn i i.rev (by
      have hi := i.isLt
      simp only [Fin.val_rev]
      omega)
  intro hd
  exact hnz (by simp [B, det_permute', hd])

/-- If the first nonzero monic-recurrence residual is at `k+d-1`,
a nonsingular size `k` has its next nonsingular size at `k+d`. -/
theorem next_nonsingular [IsDomain R] {k d : ℕ}
    (m : ℕ → R) (c : Fin k → R) (hd : 0 < d)
    (hk : (hankel m k).det ≠ 0)
    (hz : ∀ i : ℕ, i < k + d - 1 → residual m c i = 0)
    (hn : residual m c (k + d - 1) ≠ 0) :
    (hankel m (k+d)).det ≠ 0 ∧
      ∀ e : ℕ, 0 < e → e < d → (hankel m (k+e)).det = 0 := by
  constructor
  · rw [det_split m c hz]
    apply mul_ne_zero hk
    apply det_anti_ne_zero
    · intro i j hij
      change residual m c ((i : ℕ) + k + j) = 0
      apply hz
      omega
    · intro i j hij
      change residual m c ((i : ℕ) + k + j) ≠ 0
      rwa [show (i : ℕ) + k + (j : ℕ) = k + d - 1 by omega]
  · intro e he hed
    rw [det_split m c (d := e) (fun i hi => hz i (by omega))]
    apply mul_eq_zero_of_right
    apply det_eq_zero_of_row_eq_zero (⟨0, he⟩ : Fin e)
    intro j
    change residual m c (0 + k + j) = 0
    apply hz
    have hj := j.isLt
    omega

section Field

variable {F : Type*} [Field F]

/-- The invertible leading moment matrix determines the monic annihilator
of the first `k` residuals. -/
theorem exists_residual_zero {k : ℕ} (m : ℕ → F)
    (hk : (hankel m k).det ≠ 0) :
    ∃ c : Fin k → F, ∀ i : ℕ, i < k → residual m c i = 0 := by
  classical
  let A := hankel m k
  let b : Fin k → F := fun i => -m ((i : ℕ) + k)
  let c := A⁻¹ *ᵥ b
  have hAc : A *ᵥ c = b := by
    change A *ᵥ (A⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hk),
      Matrix.one_mulVec]
  refine ⟨c, fun i hi => ?_⟩
  have h := congrFun hAc (⟨i, hi⟩ : Fin k)
  change (∑ l : Fin k, m (i + l) * c l) = -m (i + k) at h
  unfold residual
  simp_rw [mul_comm (c _) (m _)]
  rw [h, add_neg_cancel]

/-- A bound on the first failure of every monic order-`k` recurrence
gives a bound on the next nonsingular leading minor. -/
theorem next_nonsingular_le {k B : ℕ} (m : ℕ → F)
    (hk : (hankel m k).det ≠ 0)
    (hB : ∀ c : Fin k → F, ∃ i ≤ B, residual m c i ≠ 0) :
    ∃ q, k < q ∧ q ≤ B+1 ∧ (hankel m q).det ≠ 0 ∧
      ∀ j, k < j → j < q → (hankel m j).det = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_residual_zero m hk
  obtain ⟨i, hiB, hin⟩ := hB c
  have hp : ∃ i, residual m c i ≠ 0 := ⟨i, hin⟩
  let s := Nat.find hp
  have hs : residual m c s ≠ 0 := Nat.find_spec hp
  have hsz (i : ℕ) (hi : i < s) : residual m c i = 0 := by
    by_contra hn
    have hle : s ≤ i := Nat.find_min' hp hn
    omega
  have hks : k ≤ s := by
    by_contra h
    exact hs (hc s (by omega))
  have hsB : s ≤ B := le_trans (Nat.find_min' hp hin) hiB
  let d := s+1-k
  have hd : 0 < d := by dsimp [d]; omega
  have hkd : k+d = s+1 := by dsimp [d]; omega
  have hkd' : k+d-1 = s := by omega
  obtain ⟨hn, hz⟩ := next_nonsingular m c hd hk
    (fun i hi => hsz i (by omega)) (by rwa [hkd'])
  have hnext : (hankel m (s+1)).det ≠ 0 :=
    Eq.mp (congrArg (fun n => (hankel m n).det ≠ 0) hkd) hn
  refine ⟨s+1, by omega, by omega, hnext, fun j hkj hjs => ?_⟩
  have h : k+(j-k) = j := by omega
  rw [← h]
  exact hz (j-k) (by omega) (by omega)

end Field

/-- No two identical factors at displacement `p>0` can have length
`p+1`. This hypothesis is invariant under any injection of alphabets. -/
def NoOverlap {A : Type*} (m : ℕ → A) : Prop :=
  ∀ u p : ℕ, 0 < p → ∃ i ≤ p, m (u+i) ≠ m (u+p+i)

/-- A bound on the factor complexity supplied by a finite code. Codes
are allowed to differ even when the two factors agree. -/
def FactorCode {A : Type*} (m : ℕ → A) (k P : ℕ) : Prop :=
  ∃ code : ℕ → Fin P,
    ∀ u v, code u = code v → ∀ i < k, m (u+i) = m (v+i)

/-- Factor codes for two predecessor lengths give a code for a
factor of a two-uniform morphic word. -/
theorem factorCode_uniform_two {A : Type*} {n k₀ k₁ P Q : ℕ}
    (m : ℕ → A) (image : ℕ → A → A)
    (hm : ∀ u, m u = image (u % 2) (m (u / 2)))
    (he : ∀ j < n, j / 2 < k₀) (ho : ∀ j < n, (j+1) / 2 < k₁)
    (h₀ : FactorCode m k₀ P) (h₁ : FactorCode m k₁ Q) :
    FactorCode m n (P+Q) := by
  obtain ⟨c₀, hc₀⟩ := h₀
  obtain ⟨c₁, hc₁⟩ := h₁
  let f (u : ℕ) : Fin P ⊕ Fin Q :=
    if u % 2 = 0 then Sum.inl (c₀ (u/2)) else Sum.inr (c₁ (u/2))
  let e : Fin P ⊕ Fin Q ≃ Fin (P+Q) := finSumFinEquiv
  refine ⟨e ∘ f, fun u v h j hj => ?_⟩
  have huv : f u = f v := e.injective h
  unfold f at huv
  by_cases hu : u % 2 = 0 <;> by_cases hv : v % 2 = 0
  · have hc : c₀ (u/2) = c₀ (v/2) := by simpa [hu, hv] using huv
    have hsame := hc₀ _ _ hc (j/2) (he _ hj)
    have hdivu : (u+j)/2 = u/2+j/2 := by omega
    have hdivv : (v+j)/2 = v/2+j/2 := by omega
    have hmod : (u+j)%2 = (v+j)%2 := by omega
    rw [hm (u+j), hm (v+j), hdivu, hdivv, hmod, hsame]
  · simp [hu, hv] at huv
  · simp [hu, hv] at huv
  · have hc : c₁ (u/2) = c₁ (v/2) := by simpa [hu, hv] using huv
    have hsame := hc₁ _ _ hc ((j+1)/2) (ho _ hj)
    have hdivu : (u+j)/2 = u/2+(j+1)/2 := by omega
    have hdivv : (v+j)/2 = v/2+(j+1)/2 := by omega
    have hmod : (u+j)%2 = (v+j)%2 := by omega
    rw [hm (u+j), hm (v+j), hdivu, hdivv, hmod, hsame]

theorem FactorCode.shift {A : Type*} {m : ℕ → A} {k P : ℕ}
    (h : FactorCode m k P) (t : ℕ) : FactorCode (fun n => m (t+n)) k P := by
  obtain ⟨code, hc⟩ := h
  refine ⟨fun n => code (t+n), fun u v huv j hj => ?_⟩
  simpa only [Nat.add_assoc] using hc (t+u) (t+v) huv j hj

theorem FactorCode.map {A B : Type*} {m : ℕ → A} {k P : ℕ}
    (h : FactorCode m k P) (g : A → B) : FactorCode (g ∘ m) k P := by
  obtain ⟨code, hc⟩ := h
  exact ⟨code, fun u v huv j hj => congrArg g (hc u v huv j hj)⟩

theorem NoOverlap.shift {A : Type*} {m : ℕ → A}
    (h : NoOverlap m) (t : ℕ) : NoOverlap (fun n => m (t+n)) := by
  intro u p hp
  simpa only [Nat.add_assoc] using h (t+u) p hp

theorem NoOverlap.map {A B : Type*} {m : ℕ → A}
    (h : NoOverlap m) {g : A → B} (hg : Function.Injective g) : NoOverlap (g ∘ m) := by
  intro u p hp
  obtain ⟨i, hi, hn⟩ := h u p hp
  exact ⟨i, hi, fun hh => hn (hg hh)⟩

/-- Among the first `P+1` windows, equal codes give two equal
order-`k` factors. If the recurrence held through position `2P`,
it would propagate this equality to an overlap. -/
theorem recurrence_fails_of_factorCode {k P : ℕ} (m : ℕ → R)
    (hoverlap : NoOverlap m) (hcode : FactorCode m k P) (c : Fin k → R) :
    ∃ i, i+k ≤ 2*P ∧ residual m c i ≠ 0 := by
  classical
  obtain ⟨code, hcode⟩ := hcode
  let f (u : Fin (P+1)) := code u
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hpair : ∃ u v : ℕ, u < v ∧ v ≤ P ∧ code u = code v := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, by have hb := b.isLt; omega, heq⟩
    · exact ⟨b, a, h, by have ha := a.isLt; omega, heq.symm⟩
  obtain ⟨u, v, huv, hv, hsame⟩ := hpair
  by_contra hnone
  have hz (i : ℕ) (hi : i+k ≤ 2*P) : residual m c i = 0 := by
    by_contra hn
    exact hnone ⟨i, hi, hn⟩
  have hextend (j : ℕ) : j ≤ P → m (u+j) = m (v+j) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      by_cases hlt : j < k
      · exact hcode u v hsame j hlt
      · have eu := hz (u+(j-k)) (by omega)
        have ev := hz (v+(j-k)) (by omega)
        unfold residual at eu ev
        rw [show u+(j-k)+k = u+j by omega] at eu
        rw [show v+(j-k)+k = v+j by omega] at ev
        have hs : (∑ l : Fin k, c l * m (u+(j-k)+l)) =
            ∑ l : Fin k, c l * m (v+(j-k)+l) := by
          apply Finset.sum_congr rfl
          intro l _
          have hl := l.isLt
          have h := ih (j-k+(l : ℕ)) (by omega) (by omega)
          rw [← Nat.add_assoc, ← Nat.add_assoc] at h
          rw [h]
        rw [hs] at eu
        exact add_right_cancel (eu.trans ev.symm)
  obtain ⟨j, hj, hneq⟩ := hoverlap u (v-u) (by omega)
  apply hneq
  rw [show u+(v-u) = v by omega]
  exact hextend j (by omega)

/-- The shift-independent next-order estimate from an upper bound on
length-`k` factor complexity and absence of overlaps. -/
theorem next_nonsingular_of_factorCode {F : Type*} [Field F]
    {k P : ℕ} (m : ℕ → F) (hk : (hankel m k).det ≠ 0)
    (hoverlap : NoOverlap m) (hcode : FactorCode m k P) :
    ∃ q, k < q ∧ q ≤ 2*P-k+1 ∧ (hankel m q).det ≠ 0 ∧
      ∀ j, k < j → j < q → (hankel m j).det = 0 := by
  apply next_nonsingular_le m hk
  intro c
  obtain ⟨i, hi, hn⟩ := recurrence_fails_of_factorCode m hoverlap hcode c
  exact ⟨i, by omega, hn⟩

#print axioms next_nonsingular
#print axioms exists_residual_zero
#print axioms next_nonsingular_le
#print axioms recurrence_fails_of_factorCode
#print axioms next_nonsingular_of_factorCode

end ShallitNormalIndex
