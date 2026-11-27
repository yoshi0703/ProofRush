import MeanGate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

namespace CanonneIIDHead

open CanonneDiffuse CanonneHeadTransfer CanonneQuantile
open scoped BigOperators
noncomputable section

variable {A : Type*} [Fintype A]

def E {C : Type*} [Fintype C] (p f : C → ℝ) : ℝ := ∑ a, p a*f a

theorem E_const_mul {C : Type*} [Fintype C] (p f : C → ℝ) (b : ℝ) :
    E p (fun z => b*f z) = b * E p f := by
  simp only [E,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem E_sum {C I : Type*} [Fintype C] [Fintype I] (p : C → ℝ) (f : I → C → ℝ) :
    E p (fun z => ∑ i, f i z) = ∑ i, E p (f i) := by
  simp only [E,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem E_mono {C : Type*} [Fintype C] {p : C → ℝ} (hp : ∀ z, 0 ≤ p z)
    {f g : C → ℝ} (h : ∀ z, f z ≤ g z) : E p f ≤ E p g :=
  Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (h z) (hp z))

theorem E_const {C : Type*} [Fintype C] (p : C → ℝ) (hp : ∑ i, p i = 1) (v : ℝ) :
    E p (fun _ => v) = v := by unfold E; rw [← Finset.sum_mul,hp,one_mul]

theorem E_add {C : Type*} [Fintype C] (p f g : C → ℝ) :
    E p (fun z => f z+g z) = E p f+E p g := by simp [E, mul_add, Finset.sum_add_distrib]

def centeredSum {n : ℕ} (p f : A → ℝ) (x : Fin n → A) : ℝ :=
  ∑ i, (f (x i)-E p f)

theorem centered_second_le {p : A → ℝ} (hp : IsLaw p) (f : A → ℝ) (n : ℕ) :
    E (pilotLaw p) (fun x : Fin n → A => (centeredSum p f x)^2) ≤ (n:ℝ)*E p (fun a => (f a)^2) := by
  let m := E p f
  have hz : ∑ a, p a*(f a-m) = 0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hp.total,one_mul,m,E,sub_self]
  have hs := centered_sum_second_moment (n:=n) hp (fun a => f a-m) hz
  change E (pilotLaw p) (fun x : Fin n → A => (centeredSum p f x)^2) =
    (n:ℝ)*∑ a, p a*(f a-m)^2 at hs
  rw [hs]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpoint (a) : p a*(f a-m)^2 = p a*(f a)^2 - 2*m*(p a*f a)+p a*m^2 := by ring
  simp only [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
    hp.total,one_mul,E]
  change (∑ a, p a*(f a)^2) - 2*m*m+m^2 ≤ _
  linarith [sq_nonneg m]

variable [DecidableEq A]

def hit (a b : A) : ℝ := if b=a then 1 else 0

def centeredCount {n : ℕ} (p : A → ℝ) (x : Fin n → A) (a : A) : ℝ :=
  ∑ i, (hit a (x i)-p a)

theorem hit_mean (p : A → ℝ) (a : A) : E p (hit a) = p a := by simp [E,hit,mul_ite]

theorem weighted_counts {n : ℕ} (p f : A → ℝ) (x : Fin n → A) :
    (∑ a, f a*centeredCount p x a) = centeredSum p f x := by
  unfold centeredCount centeredSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_sub,Finset.sum_sub_distrib]
  have hxin : (∑ a, f a*hit a (x i)) = f (x i) := by simp [hit,mul_ite]
  rw [hxin]
  simp [E,mul_comm]

theorem count_second_le {p : A → ℝ} (hp : IsLaw p) (a : A) (n : ℕ) :
    E (pilotLaw p) (fun x : Fin n → A => (centeredCount p x a)^2) ≤ (n:ℝ)*p a := by
  have hsecond : E p (fun b => (hit a b)^2) = p a := by simp [E,hit,ite_pow,mul_ite]
  simpa only [centeredSum,hit_mean,centeredCount,hsecond] using centered_second_le hp (hit a) n

def pairScore {n : ℕ} (u q : A → ℝ) (x y : Fin n → A) : ℝ :=
  ∑ a, (u a*centeredCount q x a)*centeredCount q y a

theorem centered_pair_second {p : A → ℝ} (hp : IsLaw p) (u : A → ℝ) (n : ℕ) :
    E (pilotLaw p) (fun x : Fin n → A => E (pilotLaw p)
      (fun y : Fin n → A => (pairScore u p x y)^2)) ≤
       (n:ℝ)^2 * ∑ a, (u a)^2*(p a)^2 := by
  let Q := pilotLaw (I:=Fin n) p
  have hQ := pilotLaw_isLaw (I:=Fin n) hp
  let g (x : Fin n → A) (a : A) := u a*centeredCount p x a
  have hcond (x : Fin n → A) :
      E Q (fun y => (pairScore u p x y)^2) ≤ (n:ℝ)*∑ a, p a*(u a)^2*(centeredCount p x a)^2 := by
    have h1 (y : Fin n → A) : pairScore u p x y = centeredSum p (g x) y := weighted_counts p (g x) y
    simp only [h1]
    refine (centered_second_le hp (g x) n).trans_eq ?_
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp [g]
    ring
  refine (E_mono hQ.nonneg hcond).trans ?_
  rw [E_const_mul, E_sum]
  simp only [E_const_mul]
  calc
    _ ≤ (n:ℝ)*∑ a, p a*(u a)^2*((n:ℝ)*p a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (count_second_le hp a n)
        (mul_nonneg (hp.nonneg a) (sq_nonneg _))
    _ = _ := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

def shapeSignal (u p q : A → ℝ) : ℝ := ∑ a, u a*(p a-q a)^2

omit [Fintype A] in
theorem count_change {n : ℕ} (p q : A → ℝ) (x : Fin n → A) (a : A) :
    centeredCount q x a = centeredCount p x a + (n:ℝ)*(p a-q a) := by
  unfold centeredCount
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem pair_decompose {n : ℕ} (u p q : A → ℝ) (x y : Fin n → A) :
    let g := fun a => u a*(p a-q a)
    pairScore u q x y-(n:ℝ)^2*shapeSignal u p q =
      pairScore u p x y + (n:ℝ)*centeredSum p g x + (n:ℝ)*centeredSum p g y := by
  dsimp only
  rw [← weighted_counts, ← weighted_counts]
  unfold pairScore shapeSignal
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [count_change p q x, count_change p q y]
  ring

def firstBatch {n : ℕ} (x : Fin (n+n) → A) : Fin n → A := fun i => x (i.castAdd n)
def lastBatch {n : ℕ} (x : Fin (n+n) → A) : Fin n → A := fun i => x (Fin.natAdd n i)

def twoBatches (n : ℕ) (C : Type*) :
    (Fin (n+n) → C) ≃ ((Fin n → C) × (Fin n → C)) where
  toFun z := ⟨firstBatch z,lastBatch z⟩
  invFun z := Fin.append z.1 z.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv z := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _

omit [DecidableEq A] in
theorem batches_expectation {n : ℕ} (p : A → ℝ) (g : (Fin n → A) → (Fin n → A) → ℝ) :
    E (pilotLaw p) (fun z => g (firstBatch z) (lastBatch z)) =
      E (pilotLaw p) (fun x => E (pilotLaw p) (fun y => g x y)) := by
  classical
  let b := twoBatches n A
  let f (xy : (Fin n → A) × (Fin n → A)) := (pilotLaw p xy.1*pilotLaw p xy.2)*g xy.1 xy.2
  have hprod (z : Fin (n+n) → A) : pilotLaw p z =
      pilotLaw p (firstBatch z) * pilotLaw p (lastBatch z) := Fin.prod_univ_add _
  calc
    _ = ∑ z, f (b z) := by
      unfold E
      apply Finset.sum_congr rfl
      intro z _
      rw [hprod]
      rfl
    _ = ∑ xy, f xy := b.sum_comp f
    _ = _ := by simp only [Fintype.sum_prod_type,E,f,Finset.mul_sum,mul_assoc]

def BExp {n : ℕ} (p : A → ℝ) (g : (Fin n → A) → (Fin n → A) → ℝ) : ℝ :=
  E (pilotLaw p) (fun x => E (pilotLaw p) (fun y => g x y))

omit [DecidableEq A] in
theorem bexp_const_mul {n : ℕ} (p : A → ℝ) (g : (Fin n → A) → (Fin n → A) → ℝ) (c : ℝ) :
    BExp p (fun x y => c*g x y) = c*BExp p g := by simp only [BExp,E_const_mul]

omit [DecidableEq A] in
theorem bexp_add {n : ℕ} (p : A → ℝ) (f g : (Fin n → A) → (Fin n → A) → ℝ) :
    BExp p (fun x y => f x y+g x y) = BExp p f + BExp p g := by simp only [BExp,E_add]

/-- A distribution-free bound for the actual 2n-record quadratic test,
with a separate n-record batch for each factor. Counts in this statement
are multinomial, with their dependence across categories kept intact. -/
theorem iid_head_quadratic_error {p : A → ℝ} (hp : IsLaw p) (q u : A → ℝ) (n : ℕ) :
    E (pilotLaw p) (fun z : Fin (n+n) → A =>
      (pairScore u q (firstBatch z) (lastBatch z)-(n:ℝ)^2*shapeSignal u p q)^2) ≤
    3*(n:ℝ)^2*(∑ a, (u a)^2*(p a)^2) +
    6*(n:ℝ)^3*(∑ a, p a*(u a*(p a-q a))^2) := by
  let g (a : A) := u a * (p a-q a)
  let Y (x : Fin n → A) := centeredSum p g x
  let V := shapeSignal u p q
  let Z (x y : Fin n → A) := pairScore u p x y
  let Q := pilotLaw (I:=Fin n) p
  have hQ := pilotLaw_isLaw (I:=Fin n) hp
  have hjoint : ∀ (x y : Fin n → A), (pairScore u q x y-(n:ℝ)^2*V)^2 ≤
    3*((Z x y)^2+(n:ℝ)^2*(Y x)^2+(n:ℝ)^2*(Y y)^2) := by
    intro x y
    have he := pair_decompose u p q x y
    change pairScore u q x y-(n:ℝ)^2*V = Z x y+(n:ℝ)*Y x+(n:ℝ)*Y y at he
    rw [he]
    nlinarith only [sq_nonneg (Z x y-(n:ℝ)*Y x),sq_nonneg (Z x y-(n:ℝ)*Y y),
      sq_nonneg ((n:ℝ)*Y x-(n:ℝ)*Y y)]
  have hx : BExp p (fun (x _y : Fin n → A) => (Y x)^2) = E Q (fun x => (Y x)^2) := by
    unfold BExp
    simp only [E_const _ hQ.total]
    rfl
  have hy : BExp p (fun (_x y : Fin n → A) => (Y y)^2) = E Q (fun x => (Y x)^2) :=
    E_const _ hQ.total _
  have h2 := centered_pair_second hp u n
  have hlin := centered_second_le hp g n
  rw [batches_expectation p (fun x y => (pairScore u q x y-(n:ℝ)^2*shapeSignal u p q)^2)]
  calc
    _ ≤ BExp p (fun x y => 3*((Z x y)^2+(n:ℝ)^2*(Y x)^2+(n:ℝ)^2*(Y y)^2)) :=
      E_mono hQ.nonneg (fun x => E_mono hQ.nonneg (hjoint x))
    _ = 3*(BExp p (fun x y => (Z x y)^2) + (n:ℝ)^2*E Q (fun x => (Y x)^2) +
                              (n:ℝ)^2*E Q (fun x => (Y x)^2)) := by
      simp only [bexp_const_mul,bexp_add,hx,hy]
    _ ≤ _ := by
      change BExp p (fun x y => (Z x y)^2) ≤ _ at h2
      change E Q (fun x => (Y x)^2) ≤ (n:ℝ)*(∑ a, p a*(u a*(p a-q a))^2) at hlin
      nlinarith only [h2, mul_le_mul_of_nonneg_left hlin (sq_nonneg (n:ℝ))]

end
end CanonneIIDHead
