import BirthdayCoupling

namespace CanonneHeadTransfer

open CanonneDiffuse
open scoped BigOperators
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A common conditional simulation can only decrease TV of its input law. -/
theorem totalVariation_same_kernel_le (p q : X → ℝ)
    (f : X → Y → ℝ) (hf : ∀ x, IsLaw (f x)) :
    totalVariation (mixLaw p f) (mixLaw q f) ≤ totalVariation p q := by
  have aux (y : Y) : |mixLaw p f y - mixLaw q f y| ≤ ∑ x, |p x - q x| * f x y := by
    unfold mixLaw
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    calc
      _ ≤ ∑ x, |(p x - q x) * f x y| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_congr rfl fun x _ => by
        rw [abs_mul, abs_of_nonneg ((hf x).nonneg y)]
  unfold totalVariation
  calc
    _ ≤ (∑ y : Y, ∑ x : X, |p x - q x| * f x y) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun y _ => aux y) (by norm_num)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, fun x => (hf x).total, mul_one]

section Completion

variable {H A : Type*} [Fintype H] [Fintype A] [DecidableEq A]

/-- Insert an independent head label at a head position, or retain its tail label. -/
def fillSite (h : H → ℝ) : Option A → H ⊕ A → ℝ
  | none, Sum.inl i => h i
  | some a, Sum.inr b => if a = b then 1 else 0
  | _, _ => 0

theorem fillSite_isLaw (h : H → ℝ) (hh : IsLaw h) (tag : Option A) :
    IsLaw (fillSite h tag) := by
  refine ⟨?_, ?_⟩
  · intro y
    cases tag <;> cases y <;> simp [fillSite, hh.nonneg]
    split <;> norm_num
  · cases tag <;> simp [Fintype.sum_sum_type, fillSite, hh.total]

def fillSample {n : ℕ} (h : H → ℝ) (x : Fin n → Option A)
    (y : Fin n → H ⊕ A) : ℝ :=
  ∏ i, fillSite h (x i) (y i)

theorem fillSample_isLaw {n : ℕ} (h : H → ℝ) (hh : IsLaw h) (x : Fin n → Option A) :
    IsLaw (fillSample h x) := by
  refine ⟨fun _ => Finset.prod_nonneg (fun i _ => (fillSite_isLaw h hh (x i)).nonneg _), ?_⟩
  unfold fillSample
  rw [← Fintype.prod_sum]
  simp only [fun i => (fillSite_isLaw h hh (x i)).total, Finset.prod_const_one]

omit [Fintype H] in
theorem fillSite_mix (w : ℝ) (h : H → ℝ) (r : A → ℝ) (y : H ⊕ A) :
    (∑ x : Option A, visibleTail w r x * fillSite h x y) = split w h r y := by
  cases y with
  | inl i => simp [Fintype.sum_option, visibleTail, fillSite, split]
  | inr a => simp [Fintype.sum_option, visibleTail, fillSite, split, mul_ite]

omit [Fintype H] in
theorem fill_iid {n : ℕ} (w : ℝ) (h : H → ℝ) (r : A → ℝ) :
    mixLaw (pilotLaw (I := Fin n) (visibleTail w r)) (fillSample h) =
      pilotLaw (split w h r) := by
  funext y
  unfold mixLaw fillSample
  rw [pilot_weighted_product (visibleTail w r) (fun i x => fillSite h x (y i))]
  simp only [fillSite_mix, pilotLaw]

/-- Complete ordered observations, with independently generated head labels
and shared with-replacement iid tail pilots, before any support conditioning. -/
def replacementFull {n : ℕ} (K : ℕ) (w : ℝ) (h : H → ℝ) (r : A → ℝ) :
    (Fin n → H ⊕ A) → ℝ :=
  mixLaw (replacementMasked K w r) (fillSample h)

/-- The weighted birthday bound on the actual full ordered sample law. -/
theorem full_pilot_tv {n K : ℕ} {h : H → ℝ} {r : A → ℝ}
    (hh : IsLaw h) (hr : IsLaw r)
    (hK : 0 < K) {w : ℝ} (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
    totalVariation (replacementFull (n := n) K w h r) (pilotLaw (split w h r)) ≤
      (n.choose 2 : ℝ) * w^2 / K := by
  rw [← fill_iid w h r]
  exact (totalVariation_same_kernel_le _ _ _ (fillSample_isLaw h hh)).trans
    (masked_pilot_tv hr hK hw₀ hw₁)

end Completion
end
end CanonneHeadTransfer
