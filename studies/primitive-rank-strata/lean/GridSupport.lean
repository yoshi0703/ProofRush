import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Push

/-! Minimum support of integer arrays whose rectangular differences above a
given order vanish. Coordinates are arbitrary finite alphabets. -/

namespace KasonyiGrid

open scoped BigOperators

/-- A product of the finite coordinate alphabets of the specified sizes. -/
def Grid : List Nat → Type
  | [] => PUnit
  | d :: ds => Fin d × Grid ds

def slice {d : Nat} {ds : List Nat} (f : Grid (d :: ds) → ℤ) (i : Fin d) :
    Grid ds → ℤ :=
  fun x => f (i, x)

def sliceDiff {d : Nat} {ds : List Nat} (f : Grid (d :: ds) → ℤ) (i j : Fin d) :
    Grid ds → ℤ :=
  fun x => slice f i x - slice f j x

/-- Vanishing of mixed differences of order one above the given order.
A test either fixes the first coordinate or differences along it. At order
zero, the latter test compares the slices pointwise. -/
def LowOrder : (ds : List Nat) → Nat → (Grid ds → ℤ) → Prop
  | [], _, _ => True
  | d :: ds, r, f =>
    (∀ i : Fin d, LowOrder ds r (slice f i)) ∧
    match r with
    | 0 => ∀ i j : Fin d, slice f i = slice f j
    | r + 1 => ∀ i j : Fin d, LowOrder ds r (sliceDiff f i j)

def weight : (ds : List Nat) → (Grid ds → ℤ) → Nat
  | [], f => if f PUnit.unit = 0 then 0 else 1
  | d :: ds, f => ∑ i : Fin d, weight ds (slice f i)

private theorem weight_pos (ds : List Nat) (f : Grid ds → ℤ)
    (h : ∃ x, f x ≠ 0) : 0 < weight ds f := by
  induction ds with
  | nil =>
    obtain ⟨⟨⟩, hx⟩ := h
    simp [weight, hx]
  | cons d ds ih =>
    obtain ⟨⟨i, x⟩, hx⟩ := h
    have hp : 0 < weight ds (slice f i) := ih _ ⟨x, hx⟩
    change 0 < ∑ j : Fin d, weight ds (slice f j)
    exact hp.trans_le (Finset.single_le_sum (f := fun j => weight ds (slice f j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

private theorem weight_difference_le (ds : List Nat) (f g : Grid ds → ℤ) :
    weight ds (fun x => f x - g x) ≤ weight ds f + weight ds g := by
  induction ds with
  | nil =>
    by_cases hf : f PUnit.unit = 0 <;> by_cases hg : g PUnit.unit = 0 <;>
      simp [weight, hf, hg]
    split <;> omega
  | cons d ds ih =>
    simp only [weight, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => ih (slice f i) (slice g i)

private theorem two_slices_le (d : Nat) (ds : List Nat)
    (f : Grid (d :: ds) → ℤ) {i j : Fin d} (hij : i ≠ j) :
    weight ds (slice f i) + weight ds (slice f j) ≤ weight (d :: ds) f := by
  have hsubset : ({i, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset hsubset (f := fun k => weight ds (slice f k))
  simpa [weight, Finset.sum_insert, hij] using hsum

private theorem constant_weight (d : Nat) (ds : List Nat) (f : Grid (d :: ds) → ℤ)
    (i : Fin d) (h : ∀ j, slice f j = slice f i) :
    weight (d :: ds) f = d * weight ds (slice f i) := by
  simp [weight, h]

private theorem prefix_cons_le (a : Nat) (ds : List Nat) (t : Nat)
    (ht : t < ds.length) (h : ∀ d ∈ ds, a ≤ d) :
    a * (ds.take t).prod ≤ (ds.take (t + 1)).prod := by
  induction ds generalizing t with
  | nil => simp at ht
  | cons d ds ih =>
    cases t with
    | zero => simpa using h d (by simp)
    | succ t =>
      have ht' : t < ds.length := by simpa using ht
      have h' : ∀ b ∈ ds, a ≤ b := fun b hb => h b (by simp [hb])
      simpa [Nat.mul_left_comm a d] using Nat.mul_le_mul_left d (ih t ht' h')

/-- A nonzero array of interaction order at most r has at least the product
of the smallest length-r coordinate sizes many nonzero entries. -/
theorem minimum_support_lower (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) (hsorted : ds.Pairwise (· ≤ ·))
    (f : Grid ds → ℤ) (hf : LowOrder ds r f) (hn : ∃ x, f x ≠ 0) :
    (ds.take (ds.length - r)).prod ≤ weight ds f := by
  induction ds generalizing r with
  | nil =>
    simp only [List.take_nil, List.prod_nil]
    exact Nat.succ_le_of_lt (weight_pos [] f hn)
  | cons d ds ih =>
    by_cases hr : r < (d :: ds).length
    · obtain ⟨i, x, hx⟩ : ∃ (i : Fin d) (x : Grid ds), f (i, x) ≠ 0 := by
        obtain ⟨⟨i, x⟩, hx⟩ := hn
        exact ⟨i, x, hx⟩
      have hds : ∀ a ∈ ds, 0 < a := fun a ha => hpos a (by simp [ha])
      have hhead := (List.pairwise_cons.mp hsorted).1
      have htail := (List.pairwise_cons.mp hsorted).2
      have hs : ∀ j : Fin d, LowOrder ds r (slice f j) := hf.1
      have hlength : (d :: ds).length - r = (ds.length - r) + 1 := by
        simp only [List.length_cons] at hr ⊢
        omega
      rw [hlength, List.take_succ_cons, List.prod_cons]
      by_cases hc : ∀ j, slice f j = slice f i
      · rw [constant_weight d ds f i hc]
        exact Nat.mul_le_mul_left d (ih r hds htail (slice f i) (hs i) ⟨x, hx⟩)
      · push Not at hc
        obtain ⟨j, hj⟩ := hc
        have hji : j ≠ i := by
          intro e
          exact hj (congrArg (slice f) e)
        cases r with
        | zero => exact (hj (hf.2 j i)).elim
        | succ r =>
          have hm : LowOrder ds r (sliceDiff f j i) := hf.2 j i
          have hd : ∃ x, sliceDiff f j i x ≠ 0 := by
            by_contra hall
            push Not at hall
            apply hj
            funext x
            exact sub_eq_zero.mp (hall x)
          have htake : ds.length - r = (ds.length - (r + 1)) + 1 := by
            simp only [List.length_cons] at hr
            omega
          have ht : ds.length - (r + 1) < ds.length := by
            simp only [List.length_cons] at hr
            omega
          calc
            d * (ds.take (ds.length - (r + 1))).prod
              ≤ (ds.take (ds.length - r)).prod := by
                rw [htake]
                exact prefix_cons_le d ds _ ht hhead
            _ ≤ weight ds (sliceDiff f j i) := ih r hds htail _ hm hd
            _ ≤ weight ds (slice f j) + weight ds (slice f i) :=
              weight_difference_le ds _ _
            _ ≤ weight (d :: ds) f := two_slices_le d ds f hji
    · have hn' : (d :: ds).length - r = 0 := by omega
      rw [hn', List.take_zero, List.prod_nil]
      exact Nat.succ_le_of_lt (weight_pos (d :: ds) f hn)

/-- Select a base point on undifferenced axes and an ordered pair of
positions on each axis used in a rectangular mixed difference. -/
inductive RectTest : List Nat → Nat → Type
  | empty : RectTest [] 0
  | fix {d ds r} : Fin d → RectTest ds r → RectTest (d :: ds) r
  | diff {d ds r} : Fin d → Fin d → RectTest ds r → RectTest (d :: ds) (r + 1)

def testValue : {ds : List Nat} → {r : Nat} → RectTest ds r → (Grid ds → ℤ) → ℤ
  | [], 0, .empty, f => f PUnit.unit
  | _ :: _, _, .fix i t, f => testValue t (slice f i)
  | _ :: _, _, .diff i j t, f => testValue t (sliceDiff f i j)

def pointTest : {ds : List Nat} → Grid ds → RectTest ds 0
  | [], _ => .empty
  | _ :: _, (i, x) => .fix i (pointTest x)

private theorem pointTest_value (ds : List Nat) (x : Grid ds) (f : Grid ds → ℤ) :
    testValue (pointTest x) f = f x := by
  induction ds with
  | nil => cases x; rfl
  | cons d ds ih =>
    rcases x with ⟨i, x⟩
    exact ih x (slice f i)

private theorem testValue_zero {ds : List Nat} {r : Nat} (t : RectTest ds r) :
    testValue t (fun _ => 0) = 0 := by
  induction t with
  | empty => rfl
  | fix _ _ ih => exact ih
  | diff i j t ih =>
    change testValue t (fun _ => (0 : ℤ) - 0) = 0
    simpa only [sub_self] using ih

/-- The recursive slice condition equals actual vanishing of all rectangular
mixed differences of the indicated order. -/
theorem lowOrder_iff_rectTests {ds : List Nat} {r : Nat} (f : Grid ds → ℤ) :
    LowOrder ds r f ↔ ∀ t : RectTest ds (r + 1), testValue t f = 0 := by
  induction ds generalizing r with
  | nil =>
    constructor
    · intro _ t
      cases t
    · intro _
      trivial
  | cons d ds ih =>
    constructor
    · intro hf t
      cases t with
      | fix i t =>
        exact (ih (slice f i)).mp (hf.1 i) t
      | diff i j t =>
        cases r with
        | zero =>
          have he : sliceDiff f i j = fun _ => 0 := by
            funext x
            exact sub_eq_zero.mpr (congrFun (hf.2 i j) x)
          change testValue t (sliceDiff f i j) = 0
          rw [he]
          exact testValue_zero t
        | succ r => exact (ih (sliceDiff f i j)).mp (hf.2 i j) t
    · intro h
      refine ⟨fun i => (ih (slice f i)).mpr (fun t => h (.fix i t)), ?_⟩
      cases r with
      | zero =>
        intro i j
        funext x
        apply sub_eq_zero.mp
        have hv := h (.diff i j (pointTest x))
        change testValue (pointTest x) (sliceDiff f i j) = 0 at hv
        rw [pointTest_value] at hv
        exact hv
      | succ r =>
        intro i j
        exact (ih (sliceDiff f i j)).mpr (fun t => h (.diff i j t))

theorem minimum_support_from_boxes (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) (hsorted : ds.Pairwise (· ≤ ·))
    (f : Grid ds → ℤ) (hf : ∀ t : RectTest ds (r + 1), testValue t f = 0)
    (hn : ∃ x, f x ≠ 0) :
    (ds.take (ds.length - r)).prod ≤ weight ds f :=
  minimum_support_lower ds r hpos hsorted f ((lowOrder_iff_rectTests f).mpr hf) hn

private theorem prefix_cons_lt (a : Nat) (ds : List Nat) (t : Nat)
    (ht : t < ds.length) (ha : 0 < a) (h : ∀ d ∈ ds, a < d) :
    a * (ds.take t).prod < (ds.take (t + 1)).prod := by
  induction ds generalizing t with
  | nil => simp at ht
  | cons d ds ih =>
    cases t with
    | zero => simpa using h d (by simp)
    | succ t =>
      have ht' : t < ds.length := by simpa using ht
      have hd : 0 < d := ha.trans (h d (by simp))
      have h' : ∀ b ∈ ds, a < b := fun b hb => h b (by simp [hb])
      simpa [Nat.mul_left_comm a d] using Nat.mul_lt_mul_of_pos_left (ih t ht' h') hd

private theorem sliceDiff_nonzero {d : Nat} {ds : List Nat}
    {f : Grid (d :: ds) → ℤ} {i j : Fin d} (h : slice f i ≠ slice f j) :
    ∃ x, sliceDiff f i j x ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h
  funext x
  exact sub_eq_zero.mp (hall x)

/-- With strictly increasing alphabet sizes, any dependence on the smallest
axis forces weight strictly above the minimum, until the grid is unrestricted. -/
theorem differing_slices_strict (d : Nat) (ds : List Nat) (r : Nat)
    (hpos : 0 < d) (hsorted : (d :: ds).Pairwise (· < ·))
    (hr : r < (d :: ds).length) (f : Grid (d :: ds) → ℤ)
    (hf : LowOrder (d :: ds) r f) {i j : Fin d} (hij : slice f i ≠ slice f j) :
    ((d :: ds).take ((d :: ds).length - r)).prod < weight (d :: ds) f := by
  have hhead := (List.pairwise_cons.mp hsorted).1
  have htail : ds.Pairwise (· ≤ ·) :=
    (List.pairwise_cons.mp hsorted).2.imp Nat.le_of_lt
  have hds : ∀ a ∈ ds, 0 < a := fun a ha => hpos.trans (hhead a ha)
  have hne : i ≠ j := fun e => hij (congrArg (slice f) e)
  cases r with
  | zero => exact (hij (hf.2 i j)).elim
  | succ r =>
    have hlength : (d :: ds).length - (r + 1) = (ds.length - (r + 1)) + 1 := by
      simp only [List.length_cons] at hr ⊢
      omega
    have htake : ds.length - r = (ds.length - (r + 1)) + 1 := by
      simp only [List.length_cons] at hr
      omega
    have ht : ds.length - (r + 1) < ds.length := by
      simp only [List.length_cons] at hr
      omega
    rw [hlength, List.take_succ_cons, List.prod_cons]
    calc
      d * (ds.take (ds.length - (r + 1))).prod < (ds.take (ds.length - r)).prod := by
        rw [htake]
        exact prefix_cons_lt d ds _ ht hpos hhead
      _ ≤ weight ds (sliceDiff f i j) :=
        minimum_support_lower ds r hds htail _ (hf.2 i j) (sliceDiff_nonzero hij)
      _ ≤ weight ds (slice f i) + weight ds (slice f j) := weight_difference_le ds _ _
      _ ≤ weight (d :: ds) f := two_slices_le d ds f hne

private theorem lowOrder_zero (ds : List Nat) (r : Nat) :
    LowOrder ds r (fun _ => 0) :=
  (lowOrder_iff_rectTests _).mpr testValue_zero

private theorem lowOrder_of_length_le (ds : List Nat) (r : Nat)
    (hr : ds.length ≤ r) (f : Grid ds → ℤ) : LowOrder ds r f := by
  induction ds generalizing r with
  | nil => trivial
  | cons d ds ih =>
    cases r with
    | zero => simp at hr
    | succ r =>
      have hr' : ds.length ≤ r := by simpa using hr
      exact ⟨fun i => ih (r + 1) (hr'.trans (Nat.le_succ _)) (slice f i),
        fun i j => ih r hr' (sliceDiff f i j)⟩

private theorem weight_zero_of_eq_zero (ds : List Nat) (f : Grid ds → ℤ)
    (h : ∀ x, f x = 0) : weight ds f = 0 := by
  induction ds with
  | nil => simp [weight, h PUnit.unit]
  | cons d ds ih =>
    simp [weight, fun j : Fin d => ih (slice f j) (fun x => h (j, x))]

private theorem weight_eq_one_of_unique (ds : List Nat) (f : Grid ds → ℤ)
    (x : Grid ds) (hx : f x ≠ 0) (h : ∀ y, y ≠ x → f y = 0) :
    weight ds f = 1 := by
  induction ds with
  | nil => cases x; simp [weight, hx]
  | cons d ds ih =>
    rcases x with ⟨i, x⟩
    change (∑ j : Fin d, weight ds (slice f j)) = 1
    rw [Finset.sum_eq_single i]
    · exact ih (slice f i) x hx (fun y hy => h (i, y) (fun e => hy (congrArg Prod.snd e)))
    · intro j _ hj
      exact weight_zero_of_eq_zero ds (slice f j)
        (fun y => h (j, y) (fun e => hj (congrArg Prod.fst e)))
    · simp

private theorem unique_of_weight_eq_one (ds : List Nat) (f : Grid ds → ℤ)
    (hw : weight ds f = 1) (x : Grid ds) (hx : f x ≠ 0) :
    ∀ y, y ≠ x → f y = 0 := by
  induction ds with
  | nil =>
    intro y hy
    cases y
    cases x
    exact (hy rfl).elim
  | cons d ds ih =>
    obtain ⟨i, x⟩ := x
    intro y hne
    obtain ⟨j, y⟩ := y
    have hxi : 0 < weight ds (slice f i) := weight_pos ds _ ⟨x, hx⟩
    by_cases hj : j = i
    · subst j
      have hi : weight ds (slice f i) ≤ weight (d :: ds) f := by
        change weight ds (slice f i) ≤ ∑ k : Fin d, weight ds (slice f k)
        exact Finset.single_le_sum (f := fun k => weight ds (slice f k))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      exact ih (slice f i) (by omega) x hx y (fun e => hne (congrArg (i, ·) e))
    · by_contra hfy
      have hyj : 0 < weight ds (slice f j) := weight_pos ds _ ⟨y, hfy⟩
      have htwo := two_slices_le d ds f hj
      omega

/-- An array is a nonzero constant on one full fiber through the smallest
length-r axes and zero elsewhere. If r reaches the dimension, the fiber
is one point. -/
def MinimalFiber : (ds : List Nat) → Nat → (Grid ds → ℤ) → Prop
  | [], _, f => f PUnit.unit ≠ 0
  | d :: ds, r, f =>
    if r < (d :: ds).length then
      ∃ g : Grid ds → ℤ, (∀ i : Fin d, slice f i = g) ∧ MinimalFiber ds r g
    else
      ∃ x, f x ≠ 0 ∧ ∀ y, y ≠ x → f y = 0

/-- The minimum is attained exactly by the indicated fibers when the
alphabet sizes are strictly increasing. -/
theorem minimum_support_iff_fiber (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) (hsorted : ds.Pairwise (· < ·))
    (f : Grid ds → ℤ) :
    MinimalFiber ds r f ↔
      LowOrder ds r f ∧ (∃ x, f x ≠ 0) ∧ weight ds f = (ds.take (ds.length - r)).prod := by
  induction ds generalizing r with
  | nil =>
    constructor
    · intro hf
      exact ⟨trivial, ⟨PUnit.unit, hf⟩, by simp [weight, MinimalFiber] at hf ⊢; simp [hf]⟩
    · rintro ⟨_, ⟨⟨⟩, hx⟩, _⟩
      exact hx
  | cons d ds ih =>
    have hd : 0 < d := hpos d (by simp)
    have hds : ∀ a ∈ ds, 0 < a := fun a ha => hpos a (by simp [ha])
    have ht := (List.pairwise_cons.mp hsorted).2
    let i : Fin d := ⟨0, hd⟩
    by_cases hr : r < (d :: ds).length
    · have hl : (d :: ds).length - r = (ds.length - r) + 1 := by
        simp only [List.length_cons] at hr ⊢
        omega
      rw [MinimalFiber, ite_eq_left hr, hl, List.take_succ_cons, List.prod_cons]
      constructor
      · rintro ⟨g, he, hg⟩
        obtain ⟨hlow, ⟨x, hx⟩, hw⟩ := (ih r hds ht g).mp hg
        have hlow' : LowOrder (d :: ds) r f := by
          refine ⟨fun j => he j ▸ hlow, ?_⟩
          cases r with
          | zero => exact fun j k => (he j).trans (he k).symm
          | succ r =>
            intro j k
            have hz : sliceDiff f j k = fun _ => 0 := by
              funext x
              change slice f j x - slice f k x = 0
              simp [he]
            rw [hz]
            exact lowOrder_zero ds r
        have hfx : f (i, x) ≠ 0 := by
          change slice f i x ≠ 0
          rwa [he i]
        refine ⟨hlow', ⟨(i, x), hfx⟩, ?_⟩
        rw [constant_weight d ds f i (fun j => (he j).trans (he i).symm), he i, hw]
      · rintro ⟨hlow, ⟨⟨j, x⟩, hx⟩, hw⟩
        have he : ∀ k, slice f k = slice f j := by
          intro k
          by_contra hne
          have hlt := differing_slices_strict d ds r hd hsorted hr f hlow hne
          rw [hl, List.take_succ_cons, List.prod_cons, hw] at hlt
          exact (Nat.lt_irrefl _ hlt)
        refine ⟨slice f j, he, (ih r hds ht _).mpr ⟨hlow.1 j, ⟨x, hx⟩, ?_⟩⟩
        rw [constant_weight d ds f j he] at hw
        exact Nat.eq_of_mul_eq_mul_left hd hw
    · have hr' : (d :: ds).length ≤ r := Nat.le_of_not_gt hr
      rw [MinimalFiber, ite_eq_right hr, Nat.sub_eq_zero_of_le hr', List.take_zero, List.prod_nil]
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨lowOrder_of_length_le _ _ hr' f, ⟨x, hx⟩,
          weight_eq_one_of_unique _ f x hx he⟩
      · rintro ⟨_, ⟨x, hx⟩, hw⟩
        exact ⟨x, hx, unique_of_weight_eq_one _ f hw x hx⟩

theorem minimum_box_support_iff_fiber (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) (hsorted : ds.Pairwise (· < ·))
    (f : Grid ds → ℤ) :
    MinimalFiber ds r f ↔
      (∀ t : RectTest ds (r + 1), testValue t f = 0) ∧
      (∃ x, f x ≠ 0) ∧ weight ds f = (ds.take (ds.length - r)).prod := by
  rw [← lowOrder_iff_rectTests f]
  exact minimum_support_iff_fiber ds r hpos hsorted f

private def gridOrigin : (ds : List Nat) → (∀ d ∈ ds, 0 < d) → Grid ds
  | [], _ => PUnit.unit
  | d :: ds, h => (⟨0, h d (by simp)⟩, gridOrigin ds (fun k hk => h k (by simp [hk])))

private theorem exists_minimalFiber (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) : ∃ f : Grid ds → ℤ, MinimalFiber ds r f := by
  classical
  induction ds with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    change (1 : ℤ) ≠ 0
    decide
  | cons d ds ih =>
    by_cases hr : r < (d :: ds).length
    · obtain ⟨g, hg⟩ := ih (fun k hk => hpos k (by simp [hk]))
      refine ⟨fun x => g x.2, ?_⟩
      rw [MinimalFiber, ite_eq_left hr]
      exact ⟨g, fun _ => rfl, hg⟩
    · let x := gridOrigin (d :: ds) hpos
      refine ⟨fun y => if y = x then 1 else 0, ?_⟩
      rw [MinimalFiber, ite_eq_right hr]
      refine ⟨x, by simp, ?_⟩
      intro y hy
      simp [hy]

/-- A minimum-support array exists at every order. -/
theorem minimum_box_support_attained (ds : List Nat) (r : Nat)
    (hpos : ∀ d ∈ ds, 0 < d) (hsorted : ds.Pairwise (· < ·)) :
    ∃ f : Grid ds → ℤ, (∀ t : RectTest ds (r + 1), testValue t f = 0) ∧
      (∃ x, f x ≠ 0) ∧ weight ds f = (ds.take (ds.length - r)).prod := by
  obtain ⟨f, hf⟩ := exists_minimalFiber ds r hpos
  exact ⟨f, (minimum_box_support_iff_fiber ds r hpos hsorted f).mp hf⟩

end KasonyiGrid
