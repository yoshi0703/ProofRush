import CyclicBoxes
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A literal intermediate-stratum counterexample at n=105. Even without
the noncrossing condition, sparse periods cannot cover this stratum. -/

namespace Kasonyi105

open scoped BigOperators

def support (e : Gap) : Finset Idx := Finset.univ.filter (fun i => e i ≠ 0)

def TwoSparse (e : Gap) : Prop := (support e).card ≤ 2

private theorem mem_support {e : Gap} {i : Idx} : i ∈ support e ↔ e i ≠ 0 := by
  simp [support]

private theorem supported_on_pair {f : Gap} (h : TwoSparse f) :
    ∃ u v : Idx, ∀ i, f i ≠ 0 → i = u ∨ i = v := by
  have hc : (support f).card ≤ 2 := h
  by_cases he : (support f).card = 2
  · obtain ⟨u,v,_,huv⟩ := Finset.card_eq_two.mp he
    refine ⟨u,v,fun i hi => ?_⟩
    have hm := mem_support.mpr hi
    simpa [huv] using hm
  · have hle : (support f).card ≤ 1 := by omega
    obtain ⟨u,hu⟩ := Finset.card_le_one_iff_subset_singleton.mp hle
    exact ⟨u,u,fun i hi => Or.inl (Finset.mem_singleton.mp (hu (mem_support.mpr hi)))⟩

private theorem third_three : ∀ a b : Fin 3, ∃ c, c ≠ a ∧ c ≠ b := by decide
private theorem third_five : ∀ a b : Fin 5, ∃ c, c ≠ a ∧ c ≠ b := by decide
private theorem third_seven : ∀ a b : Fin 7, ∃ c, c ≠ a ∧ c ≠ b := by decide

private theorem drop_alt {T : Type*} {a b a' x : T}
    (h : a' ≠ b) (hx : x = a ∨ x = a') (hb : x = b) : x = a := by
  rcases hx with hl | hr
  · exact hl
  · exact (h (hr.symm.trans hb)).elim

/-- Every nonzero vector supported on at most two coordinates is detected
by a full mixed difference. Choose the other endpoint on each CRT axis
to avoid both support values, leaving exactly one supported box corner. -/
theorem topZero_twoSparse_eq_zero {f : Gap} (hf : TopZero (intGap f))
    (hs : TwoSparse f) : f = 0 := by
  funext i
  change f i = 0
  by_contra hi
  obtain ⟨a,b,hab⟩ := supported_on_pair hs
  obtain ⟨j,hij⟩ : ∃ j, ∀ k, f k ≠ 0 → k = i ∨ k = j := by
    rcases hab i hi with he | he
    · exact ⟨b,fun k hk => by simpa only [← he] using hab k hk⟩
    · exact ⟨a,fun k hk => by
        rcases hab k hk with hk | hk
        · exact Or.inr hk
        · exact Or.inl (hk.trans he.symm)⟩
  rcases hc : coordinates i with ⟨x,y,z⟩
  have hi' : index (x,y,z) = i := by rw [← hc,index_coordinates]
  rcases hd : coordinates j with ⟨u,v,w⟩
  obtain ⟨x',hx,hxu⟩ := third_three x u
  obtain ⟨y',hy,hyv⟩ := third_five y v
  obtain ⟨z',hz,hzw⟩ := third_seven z w
  have hzero (s : Fin 3) (t : Fin 5) (r : Fin 7)
      (hs : s=x ∨ s=x') (ht : t=y ∨ t=y') (hr : r=z ∨ r=z')
      (hn : (s,t,r) ≠ (x,y,z)) : value (intGap f) s t r = 0 := by
    by_contra hne
    have hnzero : f (index (s,t,r)) ≠ 0 := by
      intro h
      apply hne
      simp [value,intGap,h]
    rcases hij _ hnzero with h | h
    · exact hn (index_injective (h.trans hi'.symm))
    · have hcoord : (s,t,r) = (u,v,w) := by
        simpa only [coordinates_index,hd] using congrArg coordinates h
      have hu1 : s = u := congrArg Prod.fst hcoord
      have hv1 : t = v := congrArg (fun p : Point => p.2.1) hcoord
      have hw1 : r = w := congrArg (fun p : Point => p.2.2) hcoord
      exact hn (by rw [drop_alt hxu hs hu1,drop_alt hyv ht hv1,drop_alt hzw hr hw1])
  have h100 := hzero x' y z (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (by simp [hx])
  have h010 := hzero x y' z (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (by simp [hy])
  have h001 := hzero x y z' (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (by simp [hz])
  have h110 := hzero x' y' z (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (by simp [hx])
  have h101 := hzero x' y z' (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (by simp [hx])
  have h011 := hzero x y' z' (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (by simp [hy])
  have h111 := hzero x' y' z' (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (by simp [hx])
  have h := (topZero_iff_all_boxes _).mp hf x x' y y' z z'
  simp only [box,h100,h010,h001,h110,h101,h011,h111,sub_zero,add_zero] at h
  have had : (f i : ℤ) = 0 := by simpa [value,intGap,hi'] using h
  exact hi (Int.ofNat_eq_zero.mp had)

private theorem box_add (u v : Gap) (x x' : Fin 3) (y y' : Fin 5) (z z' : Fin 7) :
    box (intGap (u+v)) x x' y y' z z' =
      box (intGap u) x x' y y' z z'+box (intGap v) x x' y y' z z' := by
  simp only [box,value,intGap,Pi.add_apply,Nat.cast_add]
  ring

private theorem topZero_subtract_period {base per : Gap}
    (hb : TopZero (intGap base)) (hp : TopZero (intGap (base+per))) :
    TopZero (intGap per) := by
  apply (topZero_iff_all_boxes _).mpr
  intro x x' y y' z z'
  have hx := (topZero_iff_all_boxes _).mp hp x x' y y' z z'
  rw [box_add,(topZero_iff_all_boxes _).mp hb x x' y y' z z',zero_add] at hx
  exact hx

/-- A linear set in the usual preperiod/period representation. -/
def linear {r : ℕ} (base : Gap) (period : Fin r → Gap) : Set Gap :=
  {f | ∃ a : Fin r → ℕ, f = base + ∑ i, a i • period i}

theorem linear_subset_topZero_singleton {r : ℕ} (base : Gap) (period : Fin r → Gap)
    (hs : ∀ j, TwoSparse (period j))
    (hL : ∀ e ∈ linear base period, TopZero (intGap e)) :
    linear base period = {base} := by
  have hb : base ∈ linear base period := ⟨fun _ => 0,by simp⟩
  have hz (j : Fin r) : period j = 0 := by
    have hp : base+period j ∈ linear base period := by
      refine ⟨fun i => if i=j then 1 else 0,?_⟩
      simp [ite_smul, one_nsmul]
    exact topZero_twoSparse_eq_zero (topZero_subtract_period (hL _ hb) (hL _ hp)) (hs j)
  ext e
  constructor
  · rintro ⟨a,rfl⟩
    simp [hz]
  · intro he
    rw [Set.mem_singleton_iff.mp he]
    exact hb

/-- This class drops the noncrossing requirement of stratified semilinearity.
Failure here certifies failure of the full condition in Definition 1. Empty
pieces of a finite union may be discarded, equivalently allowing m=0. -/
def TwoSparseSemilinear (W : Set Gap) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℕ) (base : Fin m → Gap) (period : ∀ j, Fin (r j) → Gap),
    (∀ j p, TwoSparse (period j p)) ∧ W = ⋃ j, linear (base j) (period j)

def atZero {d : ℕ} (x : Fin d) : ℕ := if x.val = 0 then 1 else 0

def seed (i : Idx) : ℕ :=
  let p := coordinates i
  atZero p.1 * atZero p.2.1 + 2 * atZero p.1 * atZero p.2.2 + 2 * atZero p.2.1 * atZero p.2.2

def ray (m : ℕ) (i : Idx) : ℕ := m * seed i

private theorem ray_at (m : ℕ) (x : Fin 3) (y : Fin 5) (z : Fin 7) :
    intGap (ray m) (index (x,y,z)) =
      (m:ℤ)*((atZero x:ℤ)*(atZero y:ℤ)+2*(atZero x:ℤ)*(atZero z:ℤ)+2*(atZero y:ℤ)*(atZero z:ℤ)) := by
  simp only [intGap,ray,seed,coordinates_index,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]

theorem ray_topZero (m : ℕ) : TopZero (intGap (ray m)) := by
  apply (topZero_iff_all_boxes _).mpr
  intro x x' y y' z z'
  simp only [box,value,ray_at]
  ring

private theorem firstStep_zero_ne : ∀ t : Fin 3, t ≠ 0 → (firstStep 0 t).val ≠ 0 := by decide
private theorem secondStep_zero_ne : ∀ t : Fin 5, t ≠ 0 → (secondStep 0 t).val ≠ 0 := by decide
private theorem thirdStep_zero_ne : ∀ t : Fin 7, t ≠ 0 → (thirdStep 0 t).val ≠ 0 := by decide

theorem ray_pairs_active {m : ℕ} (hm : 0 < m) : AllPairsActive (intGap (ray m)) := by
  have hm' : (m:ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_,?_,?_⟩
  · intro t u ht hu
    refine ⟨index (0,0,0),?_⟩
    simp only [delta,shift_index_three,shift_index_five,ray_at,atZero,Fin.val_zero,
      ite_eq_right (firstStep_zero_ne t ht), ite_eq_right (secondStep_zero_ne u hu)]
    push_cast
    convert hm' using 1; ring
  · intro t v ht hv
    refine ⟨index (0,0,0),?_⟩
    simp only [delta,shift_index_three,shift_index_seven,ray_at,atZero,Fin.val_zero,
      ite_eq_right (firstStep_zero_ne t ht), ite_eq_right (thirdStep_zero_ne v hv)]
    push_cast
    convert (mul_ne_zero (by decide : (2:ℤ) ≠ 0) hm') using 1; ring
  · intro u v hu hv
    refine ⟨index (0,0,0),?_⟩
    simp only [delta,shift_index_five,shift_index_seven,ray_at,atZero,Fin.val_zero,
      ite_eq_right (secondStep_zero_ne u hu), ite_eq_right (thirdStep_zero_ne v hv)]
    push_cast
    convert (mul_ne_zero (by decide : (2:ℤ) ≠ 0) hm') using 1; ring

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem seed_unique_at_zero : ∀ i : Idx, i ≠ 0 → seed i ≠ seed 0 := by decide

theorem ray_at_zero (m : ℕ) : ray m 0 = 5*m := by
  have hs : seed 0 = 5 := by decide
  rw [ray,hs,Nat.mul_comm]

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
theorem seed_sum : (∑ i : Idx, seed i) = 23 := by decide

theorem ray_sum (m : ℕ) : (∑ i : Idx, ray m i) = 23*m := by
  simp only [ray,← Finset.mul_sum,seed_sum]
  omega

theorem ray_primitive {m : ℕ} (hm : 0 < m) : CyclicPrimitive (ray m) := by
  intro s hs
  refine ⟨0,?_⟩
  have he : shift 0 s.val = s := by
    apply Fin.ext
    simp [shift,Nat.mod_eq_of_lt s.isLt]
  rw [he]
  intro heq
  exact (seed_unique_at_zero s hs) (Nat.mul_left_cancel hm heq.symm)

theorem ray_mem_stratum {m : ℕ} (hm : 0 < m) : ray m ∈ Stratum :=
  ⟨ray_topZero m,ray_pairs_active hm,ray_primitive hm⟩

/-- Any definition of the intermediate stratum lying in the top-zero
space and accepting the rays (for example a weaker reading of the
order-two condition) has the same obstruction. -/
theorem no_twoSparse_cover_of_ray (W : Set Gap)
    (hTop : ∀ e ∈ W, TopZero (intGap e)) (hRay : ∀ t : ℕ, ray (105*t+1) ∈ W) :
    ¬ TwoSparseSemilinear W := by
  rintro ⟨m,r,base,period,hs,hw⟩
  let M := ∑ j : Fin m, base j 0
  have hL (j : Fin m) : linear (base j) (period j) = {base j} := by
    apply linear_subset_topZero_singleton _ _ (hs j)
    intro e he
    apply hTop e
    rw [hw]
    exact Set.mem_iUnion.mpr ⟨j,he⟩
  have hr := hRay M
  rw [hw] at hr
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hr
  rw [hL j,Set.mem_singleton_iff] at hj
  have hb : base j 0 ≤ M := by
    change base j 0 ≤ ∑ k : Fin m, base k 0
    exact Finset.single_le_sum (f := fun k : Fin m => base k 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← hj,ray_at_zero] at hb
  omega

/-- The strong all-pairs (E_2) primitive stratum of Definition 10 at
105 is not even a finite union of linear sets with two-sparse periods. -/
theorem intermediate_stratum_not_twoSparseSemilinear : ¬ TwoSparseSemilinear Stratum :=
  no_twoSparse_cover_of_ray Stratum (fun _ he => he.1) (fun _ => ray_mem_stratum (by omega))

end Kasonyi105
