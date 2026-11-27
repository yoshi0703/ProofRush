import Stratum105
import Mathlib.Data.Nat.Prime.Defs

/-! Literal integer scales from Definition 4 agree with the cyclic residue
scales. This includes negative admissible multipliers. -/

namespace Kasonyi105

def integerShift (i : Idx) (s : ℤ) : Idx :=
  ⟨(((i.val:ℤ)+s)%105).toNat,by
    have hm := Int.emod_lt_of_pos ((i.val:ℤ)+s) (by decide : (0:ℤ)<105)
    omega⟩

private theorem integerShift_nat (i : Idx) (s : ℕ) :
    integerShift i (s:ℤ) = shift i s := by
  apply Fin.ext
  change (((i.val:ℤ)+(s:ℤ))%105).toNat = (i.val+s)%105
  rw [← Int.natCast_add]
  exact congrArg Int.toNat (Int.natCast_emod (i.val+s) 105).symm

private theorem integerShift_cast (i : Idx) (s : ℤ) :
    ((integerShift i s).val:ℤ) = ((i.val:ℤ)+s)%105 :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem integerShift_add (i : Idx) (a b : ℤ) :
    integerShift (integerShift i a) b = integerShift i (a+b) := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [integerShift_cast,integerShift_cast,integerShift_cast,Int.emod_add_emod,add_assoc]

def residue {p : ℕ} (hp : 0 < p) (t : ℤ) : Fin p :=
  ⟨(t%(p:ℤ)).toNat,by
    have hm := Int.emod_lt_of_pos t (by exact_mod_cast hp : (0:ℤ)<p)
    omega⟩

private theorem residue_cast {p : ℕ} (hp : 0 < p) (t : ℤ) :
    ((residue hp t).val:ℤ) = t%(p:ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg t (by exact_mod_cast hp.ne'))

private theorem residue_nat {p : ℕ} (hp : 0 < p) (t : Fin p) :
    residue hp (t.val:ℤ) = t := by
  apply Fin.ext
  have h := residue_cast hp (t.val:ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast t.isLt)] at h
  omega

private theorem residue_nonzero_iff {p : ℕ} [NeZero p] (hp : 0 < p) (t : ℤ) :
    residue hp t ≠ 0 ↔ t%(p:ℤ) ≠ 0 := by
  rw [← residue_cast hp t]
  constructor
  · intro h hz
    apply h
    apply Fin.ext
    change (residue hp t).val = 0
    omega
  · intro h hz
    apply h
    rw [hz]
    rfl

theorem integerShift_reduce {p stride : ℕ} (hp : 0 < p) (hprod : p*stride=105)
    (i : Idx) (t : ℤ) :
    integerShift i (t*stride) = shift i ((residue hp t).val*stride) := by
  have hi : (p:ℤ)*(stride:ℤ)=105 := by exact_mod_cast hprod
  have hmod : ((i.val:ℤ)+t*(stride:ℤ))%105 =
      ((i.val:ℤ)+(t%(p:ℤ))*(stride:ℤ))%105 := by
    have he := Int.emod_add_ediv_mul t (p:ℤ)
    have hdiff : (i.val:ℤ)+t*(stride:ℤ) =
        ((i.val:ℤ)+(t%(p:ℤ))*(stride:ℤ)) + (t/(p:ℤ))*105 := by
      calc
        _ = (i.val:ℤ)+((t%(p:ℤ))+(t/(p:ℤ))*(p:ℤ))*(stride:ℤ) := by rw [he]
        _ = _ := by rw [← hi]; ring
    rw [hdiff,Int.add_mul_emod_self_right]
  rw [← integerShift_nat]
  apply Fin.ext
  change (((i.val:ℤ)+t*(stride:ℤ))%105).toNat =
    (((i.val:ℤ)+(((residue hp t).val*stride:ℕ):ℤ))%105).toNat
  rw [hmod,Nat.cast_mul,residue_cast]

def deltaInteger (s : ℤ) (f : Idx → ℤ) (i : Idx) : ℤ := f i-f (integerShift i s)

theorem deltaInteger_comm (a b : ℤ) (f : Idx → ℤ) :
    deltaInteger a (deltaInteger b f) = deltaInteger b (deltaInteger a f) := by
  funext i
  simp only [deltaInteger,integerShift_add]
  rw [add_comm b a]
  ring

/-- The eight corners of Definition 5, displayed in cyclic index notation. -/
def integerBox (a b c : ℤ) (f : Idx → ℤ) (i : Idx) : ℤ :=
  f i - f (integerShift i a) - f (integerShift i b) - f (integerShift i c) +
    f (integerShift i (a+b)) + f (integerShift i (a+c)) + f (integerShift i (b+c)) -
    f (integerShift i (a+b+c))

theorem deltaInteger_box (a b c : ℤ) (f : Idx → ℤ) (i : Idx) :
    deltaInteger a (deltaInteger b (deltaInteger c f)) i = integerBox a b c f i := by
  simp only [deltaInteger,integerBox,integerShift_add]
  ring

theorem admissible_iff_natCoprime {p : ℕ} (hp : p.Prime) (t : ℤ) :
    t%(p:ℤ) ≠ 0 ↔ Nat.Coprime p t.natAbs := by
  have hd : p ∣ t.natAbs ↔ (p:ℤ) ∣ t := by
    simpa only [Int.natAbs_natCast] using (@Int.natAbs_dvd_natAbs (p:ℤ) t)
  rw [hp.coprime_iff_not_dvd,hd,Int.dvd_iff_emod_eq_zero]

theorem deltaInteger_reduce {p stride : ℕ} (hp : 0 < p) (hprod : p*stride=105)
    (f : Idx → ℤ) (t : ℤ) :
    deltaInteger (t*stride) f = delta ((residue hp t).val*stride) f := by
  funext i
  simp only [deltaInteger,delta,integerShift_reduce hp hprod]

private theorem deltaThree (f : Idx → ℤ) (t : ℤ) :
    deltaInteger (t*35) f = delta ((residue (by decide : 0 < 3) t).val*35) f := by
  simpa only [Nat.cast_ofNat] using deltaInteger_reduce
    (p := 3) (stride := 35) (by decide) (by decide) f t

private theorem deltaFive (f : Idx → ℤ) (t : ℤ) :
    deltaInteger (t*21) f = delta ((residue (by decide : 0 < 5) t).val*21) f := by
  simpa only [Nat.cast_ofNat] using deltaInteger_reduce
    (p := 5) (stride := 21) (by decide) (by decide) f t

private theorem deltaSeven (f : Idx → ℤ) (t : ℤ) :
    deltaInteger (t*15) f = delta ((residue (by decide : 0 < 7) t).val*15) f := by
  simpa only [Nat.cast_ofNat] using deltaInteger_reduce
    (p := 7) (stride := 15) (by decide) (by decide) f t

/-- The original integer-scale versions of the full- and lower-order tests.
At a prime divisor, admissibility is exactly nonzero Euclidean residue. -/
def TopZeroInteger (f : Idx → ℤ) : Prop :=
  ∀ t u v : ℤ, t%3 ≠ 0 → u%5 ≠ 0 → v%7 ≠ 0 → ∀ i,
    deltaInteger (t*35) (deltaInteger (u*21) (deltaInteger (v*15) f)) i = 0

theorem topZeroInteger_iff (f : Idx → ℤ) : TopZeroInteger f ↔ TopZero f := by
  let h3 : 0 < (3:ℕ) := by decide
  let h5 : 0 < (5:ℕ) := by decide
  let h7 : 0 < (7:ℕ) := by decide
  constructor
  · intro h t u v ht hu hv i
    have ht' : (t.val:ℤ)%3 ≠ 0 := (residue_nonzero_iff h3 _).mp (by rwa [residue_nat])
    have hu' : (u.val:ℤ)%5 ≠ 0 := (residue_nonzero_iff h5 _).mp (by rwa [residue_nat])
    have hv' : (v.val:ℤ)%7 ≠ 0 := (residue_nonzero_iff h7 _).mp (by rwa [residue_nat])
    have hh := h (t.val:ℤ) (u.val:ℤ) (v.val:ℤ) ht' hu' hv' i
    simpa only [deltaThree,deltaFive,deltaSeven,residue_nat] using hh
  · intro h t u v ht hu hv i
    rw [deltaThree,deltaFive,deltaSeven]
    exact h (residue h3 t) (residue h5 u) (residue h7 v)
      ((residue_nonzero_iff h3 _).mpr ht) ((residue_nonzero_iff h5 _).mpr hu)
      ((residue_nonzero_iff h7 _).mpr hv) i

def AllPairsInteger (f : Idx → ℤ) : Prop :=
  (∀ t u : ℤ, t%3 ≠ 0 → u%5 ≠ 0 →
    ∃ i, deltaInteger (t*35) (deltaInteger (u*21) f) i ≠ 0) ∧
  (∀ t v : ℤ, t%3 ≠ 0 → v%7 ≠ 0 →
    ∃ i, deltaInteger (t*35) (deltaInteger (v*15) f) i ≠ 0) ∧
  (∀ u v : ℤ, u%5 ≠ 0 → v%7 ≠ 0 →
    ∃ i, deltaInteger (u*21) (deltaInteger (v*15) f) i ≠ 0)

private theorem integer_pair_iff {p q s t : ℕ} [NeZero p] [NeZero q]
    (hp : 0 < p) (hq : 0 < q) (hs : p*s=105) (ht : q*t=105) (f : Idx → ℤ) :
    (∀ a b : ℤ, a%(p:ℤ) ≠ 0 → b%(q:ℤ) ≠ 0 →
      ∃ i, deltaInteger (a*s) (deltaInteger (b*t) f) i ≠ 0) ↔
    (∀ (a : Fin p) (b : Fin q), a ≠ 0 → b ≠ 0 →
      ∃ i, delta (a.val*s) (delta (b.val*t) f) i ≠ 0) := by
  constructor
  · intro h a b ha hb
    have ha' : (a.val:ℤ)%(p:ℤ) ≠ 0 := (residue_nonzero_iff hp _).mp (by rwa [residue_nat])
    have hb' : (b.val:ℤ)%(q:ℤ) ≠ 0 := (residue_nonzero_iff hq _).mp (by rwa [residue_nat])
    simpa only [deltaInteger_reduce hp hs,deltaInteger_reduce hq ht,residue_nat]
      using h (a.val:ℤ) (b.val:ℤ) ha' hb'
  · intro h a b ha hb
    rw [deltaInteger_reduce hp hs,deltaInteger_reduce hq ht]
    exact h (residue hp a) (residue hq b)
      ((residue_nonzero_iff hp _).mpr ha) ((residue_nonzero_iff hq _).mpr hb)

theorem allPairsInteger_iff (f : Idx → ℤ) : AllPairsInteger f ↔ AllPairsActive f := by
  unfold AllPairsInteger AllPairsActive
  simpa only [Nat.cast_ofNat] using and_congr
    (integer_pair_iff (by decide : (0:ℕ)<3) (by decide : (0:ℕ)<5)
      (by decide : (3:ℕ)*35=105) (by decide : (5:ℕ)*21=105) f)
    (and_congr
      (integer_pair_iff (by decide : (0:ℕ)<3) (by decide : (0:ℕ)<7)
        (by decide : (3:ℕ)*35=105) (by decide : (7:ℕ)*15=105) f)
      (integer_pair_iff (by decide : (0:ℕ)<5) (by decide : (0:ℕ)<7)
        (by decide : (5:ℕ)*21=105) (by decide : (7:ℕ)*15=105) f))

/-- Exact original-scale formulation. The cyclic primitivity field is
independent of the choice of a primitive-word encoding. -/
def IntegerStratum : Set Gap :=
  {e | TopZeroInteger (intGap e) ∧ AllPairsInteger (intGap e) ∧ CyclicPrimitive e}

theorem integerStratum_eq : IntegerStratum = Stratum := by
  ext e
  simp only [IntegerStratum,Stratum,Set.mem_ofPred_eq,topZeroInteger_iff,allPairsInteger_iff]

theorem integer_stratum_not_twoSparseSemilinear : ¬ TwoSparseSemilinear IntegerStratum := by
  rw [integerStratum_eq]
  exact intermediate_stratum_not_twoSparseSemilinear

end Kasonyi105
