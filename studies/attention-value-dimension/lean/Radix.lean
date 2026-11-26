import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-! The radix-and-complement construction of Hsu–Xu Lemma 14, with zero
included as a separate monomial feature for padding. -/
namespace AttentionUpper

/-- Explicit base-b digit expansion as a list of powers, retaining
multiplicity rather than a digit array. -/
def radixTerms (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | p+1, n => List.replicate (n % b) 1 ++ (radixTerms b p (n / b)).map (b * ·)

private theorem sum_scale (b : Nat) (xs : List Nat) :
    (xs.map (b * ·)).sum = b * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

theorem radixTerms_sum {b n p : Nat} (base : 0 < b) (below : n < b^p) :
    (radixTerms b p n).sum = n := by
  induction p generalizing n with
  | zero =>
    have eq : n = 0 := by simp at below; omega
    simp [radixTerms, eq]
  | succ p ih =>
    have quotient : n / b < b^p := (Nat.div_lt_iff_lt_mul base).mpr
      (by simpa [Nat.pow_succ] using below)
    simp only [radixTerms, List.sum_append, List.sum_replicate_nat, Nat.mul_one, sum_scale, ih quotient]
    exact Nat.mod_add_div n b

theorem radixTerms_length {b : Nat} (base : 0 < b) (p n : Nat) :
    (radixTerms b p n).length ≤ p * (b-1) := by
  induction p generalizing n with
  | zero => simp [radixTerms]
  | succ p ih =>
    simp only [radixTerms, List.length_append, List.length_replicate, List.length_map]
    have digit : n % b ≤ b-1 := by
      have bounded := Nat.mod_lt n base
      omega
    exact (Nat.add_le_add digit (ih (n/b))).trans_eq (by simp [Nat.succ_mul, Nat.add_comm])

theorem radixTerms_power {b p n x : Nat} (member : x ∈ radixTerms b p n) :
    ∃ index < p, x = b ^ index := by
  induction p generalizing n x with
  | zero => simp [radixTerms] at member
  | succ p ih =>
    simp only [radixTerms, List.mem_append, List.mem_replicate, List.mem_map] at member
    rcases member with ⟨_,rfl⟩ | ⟨y, hy, rfl⟩
    · exact ⟨0, Nat.zero_lt_succ p, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := ih hy
      exact ⟨i+1, Nat.succ_lt_succ hi, by rw [Nat.pow_succ, Nat.mul_comm]⟩

private theorem listTerm_le_sum {xs : List Nat} {x : Nat} (member : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at member
  | cons a rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp
    · simpa only [List.sum_cons] using (ih later).trans (Nat.le_add_left rest.sum a)

def lowBasis (H b p : Nat) : Finset Nat :=
  ((Finset.range p).image fun j => b^j).filter (· < H)

def withComplements (H : Nat) (low : Finset Nat) : Finset Nat :=
  insert 0 (insert H (low ∪ low.image (H - ·)))

def radixBasis (H b p : Nat) : Finset Nat := withComplements H (lowBasis H b p)

theorem radixTerms_in_lowBasis {H b p r : Nat} (base : 0 < b) (covers : H ≤ b^p) (rlt : r < H) :
    ∀ x ∈ radixTerms b p r, x ∈ lowBasis H b p := by
  intro x hx
  have sum := radixTerms_sum base (rlt.trans_le covers)
  have small := listTerm_le_sum hx
  rw [sum] at small
  obtain ⟨j, hj, equality⟩ := radixTerms_power hx
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, equality.symm⟩, small.trans_lt rlt⟩

private theorem sum_complement (H : Nat) (xs : List Nat) (bounded : ∀ x ∈ xs, x ≤ H) :
    (xs.map (H - ·)).sum + xs.sum = xs.length * H := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
    have top := bounded x (by simp)
    have rest := ih (fun i hi => bounded i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Once each sub-H remainder has a short expansion, the complementary
digits fill all exponents through HD. This is precisely the two-case
argument underlying Hsu–Xu Lemma 14. -/
theorem complement_cover {H D M : Nat} {low : Finset Nat}
    (positive : 0 < H) (bound : ∀ b ∈ low, b ≤ H)
    (adequate : 2*M ≤ D+2)
    (small : ∀ r < H, ∃ xs : List Nat, xs.length ≤ M ∧ xs.sum = r ∧ ∀ x ∈ xs, x ∈ low)
    {e : Nat} (eb : e ≤ H*D) :
    ∃ xs : List Nat, xs.length ≤ D ∧ xs.sum = e ∧ ∀ x ∈ xs, x ∈ withComplements H low := by
  let q := e/H
  let r := e%H
  have rBound : r < H := Nat.mod_lt e positive
  have qBound : q ≤ D := Nat.div_le_of_le_mul eb
  have division : r+H*q = e := Nat.mod_add_div e H
  have useHead : H ∈ withComplements H low := by simp [withComplements]
  have useLow (x : Nat) (hx : x ∈ low) : x ∈ withComplements H low := by
    simp [withComplements, hx]
  have useComplement (x : Nat) (hx : x ∈ low) : H-x ∈ withComplements H low := by
    have present : H-x ∈ low.image (H - ·) := Finset.mem_image_of_mem _ hx
    simp [withComplements, present]
  by_cases zero : r = 0
  · refine ⟨List.replicate q H, by simpa using qBound, ?_, ?_⟩
    · simpa [zero, Nat.mul_comm] using division
    · intro x hx
      exact (List.mem_replicate.mp hx).2 ▸ useHead
  · have qStrict : q < D := by
      by_contra! contrary
      have equal : q = D := Nat.le_antisymm qBound contrary
      rw [equal] at division
      omega
    by_cases enough : q+M ≤ D
    · obtain ⟨xs, len, sum, included⟩ := small r rBound
      refine ⟨List.replicate q H ++ xs, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_replicate]
        omega
      · simpa [sum, Nat.mul_comm, Nat.add_comm] using division
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact (List.mem_replicate.mp h).2 ▸ useHead
        · exact useLow x (included x h)
    · have remPos : 0 < r := by omega
      have complementLT : H-r < H := by omega
      obtain ⟨xs, mBound, sum, included⟩ := small (H-r) complementLT
      let m := xs.length
      have mLe : m ≤ q+1 := by
        dsimp [m]
        omega
      have subSum := sum_complement H xs (fun x hx => bound x (included x hx))
      rw [sum] at subSum
      have joined : (q+1-m)*H + m*H = H*q+H := by
        rw [← Nat.add_mul, Nat.sub_add_cancel mLe, Nat.add_mul, Nat.one_mul, Nat.mul_comm q H]
      refine ⟨List.replicate (q+1-m) H ++ xs.map (H - ·), ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_replicate, List.length_map]
        change q+1-m + m ≤ D
        omega
      · simp only [List.sum_append, List.sum_replicate_nat]
        change (q+1-m)*H + (xs.map (H - ·)).sum = e
        change (xs.map (H - ·)).sum + (H-r) = m*H at subSum
        omega
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact (List.mem_replicate.mp h).2 ▸ useHead
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
          exact useComplement y (included y hy)

theorem radixBasis_bounded (H b p : Nat) : ∀ x ∈ radixBasis H b p, x ≤ H := by
  intro x hx
  simp only [radixBasis, withComplements, Finset.mem_insert, Finset.mem_union] at hx
  rcases hx with rfl | rfl | low | high
  · exact Nat.zero_le _
  · exact Nat.le_refl _
  · exact (Finset.mem_filter.mp low).2.le
  · obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp high
    exact Nat.sub_le ..

theorem radixBasis_card_le (H b p : Nat) : (radixBasis H b p).card ≤ 2*p+2 := by
  let low := lowBasis H b p
  have lowBound : low.card ≤ p := calc
    low.card ≤ ((Finset.range p).image fun j => b^j).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range p).card := Finset.card_image_le
    _ = p := Finset.card_range p
  have complementary := Finset.card_image_le (s := low) (f := (H - ·))
  have total := Finset.card_union_le low (low.image (H - ·))
  have insertHead := Finset.card_insert_le H (low ∪ low.image (H - ·))
  have insertZero := Finset.card_insert_le 0 (insert H (low ∪ low.image (H - ·)))
  change (insert 0 (insert H (low ∪ low.image (H - ·)))).card ≤ 2*p+2
  omega

/-- Full coverage with exactly D terms, including zero for padding. The
radix assumption is H ≤ b^p, so b may be the cited ceiling root. -/
theorem radixBasis_cover {H b p D : Nat} (heads : 0 < H) (base : 0 < b)
    (covers : H ≤ b^p) (adequate : 2*(p*(b-1)) ≤ D+2) {e : Nat} (eb : e ≤ H*D) :
    ∃ xs : List Nat, xs.length = D ∧ xs.sum = e ∧ ∀ x ∈ xs, x ∈ radixBasis H b p := by
  have short (r : Nat) (rlt : r < H) : ∃ xs : List Nat, xs.length ≤ p*(b-1) ∧
      xs.sum = r ∧ ∀ x ∈ xs, x ∈ lowBasis H b p :=
    ⟨radixTerms b p r, radixTerms_length base p r,
      radixTerms_sum base (rlt.trans_le covers), radixTerms_in_lowBasis base covers rlt⟩
  have bound (x : Nat) (hx : x ∈ lowBasis H b p) : x ≤ H := (Finset.mem_filter.mp hx).2.le
  obtain ⟨xs, len, sum, good⟩ := complement_cover heads bound adequate short eb
  refine ⟨xs ++ List.replicate (D-xs.length) 0, ?_, ?_, ?_⟩
  · simp [Nat.add_sub_of_le len]
  · simp [sum]
  · intro x hx
    rcases List.mem_append.mp hx with regular | pad
    · exact good x regular
    · have eq := (List.mem_replicate.mp pad).2
      subst x
      simp [radixBasis, withComplements]

#print axioms radixBasis_card_le
#print axioms radixBasis_cover

end AttentionUpper
