import GridStridePath

namespace GridCover.AxisPieces

open PathEmbedding
open PathEmbedding.Stride17

def row (i : ℕ) : Center := ((i : ℤ), 0)
def full (n : ℕ) (l r : Bool) : List Center :=
  row 0 :: internal n l r false ++ [row (34*n)]

def axisPoint (n : ℕ) (l r : Bool) (i : ℕ) : Prop :=
  i ≤ 34*n ∧ (l = false ∨ i ≠ 1) ∧ (r = false ∨ i+1 ≠ 34*n) ∧
    (useSwitch l r = false ∨ i < 16 ∨ 19 ≤ i)

def axisUnit (n : ℕ) (l r : Bool) (i : ℕ) : Prop :=
  1 + skip l ≤ i ∧ i+1 < 34*n - skip r ∧
    (useSwitch l r = false ∨ i < 15 ∨ 19 ≤ i)

def jogPoint (p : Center) : Prop := p = (17,1) ∨ p = (17,-1)

def jogEdge (p q : Center) : Prop :=
  (p = row 15 ∧ q = (17,1)) ∨ (p = (17,1) ∧ q = (17,-1)) ∨
  (p = (17,-1) ∧ q = row 19)

def corePoint (n : ℕ) (l r : Bool) (k : ℕ) (p : Center) : Prop :=
  (∃ i, axisPoint n l r i ∧ 17*k ≤ i+3 ∧ i ≤ 17*k+3 ∧ p = row i) ∨
  (k = 1 ∧ useSwitch l r = true ∧ jogPoint p)

def coreLink (n : ℕ) (l r : Bool) (k : ℕ) (p q : Center) : Prop :=
  (∃ i, axisUnit n l r i ∧ 17*k ≤ i+3 ∧ i+1 ≤ 17*k+3 ∧ p = row i ∧ q = row (i+1)) ∨
  (k = 0 ∧ p = row 0 ∧ q = row (1 + skip l)) ∨
  (k = 2*n ∧ p = row (34*n - skip r - 1) ∧ q = row (34*n)) ∨
  (k = 1 ∧ useSwitch l r = true ∧ jogEdge p q)

def stripPoint (k : ℕ) (p : Center) : Prop :=
  ∃ i, 17*k+4 ≤ i ∧ i ≤ 17*k+13 ∧ p = row i

def stripLink (k : ℕ) (p q : Center) : Prop :=
  ∃ i, 17*k+3 ≤ i ∧ i ≤ 17*k+13 ∧ p = row i ∧ q = row (i+1)

theorem strip_axisPoint {n k i : ℕ} {l r : Bool} (hk : k < 2*n)
    (lo : 17*k+4 ≤ i) (hi : i ≤ 17*k+13) : axisPoint n l r i := by
  have side : k = 0 ∨ 1 ≤ k := by omega
  unfold axisPoint
  rcases side with rfl | h <;> omega

theorem strip_axisUnit {n k i : ℕ} {l r : Bool} (hk : k < 2*n)
    (lo : 17*k+3 ≤ i) (hi : i ≤ 17*k+13) : axisUnit n l r i := by
  have side : k = 0 ∨ 1 ≤ k := by omega
  have hl := skip_le l
  have hr := skip_le r
  unfold axisUnit
  rcases side with rfl | h <;> omega

theorem point_partition {n i : ℕ} (hi : i ≤ 34*n) :
    (∃ k ≤ 2*n, 17*k ≤ i+3 ∧ i ≤ 17*k+3) ∨
    ∃ k < 2*n, 17*k+4 ≤ i ∧ i ≤ 17*k+13 := by
  let k := (i+3) / 17
  have nearLo : 17*k ≤ i+3 := by dsimp [k]; omega
  have nearHi : i ≤ 17*k+13 := by dsimp [k]; omega
  by_cases hc : i ≤ 17*k+3
  · exact Or.inl ⟨k, by omega, nearLo, hc⟩
  · exact Or.inr ⟨k, by omega, by omega, nearHi⟩

theorem link_partition {n i : ℕ} (hi : i < 34*n) :
    (∃ k ≤ 2*n, 17*k ≤ i+3 ∧ i+1 ≤ 17*k+3) ∨
    ∃ k < 2*n, 17*k+3 ≤ i ∧ i ≤ 17*k+13 := by
  let k := (i+3) / 17
  have nearLo : 17*k ≤ i+3 := by dsimp [k]; omega
  have nearHi : i ≤ 17*k+13 := by dsimp [k]; omega
  by_cases hc : i+1 ≤ 17*k+3
  · exact Or.inl ⟨k, by omega, nearLo, hc⟩
  · exact Or.inr ⟨k, by omega, by omega, nearHi⟩

private theorem ends_or_interior {n i : ℕ} (hn : 1 ≤ n) (l r : Bool) :
    axisPoint n l r i ↔ i = 0 ∨ i = 34*n ∨
      (1 + skip l ≤ i ∧ i < 34*n - skip r ∧
        (useSwitch l r = false ∨ i < 16 ∨ 19 ≤ i)) := by
  cases l <;> cases r <;> simp [axisPoint, useSwitch, skip] <;> omega

theorem full_point_iff {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p : Center) :
    p ∈ full n l r ↔ (∃ i, axisPoint n l r i ∧ p = row i) ∨
      (useSwitch l r = true ∧ jogPoint p) := by
  simp only [full, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
    internal_mem_iff hn, jogPoint]
  constructor
  · rintro ((zero | (⟨i,hl,hr,hg,eq⟩ | jogged)) | last)
    · exact Or.inl ⟨0, (ends_or_interior hn l r).mpr (Or.inl rfl), zero⟩
    · exact Or.inl ⟨i, (ends_or_interior hn l r).mpr (Or.inr (Or.inr ⟨hl,hr,hg⟩)), eq⟩
    · exact Or.inr jogged
    · exact Or.inl ⟨_, (ends_or_interior hn l r).mpr (Or.inr (Or.inl rfl)), last⟩
  · rintro (⟨i, ha, eq⟩ | hj)
    · rcases (ends_or_interior hn l r).mp ha with rfl | rfl | ⟨hl,hr,hg⟩
      · exact Or.inl (Or.inl eq)
      · exact Or.inr eq
      · exact Or.inl (Or.inr (Or.inl ⟨i,hl,hr,hg,eq⟩))
    · exact Or.inl (Or.inr (Or.inr hj))

theorem point_pieces_iff {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p : Center) :
    p ∈ full n l r ↔ (∃ k ≤ 2*n, corePoint n l r k p) ∨ ∃ k < 2*n, stripPoint k p := by
  rw [full_point_iff hn]
  constructor
  · rintro (⟨i,ha,eq⟩ | ⟨hs,hj⟩)
    · rcases point_partition ha.1 with ⟨k,hk,hl,hr⟩ | ⟨k,hk,hl,hr⟩
      · exact Or.inl ⟨k,hk,Or.inl ⟨i,ha,hl,hr,eq⟩⟩
      · exact Or.inr ⟨k,hk,i,hl,hr,eq⟩
    · exact Or.inl ⟨1,by omega,Or.inr ⟨rfl,hs,hj⟩⟩
  · rintro (⟨k,hk,hc⟩ | ⟨k,hk,i,hl,hr,eq⟩)
    · rcases hc with ⟨i,ha,_,_,eq⟩ | ⟨_,hs,hj⟩
      · exact Or.inl ⟨i,ha,eq⟩
      · exact Or.inr ⟨hs,hj⟩
    · exact Or.inl ⟨i,strip_axisPoint hk hl hr,eq⟩

private theorem axial_succ (s m : ℕ) : axial s (m+1) = row s :: axial (s+1) m := by
  rfl

private theorem pairs_range (s count : ℕ) (rest : List Center) (last : Center)
    (e : Center × Center) :
    e ∈ pairs (row s) (axial (s+1) count ++ rest) last ↔
      (∃ i, s ≤ i ∧ i < s+count ∧ e = (row i, row (i+1))) ∨
      e ∈ pairs (row (s+count)) rest last := by
  induction count generalizing s with
  | zero =>
    simp [axial]
    intro i lo hi
    omega
  | succ m ih =>
    rw [axial_succ, List.cons_append, pairs, List.mem_cons, ih]
    have h : s+1+m = s+(m+1) := by omega
    rw [h]
    constructor
    · rintro (he | ⟨i,lo,hi,he⟩ | tail)
      · exact Or.inl ⟨s,by omega,by omega,he⟩
      · exact Or.inl ⟨i,by omega,hi,he⟩
      · exact Or.inr tail
    · rintro (⟨i,lo,hi,he⟩ | tail)
      · by_cases eq : i = s
        · exact Or.inl (eq ▸ he)
        · exact Or.inr (Or.inl ⟨i,by omega,hi,he⟩)
      · exact Or.inr (Or.inr tail)

private theorem pairs_block (s m : ℕ) (hm : 0 < m) (left : Center) (rest : List Center)
    (last : Center) (e : Center × Center) :
    e ∈ pairs left (axial s m ++ rest) last ↔
    e = (left,row s) ∨ (∃ i, s ≤ i ∧ i+1 < s+m ∧ e = (row i,row (i+1))) ∨
      e ∈ pairs (row (s+m-1)) rest last := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [axial_succ, List.cons_append, pairs, List.mem_cons, pairs_range]
  simp only [Nat.succ_eq_add_one]
  have h : s+(m+1)-1 = s+m := by omega
  rw [h]
  apply or_congr_right
  apply or_congr_left
  apply exists_congr
  intro i
  have h' : i < s+m ↔ i+1 < s+(m+1) := by omega
  rw [h']

private theorem pairs_singleBlock (s m : ℕ) (hm : 0 < m) (left last : Center)
    (e : Center × Center) :
    e ∈ pairs left (axial s m) last ↔
    e = (left,row s) ∨ (∃ i, s ≤ i ∧ i+1 < s+m ∧ e = (row i,row (i+1))) ∨
      e = (row (s+m-1),last) := by
  simpa only [List.append_nil, pairs, List.mem_singleton] using
    pairs_block s m hm left [] last e

private theorem switched_block (s b : ℕ) (hs : s ≤ 2) (hb : 20 ≤ b)
    (left last : Center) (e : Center × Center) :
    e ∈ pairs left (axial s (16-s) ++ jog false ++ axial 19 (b-19)) last ↔
    e = (left,row s) ∨ e = (row (b-1),last) ∨
    (∃ i, s ≤ i ∧ i+1 < b ∧ (i < 15 ∨ 19 ≤ i) ∧ e = (row i,row (i+1))) ∨
    e = (row 15,(17,1)) ∨ e = ((17,1),(17,-1)) ∨ e = ((17,-1),row 19) := by
  have hpre : s+(16-s) = 16 := by omega
  have hpost : 19+(b-19) = b := by omega
  simp only [List.append_assoc]
  rw [pairs_block s (16-s) (by omega),hpre]
  simp only [jog, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
    pairs, List.mem_cons]
  rw [pairs_singleBlock 19 (b-19) (by omega),hpost]
  have ranges : ((∃ i, s ≤ i ∧ i+1 < 16 ∧ e = (row i,row (i+1))) ∨
      (∃ i, 19 ≤ i ∧ i+1 < b ∧ e = (row i,row (i+1)))) ↔
      ∃ i, s ≤ i ∧ i+1 < b ∧ (i < 15 ∨ 19 ≤ i) ∧ e = (row i,row (i+1)) := by
    constructor
    · rintro (⟨i,lo,hi,eq⟩ | ⟨i,lo,hi,eq⟩)
      · exact ⟨i,lo,by omega,Or.inl (by omega),eq⟩
      · exact ⟨i,by omega,hi,Or.inr lo,eq⟩
    · rintro ⟨i,lo,hi,side,eq⟩
      rcases side with h | h
      · exact Or.inl ⟨i,lo,by omega,eq⟩
      · exact Or.inr ⟨i,h,hi,eq⟩
  rw [← ranges]
  simp only [or_comm, or_left_comm, or_assoc]

theorem full_link_iff {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p q : Center) :
    (p,q) ∈ pairs (row 0) (internal n l r false) (row (34*n)) ↔
    (p = row 0 ∧ q = row (1+skip l)) ∨
    (p = row (34*n-skip r-1) ∧ q = row (34*n)) ∨
    (∃ i, axisUnit n l r i ∧ p = row i ∧ q = row (i+1)) ∨
    (useSwitch l r = true ∧ jogEdge p q) := by
  have hl := skip_le l
  have hr := skip_le r
  cases sw : useSwitch l r with
  | false =>
    have fb : (1+skip l) + (34*n-skip r-(1+skip l)) = 34*n-skip r := by omega
    simp only [internal, sw, Bool.false_eq_true, ite_false]
    rw [pairs_singleBlock _ _ (by omega),fb]
    simp only [Prod.mk.injEq, axisUnit, sw, true_or, and_true, false_and, or_false, and_assoc]
    exact or_congr_right or_comm
  | true =>
    simp only [internal, sw, ite_true, true_and]
    rw [switched_block _ _ (by omega) (by omega)]
    simp only [axisUnit, sw, Bool.true_eq_false, false_or, Prod.mk.injEq, jogEdge, and_assoc]

theorem link_pieces_iff {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p q : Center) :
    (p,q) ∈ pairs (row 0) (internal n l r false) (row (34*n)) ↔
    (∃ k ≤ 2*n, coreLink n l r k p q) ∨ ∃ k < 2*n, stripLink k p q := by
  rw [full_link_iff hn]
  constructor
  · rintro (⟨hp,hq⟩ | ⟨hp,hq⟩ | ⟨i,ha,hp,hq⟩ | ⟨hs,hj⟩)
    · exact Or.inl ⟨0, by omega, Or.inr (Or.inl ⟨rfl,hp,hq⟩)⟩
    · exact Or.inl ⟨2*n, le_refl _, Or.inr (Or.inr (Or.inl ⟨rfl,hp,hq⟩))⟩
    · have hi := ha.2.1
      rcases link_partition (n:=n) (i:=i) (by omega) with ⟨k,hk,lo,up⟩ | ⟨k,hk,lo,up⟩
      · exact Or.inl ⟨k,hk,Or.inl ⟨i,ha,lo,up,hp,hq⟩⟩
      · exact Or.inr ⟨k,hk,i,lo,up,hp,hq⟩
    · exact Or.inl ⟨1,by omega,Or.inr (Or.inr (Or.inr ⟨rfl,hs,hj⟩))⟩
  · rintro (⟨k,_,hc⟩ | ⟨k,hk,i,lo,up,hp,hq⟩)
    · rcases hc with ⟨i,ha,_,_,hp,hq⟩ | ⟨_,hp,hq⟩ | ⟨_,hp,hq⟩ | ⟨_,hs,hj⟩
      · exact Or.inr (Or.inr (Or.inl ⟨i,ha,hp,hq⟩))
      · exact Or.inl ⟨hp,hq⟩
      · exact Or.inr (Or.inl ⟨hp,hq⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hs,hj⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨i,strip_axisUnit hk lo up,hp,hq⟩))

end GridCover.AxisPieces
