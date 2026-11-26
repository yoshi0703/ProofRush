import AttentionLower

namespace AttentionBounds
open AttentionWindows

def B (D j : ℕ) := (D+j).choose j

theorem raise_one (D j : ℕ) : B D (j+1)*(j+1) = (D+j+1)*B D j := by
  simpa only [B,Nat.add_assoc] using (Nat.add_one_mul_choose_eq (D+j) j).symm

theorem at_least_axes (D j : ℕ) : 1+D*j ≤ B D j := by
  induction j with
  | zero => simp [B]
  | succ j ih =>
    have step := raise_one D j
    have diff : D ≤ B D j * D / (j+1) := by
      by_cases h : D=0
      · simp [h]
      · have grown := Nat.mul_le_mul_right j (show 1 ≤ D by omega)
        have bound : j+1 ≤ B D j := by nlinarith
        exact (Nat.le_div_iff_mul_le (Nat.succ_pos j)).2
          (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right D bound)
    have mono : (B D j + D)*(j+1) ≤ B D (j+1)*(j+1) := by
      have := (Nat.le_div_iff_mul_le (Nat.succ_pos j)).1 diff
      nlinarith
    have := Nat.le_of_mul_le_mul_right mono (Nat.succ_pos j)
    nlinarith

/-- A coefficient comparison avoids logarithms and Stirling's formula. -/
theorem scaled (q D r j : ℕ) (hq : 1 ≤ q) (enough : D ≤ q*r) :
    B D j ≤ q^j * B r j := by
  induction j with
  | zero => simp [B]
  | succ j ih =>
    apply Nat.le_of_mul_le_mul_right _ (Nat.succ_pos j)
    have factor : D+j+1 ≤ q*(r+j+1) := by nlinarith
    have prod := Nat.mul_le_mul factor ih
    rw [raise_one, pow_succ]
    calc
      _ ≤ _ := prod
      _ = (q^j*q)*((r+j+1)*B r j) := by ring
      _ = _ := by rw [← raise_one]; exact (Nat.mul_assoc _ _ _).symm

theorem bound_by_blocks {D r q : ℕ} (pos : 1 ≤ q) (cover : D ≤ q*r) :
    B D r ≤ (4*q)^r := by
  have cent := Nat.choose_le_two_pow (r+r) r
  change B r r ≤ _ at cent
  have p : (2:ℕ)^(r+r) = 4^r := by rw [← two_mul, pow_mul]; norm_num
  rw [p] at cent
  apply (scaled q D r r pos cover).trans
  rw [mul_comm 4 q,mul_pow]
  exact Nat.mul_le_mul_left _ cent

/-- An upper dimension of at most 10r via a single mixed-radix basis in
the only regime where the known d≤D upper bound exceeds 32r. -/
theorem radix_parameters {H D r : ℕ} (rp : 0 < r) (degree : 32*r ≤ D)
    (threshold : H ≤ B D r) :
    ∃ b p : ℕ, 0 < b ∧ H ≤ b^p ∧ 2*(p*(b-1)) ≤ D+2 ∧ 2*p+2 ≤ 10*r := by
  let a := D/(8*r)
  let b := a+1
  have a4 : 4 ≤ a := (Nat.le_div_iff_mul_le (by positivity : 0 < 8*r)).2 (by nlinarith)
  have floor := Nat.div_mul_le_self D (8*r)
  have ceil := Nat.lt_mul_div_succ D (by positivity : 0 < 8*r)
  change a*(8*r) ≤ D at floor
  change D < (8*r)*(a+1) at ceil
  have blocks : D ≤ (8*b)*r := by dsimp [b]; nlinarith
  have bpos : 0 < b := Nat.succ_pos _
  have compare : 4*(8*b) ≤ b^4 := by
    have b5 : 5 ≤ b := by dsimp [b]; omega
    have squared := Nat.pow_le_pow_left b5 2
    have cubed := Nat.pow_le_pow_left b5 3
    have quartic := Nat.mul_le_mul_right b cubed
    norm_num at cubed
    nlinarith [show b^4=b^3*b by ring]
  refine ⟨b,4*r,bpos,?_,?_,by omega⟩
  · rw [pow_mul]
    exact threshold.trans ((bound_by_blocks (by omega : 1 ≤ 8*b) blocks).trans
      (Nat.pow_le_pow_left compare r))
  · dsimp [b]
    nlinarith

private theorem exists_threshold (H D : ℕ) : ∃ r, 1 ≤ r ∧ H*D+1 ≤ B D r := by
  refine ⟨max 1 H,le_max_left ..,?_⟩
  have h := at_least_axes D (max 1 H)
  have aux := Nat.mul_le_mul_left D (le_max_right 1 H)
  nlinarith

noncomputable def index (H D : ℕ) : ℕ := Nat.find (exists_threshold H D)

theorem index_spec (H D : ℕ) : 1 ≤ index H D ∧ H*D+1 ≤ B D (index H D) :=
  Nat.find_spec (exists_threshold H D)

theorem index_min {H D j : ℕ} (pos : 1 ≤ j) (enough : H*D+1 ≤ B D j) : index H D ≤ j :=
  Nat.find_min' (exists_threshold H D) ⟨pos,enough⟩

/-- The size of the coefficient chart imposes a joint dimension obstruction. -/
theorem necessary {H D d : ℕ} (dp : 1 ≤ d)
    (enough : H*D ≤ (d+1)*(H+1) + B D d) : min D (index H D) ≤ 3*d := by
  by_cases heads : H ≤ 3
  · have aux := at_least_axes D (max 1 H)
    have h := Nat.mul_le_mul_left D (le_max_right 1 H)
    have cap := index_min (H:=H) (D:=D) (j:=max 1 H) (le_max_left ..) (by nlinarith)
    omega
  by_cases narrow : 2*(d+1) ≤ D
  · have dh := Nat.mul_le_mul_right H narrow
    have four := Nat.mul_le_mul_right (d+1) (show 4 ≤ H by omega)
    have available : H*D+1 ≤ 3*B D d := by nlinarith
    have step := raise_one D d
    have more : 3*(d+1) ≤ D+d+1 := by omega
    have product := Nat.mul_le_mul_right (B D d) more
    have mulBound : (3*B D d)*(d+1) ≤ B D (d+1)*(d+1) := by nlinarith
    have growth := Nat.le_of_mul_le_mul_right mulBound (Nat.succ_pos d)
    have cap := index_min (Nat.succ_pos d) (available.trans growth)
    omega
  · omega

theorem necessary_dimension {H D d : ℕ} (dp : 1 ≤ d) (gap : 3*d < min D (index H D)) :
    Misses H D d := by
  apply insufficient_dimension
  change (d+1)*(H+1)+(d+D).choose D < H*D
  rw [Nat.add_comm d D,Nat.choose_symm_add (a:=D) (b:=d)]
  change (d+1)*(H+1)+B D d < H*D
  by_contra! enough
  exact (Nat.not_lt_of_ge (necessary dp enough)) gap

end AttentionBounds
