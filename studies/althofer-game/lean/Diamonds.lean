import GameTwo

/-! Finite-strategy witnesses for Althöfer Prize 3 and two inverse diamonds. -/
namespace Althofer

def Playable (n : ℤ) : Prop := 1 < n ∧ n % 2 = 1

mutual
  /-- The player to move can earn the terminal win within the ply budget. -/
  def WinsBy : ℕ → ℤ → Prop
    | 0, _ => False
    | k+1, n => Playable n ∧ ∃ s m, Move s n m ∧ (m = 1 ∨ LosesBy k m)

  /-- The other player can earn the terminal win within the ply budget. -/
  def LosesBy : ℕ → ℤ → Prop
    | 0, _ => False
    | k+1, n => Playable n ∧ ∀ s, ∃ m, Move s n m ∧ WinsBy k m
end

def ForcedWin (n : ℤ) : Prop := ∃ k, WinsBy k n

def ForcedLoss (n : ℤ) : Prop := ∃ k, LosesBy k n

theorem winsBy_playable {k : ℕ} {n : ℤ} (h : WinsBy k n) : Playable n := by
  cases k with
  | zero => exact False.elim h
  | succ k => exact h.1

theorem losesBy_playable {k : ℕ} {n : ℤ} (h : LosesBy k n) : Playable n := by
  cases k with
  | zero => exact False.elim h
  | succ k => exact h.1

theorem horizons_disjoint (a b : ℕ) {n : ℤ}
    (win : WinsBy a n) (loss : LosesBy b n) : False := by
  cases a with
  | zero => exact win
  | succ a =>
    cases b with
    | zero => exact loss
    | succ b =>
      obtain ⟨_, s, m, first, terminal | remaining⟩ := win
      · obtain ⟨z, hstep, opponent⟩ := loss.2 s
        have hz : z = 1 := (move_unique hstep first).trans terminal
        have impossible := (winsBy_playable opponent).1
        omega
      · obtain ⟨z, hstep, opponent⟩ := loss.2 s
        have equal := move_unique hstep first
        subst z
        exact horizons_disjoint b a opponent remaining
termination_by a+b
decreasing_by omega

theorem forced_outcomes_disjoint {n : ℤ} (win : ForcedWin n) (loss : ForcedLoss n) : False := by
  obtain ⟨a,ha⟩ := win
  obtain ⟨b,hb⟩ := loss
  exact horizons_disjoint a b ha hb

private theorem move_domain_odd {s : Sign} {n m : ℤ} (hm : Move s n m) : n % 2 = 1 := by
  obtain ⟨_, _, a, ha, eq⟩ := hm
  have a_succ : ∃ b : ℕ, a = b+1 := ⟨a-1, by omega⟩
  obtain ⟨b,rfl⟩ := a_succ
  rw [pow_succ] at eq
  have even_eq : 2*((2 : ℤ)^b*m) = 3*n+s.val := by
    calc
      _ = ((2 : ℤ)^b*2)*m := by ring
      _ = _ := eq
  cases s <;> simp [Sign.val] at even_eq <;> omega

theorem winsBy_one_iff (n : ℤ) : WinsBy 1 n ↔ WinsInOne n := by
  change (Playable n ∧ ∃ s m, Move s n m ∧ (m = 1 ∨ False)) ↔ WinsInOne n
  constructor
  · rintro ⟨⟨n_gt,_⟩, s, m, hm, rfl | empty⟩
    · exact ⟨n_gt, s, hm⟩
    · exact False.elim empty
  · rintro ⟨n_gt,s,hm⟩
    exact ⟨⟨n_gt,move_domain_odd hm⟩, s, 1, hm, Or.inl rfl⟩

theorem losesBy_two_iff (n : ℤ) : LosesBy 2 n ↔ LosesInTwo n := by
  change (Playable n ∧ ∀ s, ∃ m, Move s n m ∧ WinsBy 1 m) ↔ LosesInTwo n
  constructor
  · rintro ⟨⟨ngt,nodd⟩, legs⟩
    refine ⟨ngt,nodd,?_⟩
    intro s
    obtain ⟨m,hm,win⟩ := legs s
    have instant := (winsBy_one_iff m).mp win
    exact ⟨m,hm,instant.1,instant⟩
  · rintro ⟨ngt,nodd,legs⟩
    refine ⟨⟨ngt,nodd⟩,?_⟩
    intro s
    obtain ⟨m,hm,_,win⟩ := legs s
    exact ⟨m,hm,(winsBy_one_iff m).mpr win⟩

theorem winsBy_step {n m : ℤ} {s : Sign} {k : ℕ}
    (live : Playable n) (step : Move s n m) (tail : LosesBy k m) :
    WinsBy (k+1) n :=
  ⟨live, s, m, step, Or.inr tail⟩

private theorem loses_of_common_child {k : ℕ} {n y z g : ℤ} {s sy sz : Sign}
    (live_n : Playable n) (live_y : Playable y) (live_z : Playable z)
    (left : Move s n y) (right : Move s.flip n z)
    (left_reply : Move sy y g) (right_reply : Move sz z g)
    (goal_loss : LosesBy k g) : LosesBy (k+2) n := by
  change Playable n ∧ ∀ sign, ∃ m, Move sign n m ∧ WinsBy (k+1) m
  have left_win := winsBy_step live_y left_reply goal_loss
  have right_win := winsBy_step live_z right_reply goal_loss
  refine ⟨live_n,?_⟩
  cases s <;> intro sign <;> cases sign
  · exact ⟨y,left,left_win⟩
  · exact ⟨z,right,right_win⟩
  · exact ⟨z,right,right_win⟩
  · exact ⟨y,left,left_win⟩

private theorem move_at_power {s : Sign} {n m : ℤ}
    (live : Playable m) (e : ℕ) (e_pos : 0 < e)
    (eq : (2 : ℤ)^e*m = 3*n+s.val) : Move s n m :=
  ⟨lt_trans (by decide : (0 : ℤ) < 1) live.1, live.2, e, e_pos, eq⟩

set_option maxHeartbeats 2000000 in
theorem diamond_eight {k : ℕ} {n g : ℤ} (s : Sign)
    (eq : 9*n = 8*g-s.val)
    (goal_loss : LosesBy k g) : LosesBy (k+2) n := by
  let y := (3*n+s.val)/2
  let z := (3*n+s.flip.val)/4
  have live_g := losesBy_playable goal_loss
  have g_gt := live_g.1
  have g_odd := live_g.2
  have live_n : Playable n := by
    cases s <;> simp only [Playable, Sign.val] at eq ⊢ <;> omega
  have live_y : Playable y := by
    cases s <;> simp only [Playable, y, Sign.val] <;> simp only [Sign.val] at eq <;> omega
  have live_z : Playable z := by
    cases s <;> simp only [Playable, z, Sign.val, Sign.flip] <;>
      simp only [Sign.val] at eq <;> omega
  apply loses_of_common_child (s := s) (sy := s.flip) (sz := s)
    live_n live_y live_z _ _ _ _ goal_loss
  · apply move_at_power live_y 1 (by decide)
    cases s <;> norm_num [y, Sign.val] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_z 2 (by decide)
    cases s <;> norm_num [z, Sign.val, Sign.flip] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_g 2 (by decide)
    cases s <;> norm_num [y, Sign.val, Sign.flip] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_g 1 (by decide)
    cases s <;> norm_num [z, Sign.val, Sign.flip] <;> simp only [Sign.val] at eq <;> omega

set_option maxHeartbeats 2000000 in
theorem diamond_sixteen {k : ℕ} {n g : ℤ} (s : Sign)
    (eq : 9*n = 16*g-5*s.val)
    (goal_loss : LosesBy k g) : LosesBy (k+2) n := by
  let y := (3*n+s.val)/2
  let z := (3*n+s.flip.val)/8
  have live_g := losesBy_playable goal_loss
  have g_gt := live_g.1
  have g_odd := live_g.2
  have live_n : Playable n := by
    cases s <;> simp only [Playable, Sign.val] at eq ⊢ <;> omega
  have live_y : Playable y := by
    cases s <;> simp only [Playable, y, Sign.val] <;> simp only [Sign.val] at eq <;> omega
  have live_z : Playable z := by
    cases s <;> simp only [Playable, z, Sign.val, Sign.flip] <;>
      simp only [Sign.val] at eq <;> omega
  apply loses_of_common_child (s := s) (sy := s) (sz := s)
    live_n live_y live_z _ _ _ _ goal_loss
  · apply move_at_power live_y 1 (by decide)
    cases s <;> norm_num [y, Sign.val] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_z 3 (by decide)
    cases s <;> norm_num [z, Sign.val, Sign.flip] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_g 3 (by decide)
    cases s <;> norm_num [y, Sign.val] <;> simp only [Sign.val] at eq <;> omega
  · apply move_at_power live_g 1 (by decide)
    cases s <;> norm_num [z, Sign.val, Sign.flip] <;> simp only [Sign.val] at eq <;> omega

theorem win_from_loss {k : ℕ} {w g : ℤ} (s : Sign)
    (eq : 3*w = 2*g-s.val) (goal_loss : LosesBy k g) :
    WinsBy (k+1) w := by
  have live_g := losesBy_playable goal_loss
  have g_gt := live_g.1
  have g_odd := live_g.2
  have live_w : Playable w := by
    cases s <;> simp only [Playable, Sign.val] at eq ⊢ <;> omega
  apply winsBy_step (s := s) live_w _ goal_loss
  apply move_at_power live_g 1 (by decide)
  norm_num
  omega

theorem forced_loss_diamond_eight {n g : ℤ} (s : Sign)
    (eq : 9*n = 8*g-s.val)
    (goal_loss : ForcedLoss g) : ForcedLoss n := by
  obtain ⟨k,loss⟩ := goal_loss
  exact ⟨k+2,diamond_eight s eq loss⟩

theorem forced_loss_diamond_sixteen {n g : ℤ} (s : Sign)
    (eq : 9*n = 16*g-5*s.val)
    (goal_loss : ForcedLoss g) : ForcedLoss n := by
  obtain ⟨k,loss⟩ := goal_loss
  exact ⟨k+2,diamond_sixteen s eq loss⟩

theorem forced_win_from_loss {w g : ℤ} (s : Sign)
    (eq : 3*w = 2*g-s.val) (goal_loss : ForcedLoss g) :
    ForcedWin w := by
  obtain ⟨k,loss⟩ := goal_loss
  exact ⟨k+1,win_from_loss s eq loss⟩

end Althofer
