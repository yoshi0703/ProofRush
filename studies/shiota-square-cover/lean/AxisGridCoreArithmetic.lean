import GridCorePaths
import GridAxisPieces

namespace GridCover.AxisPieces

open GridCover.Placement GridCover.CorePaths GridCover.PathEmbedding.Stride17

def centered (k : ℕ) (p : Center) : Center := (p.1 - (17 : ℤ)*k, p.2)

def pairMem (path : List Center) (p q : Center) : Prop :=
  (p,q) ∈ path.zip path.tail ∨ (q,p) ∈ path.zip path.tail

syntax "choose_linear_case" : tactic
syntax "explode_linear" ident : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| choose_linear_case) => do
    if (← Lean.Meta.whnf (← getMainTarget)).consumeMData.isAppOfArity ``Or 2 then
      evalTactic (← `(tactic| first | (left; choose_linear_case) | (right; choose_linear_case)))
    else
      evalTactic (← `(tactic| omega))
  | `(tactic| explode_linear $h:ident) => withMainContext do
    let f ← getFVarId h
    let ty := (← Lean.Meta.whnf (← f.getDecl).type).consumeMData
    let term : TSyntax `term := ⟨h.raw⟩
    if ty.isAppOfArity ``Or 2 then
      evalTactic (← `(tactic|
        rcases ($term) with hleft | hright <;>
          first | explode_linear hleft | explode_linear hright))
    else if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic|
        rcases ($term) with ⟨hleft,hright⟩
        <;> explode_linear hleft <;> explode_linear hright))

macro "solve_link_cases" x:term : tactic =>
  `(tactic| constructor <;> intro h <;> explode_linear h <;>
    first
    | choose_linear_case
    | have xi : ($x : ℤ) = -3 ∨ ($x : ℤ) = -2 ∨ ($x : ℤ) = -1 ∨ ($x : ℤ) = 0 ∨
          ($x : ℤ) = 1 ∨ ($x : ℤ) = 2 ∨ ($x : ℤ) = 3 := by omega
      explode_linear xi <;> first | choose_linear_case | omega)

private theorem indexed_point {P : ℕ → Prop} (x y : ℤ) :
    (∃ i, P i ∧ (x,y) = row i) ↔ 0 ≤ x ∧ P x.toNat ∧ y = 0 := by
  constructor
  · rintro ⟨i,hi,h⟩
    have h := Prod.mk.inj h
    change x = (i : ℤ) ∧ y = 0 at h
    have hx : x.toNat = i := by omega
    exact ⟨by omega,hx.symm ▸ hi,h.2⟩
  · rintro ⟨hx,hp,hy⟩
    exact ⟨x.toNat,hp,Prod.ext (by simp [row]; omega) (by simpa [row] using hy)⟩

private theorem indexed_link {P : ℕ → Prop} (x y z w : ℤ) :
    (∃ i, P i ∧ (x,y) = row i ∧ (z,w) = row (i+1)) ↔
    0 ≤ x ∧ P x.toNat ∧ y = 0 ∧ z = x+1 ∧ w = 0 := by
  constructor
  · rintro ⟨i,hi,h,g⟩
    have h1 : x = (i : ℤ) := congrArg Prod.fst h
    have h2 : y = 0 := congrArg Prod.snd h
    have g1 : z = ((i+1 : ℕ) : ℤ) := congrArg Prod.fst g
    have g2 : w = 0 := congrArg Prod.snd g
    have hi' : x.toNat = i := by omega
    exact ⟨by omega,hi'.symm ▸ hi,h2,by omega,g2⟩
  · rintro ⟨hx,hp,hy,hz,hw⟩
    refine ⟨x.toNat,hp,Prod.ext ?_ hy,Prod.ext ?_ hw⟩
    · change x = ((x.toNat : ℕ) : ℤ)
      omega
    · change z = ((x.toNat+1 : ℕ) : ℤ)
      omega

private theorem window_point (n k : ℕ) (l r : Bool) (x y : ℤ) :
    (∃ i, axisPoint n l r i ∧ 17*k ≤ i+3 ∧ i ≤ 17*k+3 ∧ (x,y) = row i) ↔
    0 ≤ x ∧ (axisPoint n l r x.toNat ∧ 17*k ≤ x.toNat+3 ∧ x.toNat ≤ 17*k+3) ∧ y = 0 := by
  simpa only [and_assoc] using indexed_point
    (P := fun i => axisPoint n l r i ∧ 17*k ≤ i+3 ∧ i ≤ 17*k+3) x y

private theorem window_link (n k : ℕ) (l r : Bool) (x y z w : ℤ) :
    (∃ i, axisUnit n l r i ∧ 17*k ≤ i+3 ∧ i+1 ≤ 17*k+3 ∧ (x,y) = row i ∧ (z,w) = row (i+1)) ↔
    0 ≤ x ∧ (axisUnit n l r x.toNat ∧ 17*k ≤ x.toNat+3 ∧ x.toNat+1 ≤ 17*k+3) ∧
      y = 0 ∧ z = x+1 ∧ w = 0 := by
  simpa only [and_assoc] using indexed_link
    (P := fun i => axisUnit n l r i ∧ 17*k ≤ i+3 ∧ i+1 ≤ 17*k+3) x y z w

set_option maxHeartbeats 1000000 in
theorem corePoint_left {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p : Center) :
    corePoint n l r 0 p ↔ p ∈ arm .east l := by
  rcases p with ⟨x,y⟩
  unfold corePoint
  rw [window_point]
  cases l <;> cases r <;>
    simp [arm, Direction.atSite, axisPoint, useSwitch] <;> omega

set_option maxHeartbeats 1000000 in
theorem corePoint_right {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p : Center) :
    corePoint n l r (2*n) p ↔ centered (2*n) p ∈ arm .west r := by
  rcases p with ⟨x,y⟩
  unfold corePoint
  rw [window_point]
  cases l <;> cases r <;>
    simp [arm, centered, Direction.atSite, axisPoint, useSwitch] <;> omega

set_option maxHeartbeats 1000000 in
theorem coreLink_left {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p q : Center) :
    (coreLink n l r 0 p q ∨ coreLink n l r 0 q p) ↔ pairMem (arm .east l) p q := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨z,w⟩
  unfold coreLink
  simp only [window_link]
  cases l <;> cases r <;>
    simp [pairMem, arm, Direction.atSite, axisUnit, useSwitch, skip, row, Prod.mk.injEq] <;>
    solve_link_cases x

set_option maxHeartbeats 1000000 in
theorem coreLink_right {n : ℕ} (hn : 1 ≤ n) (l r : Bool) (p q : Center) :
    (coreLink n l r (2*n) p q ∨ coreLink n l r (2*n) q p) ↔
    pairMem (arm .west r) (centered (2*n) p) (centered (2*n) q) := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨z,w⟩
  unfold coreLink
  simp only [window_link]
  cases l <;> cases r <;>
    simp [pairMem, centered, arm, Direction.atSite, axisUnit, useSwitch, skip, row, Prod.mk.injEq] <;>
    solve_link_cases (x - 34 * (n : ℤ))

def isSwitchIndex (l r : Bool) (i : ℕ) : Bool := useSwitch l r && (i == 1)

def corePaths (b : Bool) : List (List Center) := if b then [switchPath] else linePaths

set_option maxHeartbeats 1000000 in
theorem corePoint_inside {n k : ℕ} (hk0 : 0 < k) (hkl : k < 2*n) (l r : Bool)
    (p : Center) :
    corePoint n l r k p ↔ centered k p ∈ skeletonPoints (corePaths (isSwitchIndex l r k)) := by
  rcases p with ⟨x,y⟩
  unfold corePoint
  rw [window_point]
  by_cases sw : k = 1
  · subst k
    cases l <;> cases r <;>
      simp [isSwitchIndex, skeletonPoints, corePaths, linePaths, switchPath, arm,
        centered, Direction.atSite, axisPoint, useSwitch, jogPoint, Prod.mk.injEq] <;> omega
  · cases l <;> cases r <;>
      simp [sw, isSwitchIndex, skeletonPoints, corePaths, linePaths, arm,
        centered, Direction.atSite, axisPoint, useSwitch, jogPoint, Prod.mk.injEq] <;> omega

set_option maxHeartbeats 1400000 in
theorem coreLink_inside {n k : ℕ} (hk0 : 0 < k) (hkl : k < 2*n) (l r : Bool)
    (p q : Center) :
    (coreLink n l r k p q ∨ coreLink n l r k q p) ↔
    ∃ path ∈ corePaths (isSwitchIndex l r k), pairMem path (centered k p) (centered k q) := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨z,w⟩
  unfold coreLink
  simp only [window_link]
  by_cases sw : k = 1
  · subst k
    cases l <;> cases r <;>
      simp [isSwitchIndex, pairMem, corePaths, linePaths, switchPath, arm, centered,
        Direction.atSite, axisUnit, useSwitch, skip, row, jogEdge, Prod.mk.injEq] <;>
      solve_link_cases (x - 17)
  · cases l <;> cases r <;>
      simp [sw, isSwitchIndex, pairMem, corePaths, linePaths, arm, centered,
        Direction.atSite, axisUnit, useSwitch, skip, row, jogEdge, Prod.mk.injEq] <;>
      solve_link_cases (x - 17 * (k : ℤ))

end GridCover.AxisPieces
