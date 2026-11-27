import GridPeriodic

namespace GridCover

/-- All tests at one anchor use only its radius-two seed roles and
the links between centers in that same box. -/
theorem rawCheck_of_local_agreement {P Q : Roles} {L K : Links} {p : Center}
    (roleEq : ∀ q ∈ box 2 p, P q = Q q)
    (linkEq : ∀ q ∈ box 2 p, ∀ r ∈ box 2 p, L q r = K q r)
    (checked : rawCheck Q K p) : rawCheck P L p := by
  have pIn : p ∈ box 2 p := by
    apply mem_box.mpr
    unfold nearby
    omega
  have inBox {e : GridEdge} (he : e ∈ perimeter p) {q : Center}
      (hq : q ∈ incidentCenters e) : q ∈ box 2 p :=
    mem_box.mpr (sharedEdge_nearby ((mem_incidentCenters e p).mpr he) hq)
  have eqCover {e : GridEdge} (he : e ∈ perimeter p) :
      seededCoverers P e = seededCoverers Q e := by
    ext q
    simp only [seededCoverers, Finset.mem_filter]
    refine and_congr_right fun hq => ?_
    rw [roleEq q (inBox he hq)]
  have elig : geometricEligible P p ↔ geometricEligible Q p := by
    exact forall₂_congr fun e he => by unfold present; rw [eqCover he]
  refine ⟨elig.trans (checked.1.trans ?_), ?_, ?_⟩
  · rw [roleEq p pIn]
  · intro hguard
    obtain ⟨e, he, unique⟩ := checked.2.1 ((roleEq p pIn).symm.trans hguard)
    exact ⟨e, he, (eqCover he).trans unique⟩
  · intro hoption
    obtain ⟨coverage, witness⟩ := checked.2.2 ((roleEq p pIn).symm.trans hoption)
    refine ⟨?_, ?_⟩
    · intro e he
      rw [eqCover he]
      rcases coverage e he with ⟨q, hq, hg⟩ | ⟨q, hq, r, hr, hqo, hro, hlink⟩
      · have hbox := inBox he (Finset.mem_filter.mp hq).1
        exact Or.inl ⟨q, hq, (roleEq q hbox).trans hg⟩
      · have hbox := inBox he (Finset.mem_filter.mp hq).1
        have hbox' := inBox he (Finset.mem_filter.mp hr).1
        exact Or.inr ⟨q, hq, r, hr, (roleEq q hbox).trans hqo,
          (roleEq r hbox').trans hro, (linkEq q hbox r hbox').trans hlink⟩
    · intro q hq hlink
      obtain ⟨e, he, unique⟩ := witness q hq ((linkEq p pIn q hq).symm.trans hlink)
      exact ⟨e, he, (eqCover he).trans unique⟩

def generalWireRoles (guarded : ℤ → Bool) (p : Center) : Role :=
  if p.2 = 0 then .optional
  else if (p.2 = -1 ∨ p.2 = 1) ∧ guarded p.1 = true then .guard else .empty

def tripleOK (a b c : Bool) : Bool := (a || b || c) && (!(a == c) || (a == b))

/-- Forbid 000, 010, 101, and 11111. This is a local condition
satisfied by every two-zero gap and guard runs of length two through four. -/
def fiveOK (a b c d e : Bool) : Bool :=
  tripleOK a b c && tripleOK b c d && tripleOK c d e && !(a && b && c && d && e)

def template (a b c d e : Bool) (x : ℤ) : Bool :=
  if x = -2 then a else if x = -1 then b else if x = 0 then c
  else if x = 1 then d else if x = 2 then e else false

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem finite_guard_windows (a b c d e : Bool) :
    fiveOK a b c d e = true →
    ∀ y ∈ Finset.Icc (-3 : ℤ) 3,
      rawCheck (generalWireRoles (template a b c d e)) wireLinks (0, y) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem generalWire_raw (guarded : ℤ → Bool)
    (good : ∀ x : ℤ, fiveOK (guarded (x - 2)) (guarded (x - 1)) (guarded x)
      (guarded (x + 1)) (guarded (x + 2)) = true)
    (p : Center) : rawCheck (generalWireRoles guarded) wireLinks p := by
  by_cases hy : -3 ≤ p.2 ∧ p.2 ≤ 3
  · let g := horizontalShift (-p.1)
    let moved := fun x : ℤ => guarded (p.1 + x)
    have movedPoint : g.point p = (0,p.2) := by
      change (p.1 + (-p.1), p.2) = (0,p.2)
      simp
    have atOrigin : rawCheck (generalWireRoles moved) wireLinks (0,p.2) := by
      apply rawCheck_of_local_agreement _ (fun _ _ _ _ => rfl)
        (finite_guard_windows _ _ _ _ _ (good p.1) p.2 (Finset.mem_Icc.mpr hy))
      rintro ⟨x,y⟩ hx
      have hx' := mem_box.mp hx
      unfold nearby at hx'
      have he : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by simp at hx'; omega
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
        simp [generalWireRoles, moved, template, sub_eq_add_neg]
    rw [← movedPoint] at atOrigin
    refine g.raw_pullback ?_ ?_ atOrigin
    · rintro ⟨x,y⟩
      change generalWireRoles guarded (x,y) = generalWireRoles moved (x + (-p.1),y)
      have hx : p.1 + (x + -p.1) = x := by omega
      simp [generalWireRoles, moved, hx]
    · rintro ⟨x,y⟩ ⟨u,v⟩
      change wireLinks (x,y) (u,v) = wireLinks (x + (-p.1),y) (u + (-p.1),v)
      have hApart : unitApart (x + (-p.1)) (u + (-p.1)) ↔ unitApart x u := by
        unfold unitApart
        omega
      simp [wireLinks, hApart]
  · apply raw_empty
    intro q hq
    unfold generalWireRoles nearby at *
    have hn : q.2 ≠ 0 ∧ q.2 ≠ -1 ∧ q.2 ≠ 1 := by omega
    simp [hn]

theorem generalWire_geometry (guarded : ℤ → Bool)
    (good : ∀ x : ℤ, fiveOK (guarded (x - 2)) (guarded (x - 1)) (guarded x)
      (guarded (x + 1)) (guarded (x + 2)) = true)
    (p : Center) : geometricCheck (generalWireRoles guarded) wireLinks p :=
  geometricCheck_of_raw (generalWire_raw guarded good p) fun q _ =>
    (generalWire_raw guarded good q).1

end GridCover
