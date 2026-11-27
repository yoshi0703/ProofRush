import GridPathEmbedding
import GridPlacementGeometry
import Mathlib.Data.List.Basic

namespace GridCover.PathEmbedding.Stride17

open GridCover.Placement

def skip (brief : Bool) : ℕ := if brief then 1 else 0

def useSwitch (leftTee rightTee : Bool) : Bool := leftTee == rightTee

def axial (start count : ℕ) : List Center :=
  (List.range' start count).map (fun i : ℕ => ((i : ℤ), 0))

/-- The transversal sign records the orientation of the stencil basis. -/
def jog (reverse : Bool) : List Center :=
  if reverse then [(17, -1), (17, 1)] else [(17, 1), (17, -1)]

/-- Ordered internal path in the coordinate frame of its straight source
segment. Source positions have first been doubled, so its coarse length is
`2*n` and its physical length before local changes is `34*n`. -/
def internal (n : ℕ) (leftTee rightTee reverse : Bool) : List Center :=
  let first := 1 + skip leftTee
  let past := 34 * n - skip rightTee
  if useSwitch leftTee rightTee then
    axial first (16 - first) ++ jog reverse ++ axial 19 (past - 19)
  else
    axial first (past - first)

theorem axial_mem {first count : ℕ} {p : Center} :
    p ∈ axial first count ↔
      ∃ i : ℕ, first ≤ i ∧ i < first + count ∧ p = ((i : ℤ), 0) := by
  simp only [axial, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨hl, hh⟩, rfl⟩
    exact ⟨i, hl, hh, rfl⟩
  · rintro ⟨i, hl, hh, rfl⟩
    exact ⟨i, ⟨hl, hh⟩, rfl⟩

theorem axial_nodup (first count : ℕ) : (axial first count).Nodup := by
  unfold axial
  apply (List.nodup_range').map
  intro i j hij
  have h := congrArg Prod.fst hij
  change (i : ℤ) = (j : ℤ) at h
  exact_mod_cast h

@[simp] theorem axial_length (first count : ℕ) : (axial first count).length = count := by
  simp [axial]

@[simp] theorem jog_length (reverse : Bool) : (jog reverse).length = 2 := by
  cases reverse <;> decide

theorem jog_nodup (reverse : Bool) : (jog reverse).Nodup := by
  cases reverse <;> decide

theorem jog_mem {reverse : Bool} {p : Center} :
    p ∈ jog reverse ↔ p = (17,1) ∨ p = (17,-1) := by
  cases reverse <;> simp [jog, or_comm]

theorem skip_le (b : Bool) : skip b ≤ 1 := by cases b <;> decide

theorem internal_mem_iff {n : ℕ} (positive : 1 ≤ n) (leftTee rightTee reverse : Bool)
    (p : Center) :
    p ∈ internal n leftTee rightTee reverse ↔
      (∃ i : ℕ, 1 + skip leftTee ≤ i ∧ i < 34 * n - skip rightTee ∧
        (useSwitch leftTee rightTee = false ∨ i < 16 ∨ 19 ≤ i) ∧
        p = ((i : ℤ), 0)) ∨
      (useSwitch leftTee rightTee = true ∧ (p = (17,1) ∨ p = (17,-1))) := by
  have sl := skip_le leftTee
  have sr := skip_le rightTee
  cases h : useSwitch leftTee rightTee
  · simp only [internal, h, Bool.false_eq_true, ite_false, axial_mem, false_and, or_false,
      true_or, true_and]
    constructor <;> rintro ⟨i, hi, hh, hp⟩ <;> exact ⟨i, hi, by omega, hp⟩
  · simp only [internal, h, ite_true, List.mem_append, axial_mem, jog_mem,
      Bool.true_eq_false, false_or, true_and]
    constructor
    · rintro ((⟨i, hl, hh, hp⟩ | hj) | ⟨i, hl, hh, hp⟩)
      · exact Or.inl ⟨i, hl, by omega, Or.inl (by omega), hp⟩
      · exact Or.inr hj
      · exact Or.inl ⟨i, by omega, by omega, Or.inr hl, hp⟩
    · rintro (⟨i, hl, hh, hlt | hge, hp⟩ | hj)
      · exact Or.inl (Or.inl ⟨i, hl, by omega, hp⟩)
      · exact Or.inr ⟨i, hge, by omega, hp⟩
      · exact Or.inl (Or.inr hj)

theorem axial_jog_disjoint (first count : ℕ) (reverse : Bool) :
    List.Disjoint (axial first count) (jog reverse) := by
  intro p ha hj
  obtain ⟨i, _, _, rfl⟩ := axial_mem.mp ha
  simp [jog_mem] at hj

theorem internal_nodup (n : ℕ) (leftTee rightTee reverse : Bool) :
    (internal n leftTee rightTee reverse).Nodup := by
  cases h : useSwitch leftTee rightTee
  · simpa [internal, h] using axial_nodup (1 + skip leftTee)
      (34 * n - skip rightTee - (1 + skip leftTee))
  · simp only [internal, h, ite_true]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨axial_nodup _ _, jog_nodup _, ?_⟩, axial_nodup _ _, ?_⟩
    · intro p hp q hq h
      subst q
      exact axial_jog_disjoint _ _ _ hp hq
    intro p hl q hr h
    subst q
    rcases List.mem_append.mp hl with ha | hj
    · obtain ⟨i, hi, hh, rfl⟩ := axial_mem.mp ha
      obtain ⟨j, hj, _, he⟩ := axial_mem.mp hr
      have hi' : (i : ℤ) = j := congrArg Prod.fst he
      omega
    · exact axial_jog_disjoint _ _ _ hr hj

theorem internal_length (n : ℕ) (positive : 1 ≤ n) (leftTee rightTee reverse : Bool) :
    (internal n leftTee rightTee reverse).length =
      34 * n - 1 - skip leftTee - skip rightTee - skip (useSwitch leftTee rightTee) := by
  cases leftTee <;> cases rightTee <;>
    simp [internal, useSwitch, skip] <;> omega

theorem internal_length_even (n : ℕ) (positive : 1 ≤ n) (leftTee rightTee reverse : Bool) :
    (internal n leftTee rightTee reverse).length =
      2 * (17*n - 1 - skip (leftTee && rightTee)) := by
  rw [internal_length n positive]
  cases leftTee <;> cases rightTee <;> simp [useSwitch, skip] <;> omega

def world (d : Direction) (start : Center) : Center ≃ Center :=
  (d.localFrame start).point.symm

@[simp] theorem world_axis (d : Direction) (start : Center) (index : ℤ) :
    world d start (index,0) = d.atSite start index := by
  apply ((d.localFrame start).point).injective
  simp [world]

def placedInternal (d : Direction) (start : Center) (n : ℕ)
    (leftTee rightTee reverse : Bool) : List Center :=
  (internal n leftTee rightTee reverse).map (world d start)

def fullPath (d : Direction) (start : Center) (n : ℕ)
    (leftTee rightTee reverse : Bool) : List Center :=
  start :: placedInternal d start n leftTee rightTee reverse ++ [d.atSite start (34*n : ℤ)]

theorem placedInternal_nodup (d : Direction) (start : Center) (n : ℕ)
    (leftTee rightTee reverse : Bool) :
    (placedInternal d start n leftTee rightTee reverse).Nodup :=
  (internal_nodup n leftTee rightTee reverse).map (world d start).injective

theorem placedInternal_even (d : Direction) (start : Center) (n : ℕ) (positive : 1 ≤ n)
    (leftTee rightTee reverse : Bool) :
    (placedInternal d start n leftTee rightTee reverse).length =
      2 * (17*n - 1 - skip (leftTee && rightTee)) := by
  simpa [placedInternal] using internal_length_even n positive leftTee rightTee reverse

@[simp] theorem start_point (d : Direction) (start : Center) :
    d.atSite start 0 = start := by cases d <;> simp [Direction.atSite]

theorem fullPath_ends (d : Direction) (start : Center) (n : ℕ)
    (leftTee rightTee reverse : Bool) :
    (fullPath d start n leftTee rightTee reverse).head? = some start ∧
    (fullPath d start n leftTee rightTee reverse).getLast? = some (d.atSite start (34*n : ℤ)) := by
  simp [fullPath, List.getLast?_cons]

theorem fullPath_nodup (d : Direction) (start : Center) (n : ℕ) (positive : 1 ≤ n)
    (leftTee rightTee reverse : Bool) :
    (fullPath d start n leftTee rightTee reverse).Nodup := by
  have first : ((0 : ℤ), (0 : ℤ)) ∉ internal n leftTee rightTee reverse := by
    intro h
    rcases (internal_mem_iff positive leftTee rightTee reverse _).mp h with
      ⟨i, hl, _, _, hp⟩ | ⟨_, hp | hp⟩
    · have he := congrArg Prod.fst hp
      simp at he
      omega
    · simp at hp
    · simp at hp
  have last : ((34 : ℤ)*n, (0 : ℤ)) ∉ internal n leftTee rightTee reverse := by
    intro h
    rcases (internal_mem_iff positive leftTee rightTee reverse _).mp h with
      ⟨i, _, hh, _, hp⟩ | ⟨_, hp | hp⟩
    · have he := congrArg Prod.fst hp
      simp at he
      omega
    · simp at hp
    · simp at hp
  have hl : (d.atSite start (34*n : ℤ)) ≠ start := by
    intro h
    have he := congrArg (fun p => d.longitudinal (sub p start)) h
    rw [Direction.longitudinal_atSite] at he
    have h0 : d.longitudinal (sub start start) = 0 := by
      cases d <;> simp [sub, Direction.longitudinal]
    rw [h0] at he
    omega
  have at_first : start ∉ placedInternal d start n leftTee rightTee reverse := by
    intro h
    obtain ⟨p,hp,heq⟩ := List.mem_map.mp h
    have he : world d start p = world d start (0,0) := by simpa using heq
    exact first ((world d start).injective he ▸ hp)
  have at_last : d.atSite start (34*n : ℤ) ∉ placedInternal d start n leftTee rightTee reverse := by
    intro h
    obtain ⟨p,hp,heq⟩ := List.mem_map.mp h
    have he : world d start p = world d start ((34 : ℤ)*n,0) := by simpa using heq
    exact last ((world d start).injective he ▸ hp)
  simp only [fullPath, List.cons_append, List.nodup_cons, List.nodup_append]
  refine ⟨?_, placedInternal_nodup _ _ _ _ _ _, by simp, ?_⟩
  · simp [at_first, Ne.symm hl]
  · intro p h₁ q h₂ he
    subst q
    have eq := List.mem_singleton.mp h₂
    exact at_last (eq ▸ h₁)

theorem fullPath_links_odd (d : Direction) (start : Center) (n : ℕ) (positive : 1 ≤ n)
    (leftTee rightTee reverse : Bool) :
    (fullPath d start n leftTee rightTee reverse).length - 1 =
      2 * (17*n - 1 - skip (leftTee && rightTee)) + 1 := by
  simp [fullPath, placedInternal_even d start n positive]

end GridCover.PathEmbedding.Stride17

#print axioms GridCover.PathEmbedding.Stride17.fullPath_nodup
#print axioms GridCover.PathEmbedding.Stride17.fullPath_links_odd
