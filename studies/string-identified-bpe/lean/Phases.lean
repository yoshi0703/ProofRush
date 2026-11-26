import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases

/-! Reusable finite phase facts for the alternating / RRLL comb. These facts
are about the six phase schedules only. They do not assert the full BPE
construction, its encoding, or its approximation ratio. -/
namespace CombPhases

def side (phase : Fin 6) (j : Nat) : Bool :=
  if phase.val < 2 then (j + phase.val) % 2 == 0
  else (j + phase.val - 2) % 4 < 2

def count (j gap : Nat) (target : Bool) : Nat :=
  ((List.finRange 6).filter fun p =>
    side p j == target && side p (j+gap) == target &&
    (List.range (gap-1)).all (fun d => side p (j+d+1) != target)).length

def firstCount (j gap : Nat) (target : Bool) : Nat :=
  ((List.finRange 6).filter fun p =>
    side p (j+gap) == target &&
    (List.range (gap-1)).all (fun d => side p (j+d+1) != target)).length

theorem side_period_four (phase : Fin 6) (j : Nat) :
    side phase (j+4) = side phase j := by
  unfold side
  split
  · have h : (j+4+phase.val) % 2 = (j+phase.val) % 2 := by omega
    rw [h]
  · have h : j+4+phase.val-2 = (j+phase.val-2)+4 := by omega
    rw [h]
    simp

theorem side_mod_four (phase : Fin 6) (j : Nat) :
    side phase j = side phase (j % 4) := by
  unfold side
  split
  · have h : (j+phase.val) % 2 = (j % 4+phase.val) % 2 := by omega
    rw [h]
  · have h : (j+phase.val-2) % 4 = (j % 4+phase.val-2) % 4 := by omega
    rw [h]

theorem side_shift_mod (phase : Fin 6) (j d : Nat) :
    side phase (j+d) = side phase (j%4+d) := by
  rw [side_mod_four phase (j+d), side_mod_four phase (j%4+d)]
  simp only [Nat.add_mod, Nat.mod_mod]

theorem count_mod_four (j gap : Nat) (target : Bool) :
    count j gap target = count (j%4) gap target := by
  unfold count
  congr 2
  funext p
  have h0 : side p j = side p (j%4) := side_mod_four p j
  have hgap := side_shift_mod p j gap
  rw [h0,hgap]
  congr 2
  funext d
  simpa [Nat.add_assoc] using side_shift_mod p j (d+1)

/-- Over all four start residues and gaps 1..3, an already inserted level can
be followed by a given side at most once across all six phases. -/
theorem finite_gap_counts : ∀ (j : Fin 4) (gap : Fin 3) (target : Bool),
    count j.val (gap.val+1) target ≤ 1 := by decide +kernel

/-- For a seed's two exposed endpoints, at most three phases first hit the
specified side at a given gap. -/
theorem finite_seed_counts : ∀ (j : Fin 4) (gap : Fin 3) (target : Bool),
    firstCount j.val (gap.val+1) target ≤ 3 := by decide +kernel

/-- In any three consecutive insertions, both sides occur in every phase. -/
theorem finite_three_window : ∀ (j : Fin 4) (p : Fin 6) (target : Bool),
    side p (j.val+1) = target ∨ side p (j.val+2) = target ∨
      side p (j.val+3) = target := by decide +kernel

theorem firstCount_mod_four (j gap : Nat) (target : Bool) :
    firstCount j gap target = firstCount (j%4) gap target := by
  unfold firstCount
  congr 2
  funext p
  rw [side_shift_mod p j gap]
  congr 2
  funext d
  simpa [Nat.add_assoc] using side_shift_mod p j (d+1)

theorem bounded_small_gap (j gap : Nat) (target : Bool) (hp : 1 ≤ gap) (hb : gap ≤ 3) :
    count j gap target ≤ 1 ∧ firstCount j gap target ≤ 3 := by
  rw [count_mod_four, firstCount_mod_four]
  let jj : Fin 4 := ⟨j%4, Nat.mod_lt _ (by decide)⟩
  let gg : Fin 3 := ⟨gap-1, by omega⟩
  have h1 := finite_gap_counts jj gg target
  have h2 := finite_seed_counts jj gg target
  have hgap : gg.val+1 = gap := by dsimp [gg]; omega
  rw [hgap] at h1 h2
  exact ⟨h1,h2⟩

theorem three_window (j : Nat) (p : Fin 6) (target : Bool) :
    side p (j+1) = target ∨ side p (j+2) = target ∨ side p (j+3) = target := by
  have h := finite_three_window ⟨j%4, Nat.mod_lt _ (by decide)⟩ p target
  simpa only [← side_shift_mod p j 1, ← side_shift_mod p j 2,
    ← side_shift_mod p j 3] using h

theorem large_gap_no_phase (j gap : Nat) (p : Fin 6) (target : Bool) (hg : 4 ≤ gap) :
    (List.range (gap-1)).all (fun d => side p (j+d+1) != target) = false := by
  have h := three_window j p target
  rcases h with h | h | h
  · apply List.all_eq_false.mpr
    exact ⟨0, List.mem_range.mpr (by omega), by simpa using h⟩
  · apply List.all_eq_false.mpr
    exact ⟨1, List.mem_range.mpr (by omega), by simpa [Nat.add_assoc] using h⟩
  · apply List.all_eq_false.mpr
    exact ⟨2, List.mem_range.mpr (by omega), by simpa [Nat.add_assoc] using h⟩

theorem bounded_every_gap (j gap : Nat) (target : Bool) (hp : 1 ≤ gap) :
    count j gap target ≤ 1 ∧ firstCount j gap target ≤ 3 := by
  by_cases h : gap ≤ 3
  · exact bounded_small_gap j gap target hp h
  · have hg : 4 ≤ gap := by omega
    have hz : ∀ p : Fin 6,
        (List.range (gap-1)).all (fun d => side p (j+d+1) != target) = false :=
      fun p => large_gap_no_phase j gap p target hg
    simp [count, firstCount, hz]

end CombPhases
