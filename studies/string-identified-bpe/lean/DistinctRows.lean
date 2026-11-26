import EdgeCodes

namespace DiamondCount

open Diamond SpellingBPE

theorem stage_tokens (m s x y d : Nat) {tile : Token Nat}
    (present : tile ∈ stage m s x y d) :
    tile = spell (hub m s) ∨ ∃ j, s ≤ j ∧ j < s+d ∧
      (tile = spell (U m j (variant j x y)) ∨ tile = spell (V m j (variant j x y))) := by
  induction d with
  | zero => exact Or.inl (by simpa [stage_zero] using present)
  | succ n ih =>
    rw [stage_succ] at present
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with (newLeft | old) | newRight
    · exact Or.inr ⟨s+n,by omega,by omega,Or.inl newLeft⟩
    · rcases ih old with hubToken | ⟨j,low,high,eq⟩
      · exact Or.inl hubToken
      · exact Or.inr ⟨j,low,by omega,eq⟩
    · exact Or.inr ⟨s+n,by omega,by omega,Or.inr newRight⟩

private theorem freshU_absent {m s x y d : Nat} (hx : x<m) (hy : y<m) (upper : s+d<m) :
    spell (U m (s+d) (variant (s+d) x y)) ∉ stage m s x y d := by
  intro present
  have var := variant_lt (j:=s+d) hx hy
  rcases stage_tokens m s x y d present with center | ⟨j,_,lt,left | right⟩
  · have eq := congrArg (fun t : Token Nat => band m t.length) center
    simp [spell, band_U upper var, band_hub] at eq
  · have jUpper : j<m := lt.trans upper
    have jVar := variant_lt (j:=j) hx hy
    have index := (U_injective var jVar (spell_injective left)).1
    omega
  · have jUpper : j<m := lt.trans upper
    have jVar := variant_lt (j:=j) hx hy
    have eq := congrArg (fun t : Token Nat => band m t.length) right
    simp [spell, band_U upper var, band_V jUpper jVar] at eq

private theorem freshV_absent {m s x y d : Nat} (hx : x<m) (hy : y<m) (upper : s+d<m) :
    spell (V m (s+d) (variant (s+d) x y)) ∉ stage m s x y d := by
  intro present
  have var := variant_lt (j:=s+d) hx hy
  rcases stage_tokens m s x y d present with center | ⟨j,_,lt,left | right⟩
  · have eq := congrArg (fun t : Token Nat => band m t.length) center
    simp [spell, band_V upper var, band_hub] at eq
  · have jUpper : j<m := lt.trans upper
    have jVar := variant_lt (j:=j) hx hy
    have eq := congrArg (fun t : Token Nat => band m t.length) left
    simp [spell, band_V upper var, band_U jUpper jVar] at eq
  · have jUpper : j<m := lt.trans upper
    have jVar := variant_lt (j:=j) hx hy
    have index := (V_injective upper var jUpper jVar (spell_injective right)).1
    omega

theorem stage_nodup {m s x y d : Nat} (hx : x<m) (hy : y<m) (within : s+d≤m) :
    (stage m s x y d).Nodup := by
  induction d with
  | zero => simp [stage_zero]
  | succ d ih =>
    rw [stage_succ, List.nodup_append, List.nodup_cons]
    have upper : s+d<m := by omega
    exact ⟨⟨freshU_absent hx hy upper, ih (by omega)⟩, by simp, by
      intro a ha b hb same
      have var := variant_lt (j:=s+d) hx hy
      have bEq : b = spell (V m (s+d) (variant (s+d) x y)) := List.mem_singleton.mp hb
      rw [same.trans bEq] at ha
      rcases List.mem_cons.mp ha with eq | old
      · have clash := congrArg (fun t : Token Nat => band m t.length) eq
        simp [spell, band_U upper var, band_V upper var] at clash
      · exact freshV_absent hx hy upper old⟩

theorem candidate_first_mem {α : Type} {w : Word α} {q : Pair α}
    (member : q ∈ candidates w) : q.1 ∈ w := by
  induction w using List.twoStepInduction with
  | nil => simp [candidates] at member
  | singleton x => simp [candidates] at member
  | cons_cons x y tail _ ih =>
    simp only [candidates, List.mem_cons] at member
    rcases member with rfl | rest
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih y rest)

theorem candidates_nodup_of_tokens_nodup {α : Type} {w : Word α} (nodup : w.Nodup) :
    (candidates w).Nodup := by
  induction w using List.twoStepInduction with
  | nil => simp [candidates]
  | singleton x => simp [candidates]
  | cons_cons x y tail _ ih =>
    obtain ⟨absent,rest⟩ := List.nodup_cons.mp nodup
    apply List.nodup_cons.mpr
    exact ⟨fun h => absent (candidate_first_mem h), ih y rest⟩

theorem row_gain_le_one {m s x y : Nat} (hs : s<m) (hx : x<m) (hy : y<m) (q : Pair Nat) :
    gain q (row m s x y) ≤ 1 :=
  CombIncidence.gain_le_one_of_nodup q _ <| candidates_nodup_of_tokens_nodup
    (stage_nodup hx hy (by omega : s+(m-s)≤m))

end DiamondCount
