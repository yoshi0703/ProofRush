import DistinctRows

namespace DiamondCount

open Diamond SpellingBPE

theorem row_token_domain {m s x y : Nat} (hs : s<m) (hx : x<m) (hy : y<m)
    {tile : Token Nat} (present : tile ∈ row m s x y) : tile ≠ [] ∧ ∀ a ∈ tile, a = 0 := by
  have nonempty {len : Nat} (zero : 0<len) : spell len ≠ [] ∧ ∀ a ∈ spell len, a = 0 := by
    constructor
    · intro empty
      have lengths := congrArg List.length empty
      simp [spell] at lengths
      omega
    · exact fun a ha => (List.mem_replicate.mp ha).2
  rcases stage_tokens m s x y (m-s) present with center | ⟨j,_,jl,left | right⟩
  · rw [center]
    exact nonempty (by simp [hub, B])
  · rw [left]
    exact nonempty (U_pos ..)
  · rw [right]
    have jUpper : j<m := by omega
    exact nonempty (V_pos jUpper (variant_lt hx hy))

theorem coreTable_token_domain {m : Nat} {r : Nat × Word Nat} {tile : Token Nat}
    (rowMember : r ∈ coreTable m) (present : tile ∈ r.2) : tile ≠ [] ∧ ∀ a ∈ tile, a=0 := by
  simp only [coreTable, List.mem_flatMap, List.mem_map, List.mem_range] at rowMember
  obtain ⟨s,hs,x,hx,y,hy,rfl⟩ := rowMember
  exact row_token_domain hs hx hy present

theorem stage_contains_center (m s x y depth used : Nat) (bound : used≤depth) :
    Factor (stage m s x y used) (stage m s x y depth) := by
  induction depth with
  | zero =>
    have eq : used=0 := by omega
    subst used
    exact ⟨[],[],by simp⟩
  | succ d ih =>
    by_cases early : used≤d
    · obtain ⟨left,right,eq⟩ := ih early
      refine ⟨spell (U m (s+d) (variant (s+d) x y))::left,
        right ++ [spell (V m (s+d) (variant (s+d) x y))], ?_⟩
      rw [stage_succ, eq]
      simp [List.append_assoc]
    · have eq : used=d+1 := by omega
      subst used
      exact ⟨[],[],by simp⟩

/-- These distinct factors occur in the seed-s and seed-(s+1) rows
respectively, and have identical literal concatenations. -/
theorem seed_collision {m s x y : Nat} (hs : s+1<m) (hx : x<m) (hy : y<m) :
    ∃ u v : Word Nat, Factor u (row m s x y) ∧ Factor v (row m (s+1) x y) ∧
      u ≠ v ∧ u.flatten = v.flatten := by
  let u := stage m s x y 1
  let v := stage m (s+1) x y 0
  refine ⟨u,v,stage_contains_center m s x y (m-s) 1 (by omega),
    stage_contains_center m (s+1) x y (m-(s+1)) 0 (by omega), ?_, ?_⟩
  · intro same
    have len := congrArg List.length same
    simp [u, v, stage_succ,stage_zero] at len
  · have hsmall : s<m := by omega
    have part := pieces_sum hsmall (variant_lt (j:=s) hx hy)
    simp only [u,v,stage_succ,stage_zero,Nat.add_zero,List.cons_append,List.nil_append,
      List.flatten_cons,List.flatten_nil,List.append_nil,spelling_join]
    congr 1
    calc
      _ = hub m s + (U m s (variant s x y) + V m s (variant s x y)) := by omega
      _ = hub m s + B m := by rw [part]
      _ = hub m (s+1) := by simp [hub, Nat.add_mul]

#print axioms coreTable_token_domain
#print axioms seed_collision

end DiamondCount
