import Common
import PairRoster

/-! Every initial adjacency is one of four length patterns. The two labels
in each consecutive-layer pattern expose both parity coordinates. -/
namespace DiamondCount

open SpellingBPE Diamond

theorem spell_injective : Function.Injective spell := by
  intro a b eq
  simpa [spell] using congrArg List.length eq

theorem variant_lt {m j x y : Nat} (hx : x < m) (hy : y < m) : variant j x y < m := by
  unfold variant
  split <;> assumption

theorem variant_pair_injective {j x y a b : Nat}
    (first : variant j x y = variant j a b)
    (next : variant (j+1) x y = variant (j+1) a b) : x=a ∧ y=b := by
  by_cases even : j%2=0
  · have odd : (j+1)%2 ≠ 0 := by omega
    exact ⟨by simpa [variant, even] using first, by simpa [variant, odd] using next⟩
  · have odd : (j+1)%2 = 0 := by omega
    exact ⟨by simpa [variant, odd] using next, by simpa [variant, even] using first⟩

def stage (m s x y depth : Nat) : Word Nat := (wrap m x y s depth [hub m s]).map spell

theorem stage_zero (m s x y : Nat) : stage m s x y 0 = [spell (hub m s)] := rfl

theorem wrap_last (m x y start depth : Nat) (center : List Nat) :
    wrap m x y start (depth+1) center =
      U m (start+depth) (variant (start+depth) x y) ::
        wrap m x y start depth center ++ [V m (start+depth) (variant (start+depth) x y)] := by
  simp only [wrap, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stage_succ (m s x y d : Nat) :
    stage m s x y (d+1) =
      spell (U m (s+d) (variant (s+d) x y)) ::
        stage m s x y d ++ [spell (V m (s+d) (variant (s+d) x y))] := by
  simp only [stage, wrap_last, List.map_cons, List.map_append, List.map_nil]

theorem stage_nonempty (m s x y d : Nat) : stage m s x y d ≠ [] := by
  cases d with
  | zero => simp [stage_zero]
  | succ d => simp [stage_succ]

theorem stage_endpoints (m s x y d : Nat) :
    (stage m s x y (d+1)).head? = some (spell (U m (s+d) (variant (s+d) x y))) ∧
      (stage m s x y (d+1)).getLast? = some (spell (V m (s+d) (variant (s+d) x y))) := by
  constructor
  · simp [stage_succ]
  · rw [stage_succ, List.getLast?_append]
    rfl

theorem candidates_sandwich (left right : Token Nat) (middle : Word Nat) (hn : middle ≠ []) :
    candidates (left :: middle ++ [right]) =
      middle.head?.toList.map (fun x => (left,x)) ++ candidates middle ++
        middle.getLast?.toList.map (fun x => (x,right)) := by
  change candidates (left :: (middle ++ [right])) = _
  rw [CombIncidence.candidates_cons, CombIncidence.candidates_snoc, List.head?_append_of_ne_nil middle hn,
    List.append_assoc]

inductive EdgeCase where
  | seedL (s i : Nat)
  | seedR (s i : Nat)
  | layerL (inner i j : Nat)
  | layerR (inner i j : Nat)

def EdgeCase.valid (m : Nat) : EdgeCase → Prop
  | .seedL s i | .seedR s i => s<m ∧ i<m
  | .layerL a i j | .layerR a i j => a+1<m ∧ i<m ∧ j<m

def EdgeCase.pair (m : Nat) : EdgeCase → Pair Nat
  | .seedL s i => (spell (U m s i), spell (hub m s))
  | .seedR s i => (spell (hub m s), spell (V m s i))
  | .layerL a i j => (spell (U m (a+1) j), spell (U m a i))
  | .layerR a i j => (spell (V m a i), spell (V m (a+1) j))

def EdgeCase.fits (s x y : Nat) : EdgeCase → Prop
  | .seedL a i | .seedR a i => s=a ∧ variant a x y=i
  | .layerL a i j | .layerR a i j => s≤a ∧ variant a x y=i ∧ variant (a+1) x y=j

theorem candidate_stage_case {m s x y depth : Nat} (hs : s<m) (hx : x<m) (hy : y<m)
    (within : s+depth ≤ m) {q : Pair Nat} (occurs : q ∈ candidates (stage m s x y depth)) :
    ∃ edge : EdgeCase, edge.valid m ∧ q = edge.pair m ∧ edge.fits s x y := by
  induction depth with
  | zero => simp [stage_zero, candidates] at occurs
  | succ d ih =>
    rw [stage_succ, candidates_sandwich _ _ _ (stage_nonempty m s x y d)] at occurs
    rw [List.mem_append, List.mem_append] at occurs
    rcases occurs with (left | old) | right
    · cases d with
      | zero =>
        simp [stage_zero] at left
        exact ⟨.seedL s (variant s x y), ⟨hs, variant_lt hx hy⟩, left, rfl, rfl⟩
      | succ n =>
        have ep := (stage_endpoints m s x y n).1
        simp only [ep, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at left
        refine ⟨.layerL (s+n) (variant (s+n) x y) (variant (s+n+1) x y),
          ⟨by omega, variant_lt hx hy, variant_lt hx hy⟩, ?_, by omega, rfl, rfl⟩
        exact left
    · exact ih (by omega) old
    · cases d with
      | zero =>
        simp [stage_zero] at right
        exact ⟨.seedR s (variant s x y), ⟨hs, variant_lt hx hy⟩, right, rfl, rfl⟩
      | succ n =>
        have ep := (stage_endpoints m s x y n).2
        simp only [ep, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at right
        refine ⟨.layerR (s+n) (variant (s+n) x y) (variant (s+n+1) x y),
          ⟨by omega, variant_lt hx hy, variant_lt hx hy⟩, ?_, by omega, rfl, rfl⟩
        exact right

theorem candidate_row_case {m s x y : Nat} (hs : s<m) (hx : x<m) (hy : y<m)
    {q : Pair Nat} (occurs : q ∈ candidates (row m s x y)) :
    ∃ edge : EdgeCase, edge.valid m ∧ q = edge.pair m ∧ edge.fits s x y :=
  candidate_stage_case hs hx hy (by omega : s+(m-s) ≤ m) occurs

end DiamondCount
