import ForestPaths
import ForestLabels

/-! The rule at each chronological stage specifies the spelling of every
original leaf attached on a given side. Short temporal gaps have few labels. -/
namespace BPEForest
open MergeTree SpellingBPE
variable {α : Type}

def operand (rules : List (Pair α)) (side : Bool) (i : ℕ) : Token α :=
  let p := rules[i]?.getD ([],[])
  if side then p.2 else p.1

def orderedPair (side : Bool) (newer older : Token α) : Pair α :=
  if side then (older,newer) else (newer,older)

def labelAt (rules : List (Pair α)) (s : ℕ) (j : GapLabel rules.length s) : Pair α :=
  let side := decide (j.1.val = 1)
  let n := j.2.1.val
  orderedPair side (operand rules side n) (operand rules side (n-(j.2.2.val+1)))

def shortLabels [DecidableEq α] (rules : List (Pair α)) (s : ℕ) : Finset (Pair α) :=
  Finset.univ.image (labelAt rules s)

theorem shortLabels_card [DecidableEq α] (rules : List (Pair α)) (s : ℕ) :
    (shortLabels rules s).card ≤ 2*rules.length*s := labels_card_le ..

theorem short_pair_mem [DecidableEq α] (rules : List (Pair α)) (s : ℕ) (side : Bool)
    {n o : ℕ} (hn : n < rules.length) (ho : o < n) (gap : n-o ≤ s) :
    orderedPair side (operand rules side n) (operand rules side o) ∈ shortLabels rules s := by
  let j : Fin rules.length := ⟨n,hn⟩
  let d : Fin s := ⟨n-o-1,by omega⟩
  have back : n-(d.val+1)=o := by dsimp [d]; omega
  cases side
  · exact Finset.mem_image.mpr ⟨((0 : Fin 2),j,d),Finset.mem_univ _,by simp [labelAt,j,back]⟩
  · exact Finset.mem_image.mpr ⟨((1 : Fin 2),j,d),Finset.mem_univ _,by simp [labelAt,j,back]⟩

def ChainValid (rules : List (Pair α)) (b : ℕ) (xs : Chain α) : Prop :=
  xs.Pairwise (fun a c => c.2.1 < a.2.1) ∧
    ∀ a∈xs, a.2.1<b ∧ a.2.2=operand rules a.1 a.2.1

private def ExtractionValid (rules : List (Pair α)) (b : ℕ) (x : Extraction α) : Prop :=
  ChainValid rules b x.1 ∧ ∀ p∈x.2, ChainValid rules b p

private theorem valid_empty (rules : List (Pair α)) (b : ℕ) : ChainValid rules b [] :=
  ⟨.nil,by simp⟩

private theorem chain_mono {rules : List (Pair α)} {b k : ℕ} {xs : Chain α}
    (valid : ChainValid rules b xs) (le : b ≤ k) : ChainValid rules k xs :=
  ⟨valid.1,fun a h => ⟨(valid.2 a h).1.trans_le le,(valid.2 a h).2⟩⟩

private theorem valid_close {rules : List (Pair α)} {b : ℕ} {x : Extraction α}
    (ok : ExtractionValid rules b x) {p : Chain α} (hp : p∈close x) : ChainValid rules b p := by
  unfold close at hp
  split at hp
  · exact ok.2 _ hp
  · rcases List.mem_cons.mp hp with rfl | mem
    · exact ok.1
    · exact ok.2 _ mem

private theorem valid_extend {rules : List (Pair α)} {b n : ℕ} {x : Extraction α}
    (ok : ExtractionValid rules n x) (side : Bool) (token : Token α)
    (lt : n<b) (label : token=operand rules side n) :
    ExtractionValid rules b (extend (side,n,token) x) := by
  refine ⟨⟨List.pairwise_cons.mpr ⟨fun a h => (ok.1.2 a h).1,ok.1.1⟩,?_⟩,?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | mem
    · exact ⟨lt,label⟩
    · exact (chain_mono ok.1 lt.le).2 _ mem
  · exact fun p h => chain_mono (ok.2 p h) lt.le

private theorem extract_valid {rules : List (Pair α)} {b : ℕ} (t : MergeTree α)
    (v : t.Valid rules b) : ExtractionValid rules b (extract t) := by
  induction t generalizing b with
  | leaf => exact ⟨valid_empty ..,by simp [extract]⟩
  | node i l r il ir =>
    obtain ⟨lt,atStage,vl,vr⟩ := v
    cases l with
    | leaf a =>
      cases r with
      | leaf => exact ⟨valid_empty ..,by simp [extract]⟩
      | node j x y =>
        exact valid_extend (ir vr) false a lt (by simp [operand,atStage,spell])
    | node j x y =>
      cases r with
      | leaf a =>
        exact valid_extend (il vl) true a lt (by simp [operand,atStage,spell])
      | node k z w =>
        refine ⟨valid_empty ..,?_⟩
        intro p hp
        rcases List.mem_append.mp hp with left | right
        · exact chain_mono (valid_close (il vl) left) lt.le
        · exact chain_mono (valid_close (ir vr) right) lt.le

theorem extracted_valid {rules : List (Pair α)} {b : ℕ} {t : MergeTree α}
    (v : t.Valid rules b) {xs : Chain α} (mem : xs∈close (extract t)) :
    ChainValid rules b xs := valid_close (extract_valid t v) mem

def sameSide (side : Bool) (xs : Chain α) : Chain α := xs.filter (fun a => a.1 == side)

def shortAhead (s : ℕ) (side : Bool) (stage : ℕ) (xs : Chain α) : Bool :=
  match (sameSide side xs).head? with
  | none => false
  | some a => decide (stage-a.2.1 ≤ s)

def shortAt (s stage : ℕ) : MergeTree α → MergeTree α → Bool
  | .leaf _, r@(.node ..) => shortAhead s false stage (extract r).1
  | l@(.node ..), .leaf _ => shortAhead s true stage (extract l).1
  | _, _ => false

def shortEdges (s : ℕ) : Chain α → ℕ
  | [] => 0
  | [_] => 0
  | a::b::xs => (decide (a.2.1-b.2.1 ≤ s)).toNat + shortEdges s (b::xs)

def shortCount (s : ℕ) (xs : Chain α) : ℕ :=
  shortEdges s (sameSide false xs) + shortEdges s (sameSide true xs)

private theorem shortEdges_cons (s : ℕ) (a : Attachment α) (xs : Chain α) :
    shortEdges s (a::xs) =
      (match xs.head? with | none => false | some b => decide (a.2.1-b.2.1 ≤ s)).toNat +
        shortEdges s xs := by cases xs <;> rfl

theorem shortCount_cons (s : ℕ) (a : Attachment α) (xs : Chain α) :
    shortCount s (a::xs) = (shortAhead s a.1 a.2.1 xs).toNat + shortCount s xs := by
  rcases a with ⟨side,i,t⟩
  cases side <;> simp [shortCount,sameSide,shortAhead,shortEdges_cons,Nat.add_assoc,Nat.add_left_comm]

private theorem side_degree (s : ℕ) (xs : Chain α)
    (desc : xs.Pairwise (fun a c => c.2.1 < a.2.1)) :
    s*xs.length ≤ s*shortEdges s xs+s+(xs.head?.map (fun a => a.2.1)).getD 0 := by
  induction xs using List.twoStepInduction with
  | nil => simp [shortEdges]
  | singleton a => simp [shortEdges]
  | cons_cons a b xs _ ih =>
    obtain ⟨smaller,tail⟩ := List.pairwise_cons.mp desc
    have order := smaller b (List.mem_cons_self ..)
    have prev := ih b tail
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at prev ⊢
    rw [List.length_cons, Nat.mul_succ,shortEdges,Nat.mul_add]
    by_cases small : a.2.1-b.2.1 ≤ s
    · simp only [decide_eq_true small, Bool.toNat_true, Nat.mul_one]
      omega
    · simp only [decide_eq_false small, Bool.toNat_false, Nat.mul_zero]
      omega

private theorem side_cost {rules : List (Pair α)} {k : ℕ} {xs : Chain α} (s : ℕ)
    (v : ChainValid rules k xs) (side : Bool) :
    s*(sameSide side xs).length ≤ s*shortEdges s (sameSide side xs)+s+k := by
  have desc : (sameSide side xs).Pairwise (fun a c => c.2.1 < a.2.1) :=
    v.1.filter _
  have cost := side_degree s _ desc
  cases eq : sameSide side xs with
  | nil => simp
  | cons a tail =>
    have mem : a∈sameSide side xs := by rw [eq]; exact List.mem_cons_self ..
    have inOld := List.mem_of_mem_filter mem
    have below := (v.2 a inOld).1
    simp only [eq,List.head?_cons,Option.map_some,Option.getD_some] at cost ⊢
    omega

private theorem side_lengths (xs : Chain α) :
    (sameSide false xs).length + (sameSide true xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨side,i,t⟩
    cases side <;> simp [sameSide] at ih ⊢ <;> omega

theorem chain_cost {rules : List (Pair α)} {k : ℕ} {xs : Chain α} (s : ℕ)
    (v : ChainValid rules k xs) : s*xs.length ≤ s*shortCount s xs+2*s+2*k := by
  have left := side_cost s v false
  have right := side_cost s v true
  rw [←side_lengths xs,Nat.mul_add,shortCount,Nat.mul_add]
  omega

#print axioms extracted_valid
#print axioms chain_cost
end BPEForest
