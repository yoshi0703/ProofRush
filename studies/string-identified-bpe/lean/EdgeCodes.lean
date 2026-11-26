import EdgeCases

namespace DiamondCount

open Diamond SpellingBPE

theorem U_small {m j i : Nat} (hj : j<m) (hi : i<m) : U m j i ≤ m*m := by
  have next : (j+1)*m ≤ m*m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hj)
  simp only [U, Nat.succ_mul] at *
  omega

theorem U_injective {m j i k l : Nat} (hi : i<m) (hl : l<m)
    (same : U m j i = U m k l) : j=k ∧ i=l := by
  have monotone {a b c d : Nat} (ab : a<b) (cm : c<m) :
      U m a c < U m b d := by
    have mul : (a+1)*m ≤ b*m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt ab)
    simp only [U, Nat.succ_mul] at *
    omega
  have eqLayer : j=k := by
    by_contra! diff
    rcases lt_or_gt_of_ne diff with earlier | later
    · exact (monotone (d:=l) earlier hi).ne same
    · exact (monotone (d:=i) later hl).ne same.symm
  subst k
  exact ⟨rfl, by simp only [U] at same; omega⟩

theorem V_injective {m j i k l : Nat} (hj : j<m) (hi : i<m) (hk : k<m) (hl : l<m)
    (same : V m j i = V m k l) : j=k ∧ i=l := by
  have a := U_lt_B hj hi
  have b := U_lt_B hk hl
  unfold V at same
  exact U_injective hi hl (by omega)

theorem V_big {m j i : Nat} (hj : j<m) (hi : i<m) : m*m < V m j i := by
  have small := U_small hj hi
  unfold V B
  rw [Nat.mul_assoc]
  omega

theorem hub_big (m j : Nat) : B m ≤ hub m j := by
  simpa only [hub, Nat.one_mul] using (Nat.mul_le_mul_right (B m) (Nat.succ_pos j))

/-- The disjoint bands distinguish the three initial roles of any token. -/
def band (m len : Nat) : Nat :=
  if len < B m then if len ≤ m*m then 0 else 1 else 2

theorem band_U {m j i : Nat} (hj : j<m) (hi : i<m) : band m (U m j i) = 0 := by
  simp [band, U_lt_B hj hi, U_small hj hi]

theorem band_V {m j i : Nat} (hj : j<m) (hi : i<m) : band m (V m j i) = 1 := by
  simp [band, V_lt_B hj hi, (V_big hj hi).not_ge]

theorem band_hub (m j : Nat) : band m (hub m j) = 2 := by simp [band, (hub_big m j).not_gt]

def EdgeCase.bands : EdgeCase → Nat × Nat
  | .seedL .. => (0,2)
  | .seedR .. => (2,1)
  | .layerL .. => (0,0)
  | .layerR .. => (1,1)

theorem EdgeCase.pair_bands {m : Nat} {edge : EdgeCase} (valid : edge.valid m) :
    (band m (edge.pair m).1.length, band m (edge.pair m).2.length) = edge.bands := by
  cases edge with
  | seedL s i =>
    obtain ⟨hs, hi⟩ := valid
    simp [EdgeCase.pair, EdgeCase.bands, spell, band_U hs hi, band_hub]
  | seedR s i =>
    obtain ⟨hs, hi⟩ := valid
    simp [EdgeCase.pair, EdgeCase.bands, spell, band_V hs hi, band_hub]
  | layerL j i l =>
    obtain ⟨next, hi, hl⟩ := valid
    have hj : j < m := by omega
    simp [EdgeCase.pair, EdgeCase.bands, spell, band_U hj hi, band_U next hl]
  | layerR j i l =>
    obtain ⟨next, hi, hl⟩ := valid
    have hj : j < m := by omega
    simp [EdgeCase.pair, EdgeCase.bands, spell, band_V hj hi, band_V next hl]

theorem EdgeCase.pair_injective {m : Nat} {a b : EdgeCase}
    (validA : a.valid m) (validB : b.valid m) (same : a.pair m = b.pair m) : a=b := by
  have bands : a.bands = b.bands := by
    rw [← pair_bands validA, ← pair_bands validB, same]
  have left := congrArg (fun q : Pair Nat => q.1.length) same
  have right := congrArg (fun q : Pair Nat => q.2.length) same
  cases a <;> cases b <;> simp [EdgeCase.bands] at bands <;>
    simp only [EdgeCase.pair, spell, List.length_replicate] at left right
  case seedL.seedL s i t j =>
    obtain ⟨_, hi⟩ := validA
    obtain ⟨_, hj⟩ := validB
    obtain ⟨rfl,rfl⟩ := U_injective hi hj left
    rfl
  case seedR.seedR s i t j =>
    obtain ⟨hs, hi⟩ := validA
    obtain ⟨ht, hj⟩ := validB
    obtain ⟨rfl,rfl⟩ := V_injective hs hi ht hj right
    rfl
  case layerL.layerL s i j t l r =>
    obtain ⟨_, hi, hj⟩ := validA
    obtain ⟨_, hl, hr⟩ := validB
    obtain ⟨rfl,rfl⟩ := U_injective hi hl right
    obtain ⟨_,rfl⟩ := U_injective hj hr left
    rfl
  case layerR.layerR s i j t l r =>
    obtain ⟨hs, hi, hj⟩ := validA
    obtain ⟨ht, hl, hr⟩ := validB
    obtain ⟨rfl,rfl⟩ := V_injective (by omega : s<m) hi (by omega : t<m) hl left
    obtain ⟨_,rfl⟩ := V_injective hs hj ht hr right
    rfl

end DiamondCount
