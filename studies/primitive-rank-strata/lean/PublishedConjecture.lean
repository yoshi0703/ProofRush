import Stratum105
import GapWords
import IntegerScales
import Mathlib.Data.Nat.PrimeFin

/-! Kászonyi, Publ. Math. Debrecen 77 (2010), p. 328, at n = 105
and α = 2. The primitive condition below is on the binary word itself. -/

namespace Kasonyi105

def Noncrossing {r : ℕ} (period : Fin r → Gap) : Prop :=
  ∀ (u v : Fin r) (i j k l : Idx), i < j → j < k → k < l →
    ¬ (period u i ≠ 0 ∧ period v j ≠ 0 ∧ period u k ≠ 0 ∧ period v l ≠ 0)

def StratifiedSemilinear (W : Set Gap) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℕ) (base : Fin m → Gap) (period : ∀ j, Fin (r j) → Gap),
    (∀ j p, TwoSparse (period j p)) ∧ (∀ j, Noncrossing (period j)) ∧
      W = ⋃ j, linear (base j) (period j)

theorem stratified_implies_twoSparse {W : Set Gap} (h : StratifiedSemilinear W) :
    TwoSparseSemilinear W := by
  obtain ⟨m, r, b, d, hs, _, he⟩ := h
  exact ⟨m, r, b, d, hs, he⟩

def ExactWordStratum : Set Gap :=
  {e | TopZero (intGap e) ∧ AllPairsActive (intGap e) ∧ KasonyiWord.Primitive (KasonyiWord.encode e)}

theorem ray_word_primitive (t : ℕ) :
    KasonyiWord.Primitive (KasonyiWord.encode (ray (105*t+1))) := by
  apply KasonyiWord.primitive_of_coprime _ (by decide)
  rw [ray_sum, show 23*(105*t+1) = 23+105*(23*t) by ring,
    Nat.coprime_add_mul_left_right]
  decide

theorem ray_mem_exact_word_stratum (t : ℕ) : ray (105*t+1) ∈ ExactWordStratum :=
  ⟨ray_topZero _, ray_pairs_active (by omega), ray_word_primitive t⟩

/-- This is the negation of the published universal assertion at one
admissible pair of parameters. Each admissible pair of prime directions
has a nonzero second difference and every third difference vanishes. -/
theorem published_intermediate_conjecture_false :
    ¬ StratifiedSemilinear ExactWordStratum := by
  intro h
  exact no_twoSparse_cover_of_ray ExactWordStratum (fun _ he => he.1)
    ray_mem_exact_word_stratum (stratified_implies_twoSparse h)

def PublishedExactSet : Set Gap :=
  {e | TopZeroInteger (intGap e) ∧ AllPairsInteger (intGap e) ∧
    KasonyiWord.Primitive (KasonyiWord.encode e)}

theorem original_integer_scale_refutation : ¬ StratifiedSemilinear PublishedExactSet := by
  have he : PublishedExactSet = ExactWordStratum := by
    ext e
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    rw [topZeroInteger_iff, allPairsInteger_iff]
  exact he ▸ published_intermediate_conjecture_false

def SomePairInteger (f : Idx → ℤ) : Prop :=
  (∃ (t u : ℤ) (i : Idx), t%3 ≠ 0 ∧ u%5 ≠ 0 ∧
    deltaInteger (t*35) (deltaInteger (u*21) f) i ≠ 0) ∨
  (∃ (t v : ℤ) (i : Idx), t%3 ≠ 0 ∧ v%7 ≠ 0 ∧
    deltaInteger (t*35) (deltaInteger (v*15) f) i ≠ 0) ∨
  (∃ (u v : ℤ) (i : Idx), u%5 ≠ 0 ∧ v%7 ≠ 0 ∧
    deltaInteger (u*21) (deltaInteger (v*15) f) i ≠ 0)

def ExistentialRankSet : Set Gap :=
  {e | TopZeroInteger (intGap e) ∧ SomePairInteger (intGap e) ∧
    KasonyiWord.Primitive (KasonyiWord.encode e)}

theorem existential_rank_refutation : ¬ StratifiedSemilinear ExistentialRankSet := by
  intro h
  apply no_twoSparse_cover_of_ray ExistentialRankSet
    (fun e he => (topZeroInteger_iff _).mp he.1) _ (stratified_implies_twoSparse h)
  intro t
  have hr := ray_mem_exact_word_stratum t
  have hp := (allPairsInteger_iff _).mpr hr.2.1
  obtain ⟨i, hi⟩ := hp.1 1 1 (by decide) (by decide)
  exact ⟨(topZeroInteger_iff _).mpr hr.1,
    Or.inl ⟨1, 1, i, by decide, by decide, hi⟩, hr.2.2⟩

/-- The author's Q_n, at n=105, as a set of binary words. -/
def Q105 : Set KasonyiWord.Word :=
  {w | (∃ e : Gap, KasonyiWord.encode e = w) ∧ KasonyiWord.Primitive w}

/-- Recover the exponent list from an actual word of the language. -/
def E (L : Set KasonyiWord.Word) : Set Gap :=
  {e | ∃ w ∈ L, KasonyiWord.decode w = (0, List.ofFn e)}

theorem exponent_mem_iff (e : Gap) : e ∈ E Q105 ↔ KasonyiWord.Primitive (KasonyiWord.encode e) := by
  constructor
  · rintro ⟨w, ⟨⟨f, rfl⟩, h⟩, hd⟩
    rw [KasonyiWord.decode_encode] at hd
    have he : f = e := List.ofFn_injective (congrArg Prod.snd hd)
    exact he ▸ h
  · intro h
    exact ⟨_, ⟨⟨e, rfl⟩, h⟩, KasonyiWord.decode_encode e⟩

def E2 : Set Gap :=
  {e | (∀ t u v : ℤ, Nat.Coprime 3 t.natAbs → Nat.Coprime 5 u.natAbs →
          Nat.Coprime 7 v.natAbs → ∀ i, integerBox (t*35) (u*21) (v*15) (intGap e) i = 0) ∧
       AllPairsInteger (intGap e)}

theorem prime_factors_105 : (105 : ℕ).primeFactors = {3, 5, 7} := by
  rw [show (105 : ℕ) = 3*(5*7) by decide, Nat.primeFactors_mul (by decide) (by decide),
    Nat.primeFactors_mul (by decide) (by decide),
    (by decide : Nat.Prime 3).primeFactors, (by decide : Nat.Prime 5).primeFactors,
    (by decide : Nat.Prime 7).primeFactors]
  decide

/-- The exact intersection and full stratification condition in the published conjecture. -/
theorem page328_intersection : ¬ StratifiedSemilinear (E2 ∩ E Q105) := by
  have he : E2 ∩ E Q105 = PublishedExactSet := by
    ext e
    change ((_ ∧ _) ∧ e ∈ E Q105) ↔ (_ ∧ _ ∧ _)
    rw [exponent_mem_iff, and_assoc]
    unfold TopZeroInteger
    have h3 (t : ℤ) : Nat.Coprime 3 t.natAbs ↔ t%3 ≠ 0 :=
      (admissible_iff_natCoprime (by decide : Nat.Prime 3) t).symm
    have h5 (t : ℤ) : Nat.Coprime 5 t.natAbs ↔ t%5 ≠ 0 :=
      (admissible_iff_natCoprime (by decide : Nat.Prime 5) t).symm
    have h7 (t : ℤ) : Nat.Coprime 7 t.natAbs ↔ t%7 ≠ 0 :=
      (admissible_iff_natCoprime (by decide : Nat.Prime 7) t).symm
    simp only [← deltaInteger_box, h3, h5, h7]
  exact he ▸ original_integer_scale_refutation

end Kasonyi105
