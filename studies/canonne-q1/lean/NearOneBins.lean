import NearOneTesting
import Mathlib.Algebra.Order.Archimedean.Basic

namespace CanonneNearOneTesting

open CanonneDiffuse
open scoped BigOperators
noncomputable section

/-- Every positive weight below the top has a bin with the chosen strict
lower endpoint, including weights exactly on a power-of-two boundary. -/
theorem exists_dyadic_bin {x top : ℝ} (hx : 0 < x) (htop : 0 < top)
    (hxtop : x ≤ top) :
    ∃ j : ℕ, x ≤ top * (1/2 : ℝ)^j ∧ top * (1/2 : ℝ)^j ≤ 2*x := by
  obtain ⟨j, hlo, hu⟩ := exists_nat_pow_near_of_lt_one (div_pos hx htop)
    ((div_le_one htop).mpr hxtop) (by norm_num : (0 : ℝ) < 1/2) (by norm_num)
  have hright := (lt_div_iff₀ htop).mp hlo
  rw [pow_succ] at hright
  refine ⟨j, ?_, ?_⟩
  · simpa [mul_comm] using (div_le_iff₀ htop).mp hu
  · nlinarith

/-- Finite instance-optimal near-one lower bound, with the dyadic assignment,
actual iid product sampling and randomized tests included. -/
theorem no_good_test_small_near_one_moment {A : Type*} [Fintype A] [DecidableEq A]
    {q : A → ℝ} (hq : IsLaw q) {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsmall : (n : ℝ) * CanonneNearOne.nearOneMoment q δ ≤ 1/64) :
    ¬ ∃ f, GoodTest q (1-δ) n f := by
  classical
  let L := {a : A // 0 < q a ∧ q a ≤ δ / 16}
  let d (a : L) : ℕ := Classical.choose
    (exists_dyadic_bin a.2.1 (show 0 < δ / 16 by positivity) a.2.2)
  have hd (a : L) :
      q a ≤ (δ/16) * (1/2 : ℝ)^(d a) ∧ (δ/16) * (1/2 : ℝ)^(d a) ≤ 2*q a :=
    Classical.choose_spec (exists_dyadic_bin a.2.1 (show 0 < δ / 16 by positivity) a.2.2)
  let bins : Finset ℕ := Finset.univ.image d
  let B := {j : ℕ // j ∈ bins}
  let bin (a : A) : Option B :=
    if h : 0 < q a ∧ q a ≤ δ / 16 then
      some ⟨d ⟨a, h⟩, Finset.mem_image.mpr ⟨⟨a,h⟩, Finset.mem_univ _, rfl⟩⟩
    else none
  let u (j : B) := (δ/16) * (1/2 : ℝ)^(j.val)
  have occupied (a : L) :
      bin a = some ⟨d a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩ := by
    unfold bin
    rw [dite_eq_left a.2]
  have bounds (a : A) (j : B) (h : bin a = some j) :
      q a ≤ u j ∧ u j ≤ 2*q a ∧ q a ≤ δ/16 := by
    have hl : 0 < q a ∧ q a ≤ δ / 16 := by
      by_contra hn
      simp [bin, hn] at h
    have hm := (occupied ⟨a, hl⟩).symm.trans h
    have hj : d ⟨a,hl⟩ = j.val := congrArg Subtype.val (Option.some.inj hm)
    have ht := hd ⟨a, hl⟩
    rw [hj] at ht
    exact ⟨ht.1, ht.2, hl.2⟩
  apply no_good_test_of_dyadic_bins hq hn hδ hsmall bin u
  · intro j
    unfold u
    positivity
  · intro a ha hl
    rw [occupied ⟨a,ha,hl⟩]
    simp
  · intro j
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp j.2
    refine ⟨a, ?_⟩
    apply (occupied a).trans
    congr 1
    exact Subtype.ext ha
  · exact fun a j h => (bounds a j h).1
  · exact fun a j h => (bounds a j h).2.1
  · exact fun a j h => (bounds a j h).2.2
  · have hgeo := CanonneColoredPilot.dyadic_top_sum
      (top := δ/16) (by positivity) bins
    have heq : (∑ j : B, u j) = ∑ j ∈ bins, (δ/16) * (1/2 : ℝ)^j := by
      unfold u B
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach bins (fun j => (δ/16) * (1/2 : ℝ)^j)
    rw [heq]
    linarith

end
end CanonneNearOneTesting
