import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic

namespace CanonneHeadEnvelope

/-- Real weights on a finite alphabet can be sorted without discarding tied labels. -/
theorem exists_sorted_equiv {A : Type*} [Fintype A] (q : A → ℝ) :
    ∃ e : Fin (Fintype.card A) ≃ A, Antitone (fun i ↦ q (e i)) := by
  classical
  let e₀ := (Fintype.equivFin A).symm
  let L := List.ofFn e₀
  let cmp (a b : A) : Bool := decide (q b ≤ q a)
  let S := L.mergeSort cmp
  have hperm : S.Perm L := List.mergeSort_perm _ _
  have hL : L.Nodup := List.nodup_ofFn_ofInjective e₀.injective
  have hS : S.Nodup := hperm.nodup_iff.mpr hL
  have Hall (a : A) : a ∈ S := hperm.mem_iff.mpr (List.mem_ofFn.mpr (e₀.surjective a))
  have hlen : Fintype.card A = S.length := by rw [hperm.length_eq]; exact List.length_ofFn.symm
  let getEquiv := hS.getEquivOfForallMemList S Hall
  let e := (finCongr hlen).trans getEquiv
  have hsort : S.Pairwise (fun a b ↦ q b ≤ q a) := by
    have hh := List.pairwise_mergeSort (le := cmp)
      (fun a b c hab hbc ↦ by
        simp only [cmp, decide_eq_true_eq] at hab hbc ⊢
        exact hbc.trans hab)
      (fun a b ↦ by
        simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total (q b) (q a))
      L
    simpa only [cmp, decide_eq_true_eq] using hh
  refine ⟨e,?_⟩
  intro i j hij
  rcases le_iff_eq_or_lt.mp hij with rfl | hij
  · rfl
  · exact List.pairwise_iff_get.mp hsort (finCongr hlen i) (finCongr hlen j) hij

theorem exists_sorted_succ_equiv {A : Type*} [Fintype A] [Nonempty A] (q : A → ℝ) :
    ∃ d : ℕ, ∃ e : Fin (d+1) ≃ A, Antitone (fun i ↦ q (e i)) := by
  obtain ⟨e,ho⟩ := exists_sorted_equiv q
  let d := Fintype.card A - 1
  have he : d+1 = Fintype.card A := by
    dsimp [d]
    have := Fintype.card_pos (α := A)
    omega
  exact ⟨d,(finCongr he).trans e,fun _ _ h ↦ ho h⟩

end CanonneHeadEnvelope
