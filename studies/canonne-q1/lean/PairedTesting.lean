import PairedAlphabet
import FiniteChiSquare

open scoped BigOperators

namespace CanonneHeadEnvelope

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem embedded_iid_mixture_tv_bound (n : ℕ) (e : (ι × Bool) ↪ α) (h : α → ℝ) (z : ι → ℝ)
    (hp : ∀ a : ι × Bool, 0 < h (e a)) (hn : ∑ a, h a = 1)
    (hw : ∀ a, 0 ≤ h a) (hz : ∀ i, 0 ≤ z i)
    (hb : ∀ a : ι × Bool, z a.1 ≤ h (e a)) :
    let M := mixture (fun s : ι → Bool ↦ iidMass n (embeddedLaw e h z s))
    (∑ x, |M x - iidMass n h x|) / 2 ≤
      Real.sqrt (Real.exp (∑ i, ((n : ℝ) * pairCoefficient (h ∘ e) z i)^2 / 2) - 1) / 2 := by
  intro M
  obtain ⟨hM, hchi⟩ := embedded_iid_mixture_bound n e h z hp hn hw hz hb
  have hp1 : ∑ a, M a = 1 :=
    mixture_normalized fun s ↦ iidMass_normalized n (hM s).2.1
  have hq1 : ∑ a, iidMass n h a = 1 := iidMass_normalized n hn
  have hq : ∀ x, 0 ≤ iidMass n h x := fun x ↦ Finset.prod_nonneg fun j _ ↦ hw (x j)
  have hzm : ∀ x, iidMass n h x = 0 → M x = 0 := by
    intro x hx
    have hzs (s : ι → Bool) : iidMass n (embeddedLaw e h z s) x = 0 := by
      apply iidMass_supported n (q := h) ?_ hx
      intro a ha
      have hs : a ∉ Set.range e := by
        rintro ⟨b,rfl⟩
        exact (hp b).ne' ha
      rw [embeddedLaw_unchanged e h z s hs, ha]
    dsimp [M, mixture]
    simp [hzs]
  apply (finite_tv_le_chiSquare hq hp1 hq1 hzm).trans
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (sub_le_sub_right hchi 1)) (by norm_num)

end CanonneHeadEnvelope
