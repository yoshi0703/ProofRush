import Peetre
import Lower
import Upper

namespace Canonne

/-- A direct comparison for all sorted probability laws on the natural numbers. -/
theorem two_radius {p : ℕ → ℝ} {s e : ℝ} {ks ke : ℕ} (hp : Law p)
    (hs : 0 < s) (hse : s < e) (he : e < 1) (cs : Cut p s ks) (ce : Cut p e ke) :
    phiAt p ke ≤ inverseK p e ∧
    inverseK p e ≤ Real.sqrt (1 + (phiAt p ks / (4 * (e-s))) ^ 2) := by
  obtain ⟨v,hv,eq,_⟩ := inverse_attained hp (hs.trans hse) he
  obtain ⟨z,hz,hbound⟩ := exists_upper_witness hp cs hse
  exact ⟨(phiAt_le_ell2 hp ce hv).trans_eq eq, (inverseK_le_ell2 hp hz).trans hbound⟩

end Canonne
