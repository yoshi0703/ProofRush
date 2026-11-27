import LabelInvariance
import TailSortedForm

open CanonneDiffuse

namespace CanonneHeadEnvelope.CanonicalSplit

variable {A : Type*} [Fintype A] [DecidableEq A] {q : A → ℝ} {ε : ℝ}

/-- Exact finite radical formula for the original-label tail mask of the canonical split. -/
theorem tail_root_eq_finite_formula (s : CanonicalSplit q ε) (hq : IsLaw q)
    {n : ℝ} (hn : 0 ≤ n) :
    CanonneQuantile.root (CanonneQuantile.tailMask s.tailSet q)
      (CanonneQuantile.tailMask_nonneg s.tailSet hq) n hn =
      CanonneQuantile.tailPrefixQuadraticMinimum (fun j ↦ q (s.tail j)) n :=
  (s.tail_root_eq hq hn).trans
    (CanonneQuantile.tail_root_eq_prefix_quadratic_minimum
      (fun j ↦ q (s.tail j)) (fun j ↦ hq.nonneg (s.tail j)) s.tail_sorted hn)

end CanonneHeadEnvelope.CanonicalSplit
