import ForestGaps
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image

/-! The set of short-gap adjacency spellings is indexed by side, later stage,
    and positive gap. Distinct labels may have the same literal spelling. -/
namespace BPEForest

abbrev GapLabel (k s : Nat) := Fin 2 × Fin k × Fin s

theorem labels_card_le {β : Type} [DecidableEq β] (k s : Nat)
    (spellings : GapLabel k s → β) :
    (Finset.univ.image spellings).card ≤ 2*k*s := by
  calc
    (Finset.univ.image spellings).card ≤ (Finset.univ : Finset (GapLabel k s)).card :=
      Finset.card_image_le
    _ = 2*k*s := by simp [GapLabel, Nat.mul_assoc]

end BPEForest
