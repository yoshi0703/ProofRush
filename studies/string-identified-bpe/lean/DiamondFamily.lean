import Common
import Separators

namespace DiamondFamily
open SpellingBPE SpellingDecoy SpellingSeparators

def privatePair (j : ℕ) : Pair ℕ := ([j+1],[j+1])
def privatePairs (k : ℕ) : List (Pair ℕ) := (List.range k).map privatePair
def extras (m k : ℕ) : Table ℕ := (privatePairs k).map (fun p => extra (m+1) p [])
def input (m k : ℕ) : Word (ℕ ⊕ ℕ) := single (Diamond.coreTable m ++ extras m k)

theorem private_injective : Function.Injective privatePair := by
  intro i j eq
  have h := congrArg Prod.fst eq
  simpa [privatePair] using h

theorem private_nodup (k : ℕ) : (privatePairs k).Nodup :=
  List.Nodup.map private_injective List.nodup_range

theorem private_length (k : ℕ) : (privatePairs k).length = k := by simp [privatePairs]

end DiamondFamily
