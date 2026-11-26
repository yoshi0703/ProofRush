import Witness
import DiamondFamily

namespace DiamondConclusion
open SpellingBPE SpellingDecoy SpellingSeparators Diamond DiamondComparator DiamondWitness
noncomputable section

theorem extras_nonempty (m k : Nat) : ∀ row ∈ DiamondFamily.extras m k,
    ∀ token ∈ row.2, token ≠ [] := by
  intro row hr token ht
  simp only [DiamondFamily.extras, List.mem_map] at hr
  obtain ⟨p,hp,rfl⟩ := hr
  simp only [DiamondFamily.privatePairs, List.mem_map] at hp
  obtain ⟨j,_,rfl⟩ := hp
  simp [extra, DiamondFamily.privatePair] at ht
  subst token
  simp

theorem input_nonempty (m k : Nat) : ∀ token ∈ DiamondFamily.input m k, token ≠ [] := by
  exact serialized_nonempty m _ (extras_nonempty m k)

theorem input_not_unique (m k : Nat) (hm : 1<m) : ¬UniqueDecoding (DiamondFamily.input m k) :=
  serialized_not_unique m hm _

theorem input_comparator (m k : Nat) :
    PartialPlay (DiamondFamily.input m k) ((comparator m).map liftPair)
      (blocks 0 ((rows m).map fun _ => [spell (hub m m)]) ++
        blocks (rows m).length (weightedRows (DiamondFamily.extras m k))) :=
  serialized_augmented_run m _

theorem input_exact_saving (m k : Nat) :
    (DiamondFamily.input m k).length =
      (blocks 0 ((rows m).map fun _ => [spell (hub m m)]) ++
        blocks (rows m).length (weightedRows (DiamondFamily.extras m k))).length + m*m*m*(m+1) :=
  serialized_exact_saving m _

end
end DiamondConclusion
