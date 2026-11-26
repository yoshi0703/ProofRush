import ReadoutBarrier

namespace AttentionWindows
open AttentionGrid AttentionModel AttentionBridge AttentionChart
noncomputable section

/-- A symmetric polynomial threshold on actual bit vectors missed by every
H-head, value-dimension-d softmax representation and every readout polynomial
of total degree at most D. Both choices of the sign at zero are included. -/
def Misses (H D d : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ b : MvPolynomial (Fin n) ℝ, b.totalDegree ≤ H*D ∧
    (∀ x y : Fin n → Bool, hammingWeight x = hammingWeight y →
      MvPolynomial.eval (booleanReals x) b = MvPolynomial.eval (booleanReals y) b) ∧
    (∀ x : Fin n → Bool, MvPolynomial.eval (booleanReals x) b ≠ 0) ∧
    ∀ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (g : MvPolynomial (Fin d) ℝ),
      (∀ h, 0 < r h) → g.totalDegree ≤ D → ∀ zeroPositive : Bool,
      ¬ (∀ bits : Fin n → Bool, 0 < MvPolynomial.eval (booleanReals bits) b ↔
        let score := MvPolynomial.eval
          (fun i => heads r v0 v1 i (grid n (hammingWeight bits))) g
        if zeroPositive then 0 ≤ score else 0 < score)

theorem insufficient_dimension {H D d : ℕ}
    (small : Count H d (AttentionEnumeration.count d D) < H*D) : Misses H D d := by
  obtain ⟨n,hn,target,b,_,bd,vals,nonzero,miss⟩ := readout_obstruction small
    (AttentionEnumeration.exponent d D) (AttentionEnumeration.exponent_bounded d D)
  refine ⟨n,hn,b,bd,?_,?_,?_⟩
  · intro x y h
    rw [vals,vals,h]
  · intro x
    rw [vals]
    exact nonzero ⟨hammingWeight x,Nat.lt_succ_of_le (hammingWeight_le x)⟩
  · intro r v0 v1 g hr degree zeroPositive agree
    let z (k : Fin (n+1)) := fun i => heads r v0 v1 i (grid n k)
    have weak (k : Fin (n+1)) : 0 < target.eval (grid n k) ↔
        if zeroPositive then 0 ≤ MvPolynomial.eval (z k) g else 0 < MvPolynomial.eval (z k) g := by
      simpa only [vals,hammingWeight_bitsAtWeight,z] using agree (bitsAtWeight k)
    obtain ⟨a,strict⟩ := strict_bias _ _ nonzero zeroPositive weak
    let shifted := g + MvPolynomial.C a
    have hd : shifted.totalDegree ≤ D :=
      (MvPolynomial.totalDegree_add ..).trans (max_le degree (by simp))
    apply miss r v0 v1 (fun k => shifted.coeff (AttentionEnumeration.expFinsupp d D k)) hr
    intro k
    rw [readout_complete shifted hd]
    simpa only [shifted,map_add,MvPolynomial.eval_C,z] using strict k

/-- In particular, d ≤ D−2 cannot work uniformly as soon as H ≥ 4^D. -/
theorem logarithmic_dimension {H D d : ℕ} (large : 4^D ≤ H) (atLeast : 3 ≤ D)
    (narrow : d+2 ≤ D) : Misses H D d := by
  apply insufficient_dimension
  change (d+1)*(H+1)+(d+D).choose D < H*D
  rw [Nat.add_comm d D, Nat.choose_symm_add (a:=D) (b:=d)]
  exact parameter_shortage large atLeast narrow

end
end AttentionWindows
