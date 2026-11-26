import ParameterBounds
import ProfileRoots
import Symmetry

/-! Joint dimension bounds in the original softmax value space. -/
namespace AttentionJoint
open AttentionBounds AttentionGrid AttentionModel AttentionUpper
noncomputable section
attribute [local instance] Classical.propDecidable

theorem bitWeight_grid {n : ℕ} (x : Fin n → Bool) :
    bitWeight x = grid n (hammingWeight x) := by
  simp [bitWeight, grid, hammingWeight]

/-- Every strict grid polynomial of degree at most HD has a representation
on all bits of this length by the same heads and one polynomial readout. -/
def GridCovers (H D d : ℕ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ F : Polynomial ℝ, F.natDegree ≤ H*D →
    (∀ k ≤ n, F.eval (grid n k) ≠ 0) →
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (g : MvPolynomial (Fin d) ℝ),
      (∀ h, 0 < r h) ∧ g.totalDegree ≤ D ∧ ∀ bits : Fin n → Bool,
        (0 < MvPolynomial.eval (fun i => heads r v0 v1 i (grid n (hammingWeight bits))) g ↔
          0 < F.eval (grid n (hammingWeight bits)))

theorem grouped_covers {H D : ℕ} (hh : 0 < H) : GridCovers H D D := by
  intro n hn F degree nz
  obtain ⟨r,v0,v1,g,hr,_,hg,agreement⟩ :=
    AttentionProfileRoots.threshold_attention hh hn F degree nz
  exact ⟨r,v0,v1,g,hr,hg,fun x => by simpa only [bitWeight_grid] using agreement x⟩

theorem grid_sufficient {H D : ℕ} (hh : 0 < H) (hd : 0 < D) :
    ∃ d, 0 < d ∧ d ≤ min D (32 * index H D) ∧ GridCovers H D d := by
  by_cases small : D ≤ 32 * index H D
  · exact ⟨D,hd,le_min le_rfl small,grouped_covers hh⟩
  have spec := index_spec H D
  have headmul : H ≤ H*D := by simpa using Nat.mul_le_mul_left H hd
  obtain ⟨b,p,hb,hpow,hadd,hdim⟩ :=
    radix_parameters spec.1 (Nat.le_of_lt (lt_of_not_ge small))
      (headmul.trans ((Nat.le_succ _).trans spec.2))
  obtain ⟨d,hpos,hsize,r,v0,v1,hr,universal⟩ := radix_shared_attention hh hb hpow hadd
  refine ⟨d,hpos,le_min (by omega) (by omega),?_⟩
  intro n _ F degree _
  obtain ⟨g,_,hg,all⟩ := universal F degree
  exact ⟨r,v0,v1,g,hr,hg, fun x => all _ (by unfold grid; positivity)⟩

/-- Every symmetric sign represented by a Boolean polynomial of degree at
most HD is represented on the same Boolean inputs with strict margins. -/
def Covers (H D d : ℕ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ b : MvPolynomial (Fin n) ℝ, b.totalDegree ≤ H*D →
    (∀ x : Fin n → Bool, MvPolynomial.eval (booleanReals x) b ≠ 0) →
    (∀ x y : Fin n → Bool, hammingWeight x = hammingWeight y →
      (0 < MvPolynomial.eval (booleanReals x) b ↔ 0 < MvPolynomial.eval (booleanReals y) b)) →
    ∃ (r : Fin H → ℝ) (v0 v1 : Fin H → Fin d → ℝ) (g : MvPolynomial (Fin d) ℝ),
      (∀ h, 0 < r h) ∧ g.totalDegree ≤ D ∧ ∀ x : Fin n → Bool,
        0 < MvPolynomial.eval (booleanReals x) b *
          MvPolynomial.eval (fun i => heads r v0 v1 i (grid n (hammingWeight x))) g

theorem covers_of_grid {H D d : ℕ} (enough : GridCovers H D d) : Covers H D d := by
  intro n hn b deg strict symm
  obtain ⟨p,dp,hp⟩ := AttentionSymmetry.exists_grid_sign hn b deg strict symm
  have nz : ∀ k ≤ n, p.eval (grid n k) ≠ 0 := by
    intro k hk
    let j : Fin (n+1) := ⟨k,by omega⟩
    have a := hp (bitsAtWeight j)
    rw [hammingWeight_bitsAtWeight] at a
    exact (mul_ne_zero_iff.mp a.ne').1
  obtain ⟨r,v0,v1,g,hr,dg,hg⟩ := enough n hn p dp nz
  let z (x : Fin n → Bool) := fun i => heads r v0 v1 i (grid n (hammingWeight x))
  have weak (x : Fin n → Bool) : 0 < MvPolynomial.eval (booleanReals x) b ↔
      0 < MvPolynomial.eval (z x) g := by
    refine Iff.trans ?_ (hg x).symm
    have h := hp x
    constructor <;> intro pos
    · exact (mul_pos_iff_of_pos_right pos).mp h
    · exact (mul_pos_iff_of_pos_left pos).mp h
  obtain ⟨a,ha⟩ := AttentionWindows.strict_bias
    (fun x => MvPolynomial.eval (booleanReals x) b) (fun x => MvPolynomial.eval (z x) g)
    strict false weak
  refine ⟨r,v0,v1,g + MvPolynomial.C a,hr,
    (MvPolynomial.totalDegree_add ..).trans (max_le dg (by simp)),?_⟩
  intro x
  simpa only [z, map_add, MvPolynomial.eval_C] using ha x

theorem universal_exists (H D : ℕ) (hh : 0 < H) (hd : 0 < D) :
    ∃ d, 0 < d ∧ d ≤ min D (32 * index H D) ∧ Covers H D d := by
  obtain ⟨d,hp,cap,all⟩ := grid_sufficient hh hd
  exact ⟨d,hp,cap,covers_of_grid all⟩

theorem misses_excludes {H D d : ℕ} (bad : AttentionWindows.Misses H D d) : ¬ Covers H D d := by
  obtain ⟨n,hn,b,deg,symmetric,strict,miss⟩ := bad
  intro all
  obtain ⟨r,v0,v1,g,hr,dg,agree⟩ := all n hn b deg strict
    (fun x y h => by rw [symmetric x y h])
  apply miss r v0 v1 g hr dg false
  intro x
  change (0 < _) ↔ 0 < _
  have h := agree x
  constructor <;> intro pos
  · exact (mul_pos_iff_of_pos_left pos).mp h
  · exact (mul_pos_iff_of_pos_right pos).mp h

private theorem exists_cover (H D : ℕ) (hh : 0 < H) (hd : 0 < D) :
    ∃ d, 0 < d ∧ Covers H D d := by
  obtain ⟨d,hp,_,all⟩ := universal_exists H D hh hd
  exact ⟨d,hp,all⟩

noncomputable def leastDimension (H D : ℕ) (hh : 0 < H) (hd : 0 < D) : ℕ :=
  Nat.find (exists_cover H D hh hd)

theorem joint_dimension (H D : ℕ) (hh : 0 < H) (hd : 0 < D) :
    min D (index H D) ≤ 3 * leastDimension H D hh hd ∧
    leastDimension H D hh hd ≤ min D (32 * index H D) := by
  let d := leastDimension H D hh hd
  have spec : 0 < d ∧ Covers H D d := Nat.find_spec (exists_cover H D hh hd)
  constructor
  · by_contra! tooSmall
    exact misses_excludes (necessary_dimension spec.1 tooSmall) spec.2
  · obtain ⟨u,hp,cap,all⟩ := universal_exists H D hh hd
    exact (Nat.find_min' (exists_cover H D hh hd) ⟨hp,all⟩).trans cap

theorem logarithmic_dimension (H D : ℕ) (hh : 0 < H) (hd : 0 < D)
    (many : 4^D ≤ H) (three : 3 ≤ D) :
    D-1 ≤ leastDimension H D hh hd ∧ leastDimension H D hh hd ≤ D := by
  let d := leastDimension H D hh hd
  have spec : 0 < d ∧ Covers H D d := Nat.find_spec (exists_cover H D hh hd)
  constructor
  · by_contra! tooSmall
    have narrow : d+2 ≤ D := by change d < D-1 at tooSmall; omega
    exact misses_excludes (AttentionWindows.logarithmic_dimension many three narrow) spec.2
  · exact (joint_dimension H D hh hd).2.trans (min_le_left ..)

#print axioms joint_dimension
#print axioms logarithmic_dimension

end
end AttentionJoint
