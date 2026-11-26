import Shoreline
import Mathlib.Algebra.Order.Group.Abs

/-! Sharp worst design biases for a calibrated endpoint contribution. An
interior sample is present at all visits, and its conditional sample
mean estimates the interior mean under each design. -/
namespace Shoreline
noncomputable section

def componentBias (d : Design) (x y : ℝ) : ℝ :=
  (law d).p1*x+(law d).p2*y-1

def envelope (x y z : ℝ) := ∀ d, |componentBias d x y| ≤ z

theorem endpoint_probabilities :
    ((law .uniform).p1+2*(law .uniform).p2)/2=1/5 ∧
    ((law .batch).p1+2*(law .batch).p2)/2=89/669 ∧
    ((law .oneAtATime).p1+2*(law .oneAtATime).p2)/2=257570377/1993493502 := by
  obtain ⟨u,v,w,x,a,b⟩ := probabilities
  rw [u,v,w,x,a,b]
  norm_num

private theorem inequalities {x y z : ℝ} (h : envelope x y z) :
    (-(z) ≤ 32/95*x+3/95*y-1 ∧ 32/95*x+3/95*y-1 ≤ z) ∧
    (-(z) ≤ 160/669*x+3/223*y-1 ∧ 160/669*x+3/223*y-1 ≤ z) ∧
    (-(z) ≤ 17871250/76672827*x+2804903/221499278*y-1 ∧
      17871250/76672827*x+2804903/221499278*y-1 ≤ z) := by
  obtain ⟨u,v,w,t,a,b⟩ := probabilities
  exact ⟨by simpa only [componentBias,u,v] using abs_le.mp (h .uniform),
    by simpa only [componentBias,w,t] using abs_le.mp (h .batch),
    by simpa only [componentBias,a,b] using abs_le.mp (h .oneAtATime)⟩

theorem signed_lower {x y z : ℝ} (h : envelope x y z) :
    58147400/10950683419 ≤ z := by
  obtain ⟨⟨u,v⟩,⟨w,t⟩,a,b⟩ := inequalities h
  linarith

theorem nonnegative_lower {x y z : ℝ} (hy : 0≤y) (h : envelope x y z) :
    377880857/2075649607 ≤ z := by
  obtain ⟨⟨u,v⟩,⟨w,t⟩,a,b⟩ := inequalities h
  linarith

theorem monotone_lower {x y z : ℝ} (hxy : x≤y) (h : envelope x y z) :
    164167/821909 ≤ z := by
  obtain ⟨⟨u,v⟩,⟨w,t⟩,a,b⟩ := inequalities h
  linarith

theorem sharp_calibrations :
    envelope (266283440781/43802733676) (-84267431111/2527080789) (58147400/10950683419) ∧
    envelope (7283918565/2075649607) 0 (377880857/2075649607) ∧
    envelope (2676492/821909) (2676492/821909) (164167/821909) := by
  obtain ⟨u,v,w,t,a,b⟩ := probabilities
  refine ⟨?_,?_,?_⟩ <;> intro d <;> cases d <;> norm_num [componentBias,u,v,w,t,a,b]

#print axioms signed_lower
#print axioms sharp_calibrations
end
end Shoreline
