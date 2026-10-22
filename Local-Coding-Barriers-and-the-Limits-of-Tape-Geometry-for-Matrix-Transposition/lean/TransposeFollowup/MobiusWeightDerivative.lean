import TransposeFollowup.RealMobiusWeighted
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The exact derivative of the absolute Jacobian weight, on both sides
of the possible pole. No positivity of the denominator is assumed. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
set_option autoImplicit false

theorem hasDerivAt_denom (g : Group) (x : ℝ) : HasDerivAt (denom g) (g 1 0) x := by
  convert ((hasDerivAt_id x).const_mul (g 1 0)).add_const (g 1 1) using 1
  · rfl
  · simp only [mul_one]

theorem hasDerivAt_inverse_abs_denom (g : Group) {x : ℝ} (hx : x ∈ domain g) :
    HasDerivAt (fun y => |denom g y|⁻¹) (-(g 1 0 / denom g x) * |denom g x|⁻¹) x := by
  have hd := hasDerivAt_denom g x
  have hn : denom g x ≠ 0 := hx
  obtain hneg | hpos := hn.lt_or_gt
  · have ha : HasDerivAt (fun y => |denom g y|) (-g 1 0) x := by
      simpa only [Function.comp_def, neg_one_mul] using (hasDerivAt_abs_neg hneg).comp x hd
    convert ha.inv (abs_ne_zero.mpr hn) using 1
    rw [abs_of_neg hneg]
    field_simp
  · have ha : HasDerivAt (fun y => |denom g y|) (g 1 0) x := by
      simpa only [Function.comp_def, one_mul] using (hasDerivAt_abs_pos hpos).comp x hd
    convert ha.inv (abs_ne_zero.mpr hn) using 1
    rw [abs_of_pos hpos]
    field_simp

end TransposeFollowup.RealMobius
