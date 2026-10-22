import TransposeFollowup.ComplexMobiusComposition

/-! Preservation of the complex inner product by the existing real-linear
presentation of the complexified action. Multiplication by I is proved to
commute with the action before using complex polarization. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
set_option autoImplicit false

theorem complexPullbackL2_I_smul (g : Group) (f : ComplexL2) :
    complexPullbackL2 g (Complex.I • f) = Complex.I • complexPullbackL2 g f := by
  apply complexL2_ext_parts
  · simp only [complexPullbackL2, realPartL2_complexify, realPartL2_I_smul,
      imagPartL2_complexify, map_neg]
  · simp only [complexPullbackL2, imagPartL2_complexify, imagPartL2_I_smul,
      realPartL2_complexify]

theorem complexPullbackL2_inner (g : Group) (f h : ComplexL2) :
    inner ℂ (complexPullbackL2 g f) (complexPullbackL2 g h) = inner ℂ f h := by
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [show (RCLike.I : ℂ) = Complex.I from rfl, ← complexPullbackL2_I_smul,
    ← map_add, ← map_sub, complexPullbackL2_norm]

theorem complexPullbackL2_inner_transfer (g : Group) (v w : ComplexL2) :
    inner ℂ v (complexPullbackL2 g⁻¹ w) = inner ℂ (complexPullbackL2 g v) w := by
  calc
    _ = inner ℂ (complexPullbackL2 g v)
        (complexPullbackL2 g (complexPullbackL2 g⁻¹ w)) := (complexPullbackL2_inner g _ _).symm
    _ = _ := by rw [← complexPullbackL2_mul, inv_mul_cancel, complexPullbackL2_one]

theorem complexPullbackL2_product_coefficient (g h : Group) (v u : ComplexL2) :
    inner ℂ v (complexPullbackL2 (g * h)⁻¹ u) =
      inner ℂ (complexPullbackL2 g v) (complexPullbackL2 h⁻¹ u) := by
  rw [mul_inv_rev, complexPullbackL2_mul, complexPullbackL2_inner_transfer]

end TransposeFollowup.RealMobius
