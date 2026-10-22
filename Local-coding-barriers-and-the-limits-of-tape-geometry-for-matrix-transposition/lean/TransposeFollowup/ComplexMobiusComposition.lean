import TransposeFollowup.MobiusSchwartzL2Derivative

/-! Composition and exact norm preservation for the actual complex L2
pullback. Its product order is opposite to matrix multiplication. -/
namespace TransposeFollowup
open Classical MeasureTheory
set_option autoImplicit false

theorem complexL2_ext_parts {f h : ComplexL2}
    (hr : realPartL2 f = realPartL2 h) (hi : imagPartL2 f = imagPartL2 h) : f = h := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hn := complexL2_norm_sq_parts (f - h)
  simp only [map_sub, hr, hi, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hn
  exact sq_eq_zero_iff.mp hn

namespace RealMobius

noncomputable def complexPullbackL2 (g : Group) : ComplexL2 →L[ℝ] ComplexL2 :=
  complexifyL2 (actionCLM g⁻¹)

theorem complexPullbackL2_coe (g : Group) (f : ComplexL2) :
    ⇑(complexPullbackL2 g f) =ᵐ[volume] scaledPullback g f :=
  complexify_inverse_action_coe g f

theorem complexPullbackL2_one (f : ComplexL2) : complexPullbackL2 1 f = f := by
  apply complexL2_ext_parts
  · simpa [complexPullbackL2, realPartL2_complexify, inv_one, actionCLM] using
      unitaryAction_one (realPartL2 f)
  · simpa [complexPullbackL2, imagPartL2_complexify, inv_one, actionCLM] using
      unitaryAction_one (imagPartL2 f)

theorem complexPullbackL2_mul (g h : Group) (f : ComplexL2) :
    complexPullbackL2 (g * h) f = complexPullbackL2 h (complexPullbackL2 g f) := by
  apply complexL2_ext_parts
  · simp [complexPullbackL2, realPartL2_complexify, mul_inv_rev, actionCLM,
      unitaryAction_mul]
  · simp [complexPullbackL2, imagPartL2_complexify, mul_inv_rev, actionCLM,
      unitaryAction_mul]

theorem complexPullbackL2_norm (g : Group) (f : ComplexL2) : ‖complexPullbackL2 g f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexL2_norm_sq_parts (complexPullbackL2 g f), complexPullbackL2,
    realPartL2_complexify, imagPartL2_complexify, complexL2_norm_sq_parts f]
  simp [actionCLM]

theorem complexPullbackL2_norm_sub (g : Group) (f h : ComplexL2) :
    ‖complexPullbackL2 g f - complexPullbackL2 g h‖ = ‖f - h‖ := by
  rw [← map_sub, complexPullbackL2_norm]

theorem complexPullbackL2_schwartz (g : Group) (u : SchwartzMap ℝ ℂ) :
    complexPullbackL2 g (u.toLp 2 volume) = schwartzActionL2 g u := rfl

theorem complexPullbackL2_product_difference_le (g h : Group) (f : ComplexL2) :
    ‖complexPullbackL2 (g * h) f - f‖ ≤
      ‖complexPullbackL2 g f - f‖ + ‖complexPullbackL2 h f - f‖ := by
  rw [complexPullbackL2_mul]
  have ht := dist_triangle (complexPullbackL2 h (complexPullbackL2 g f))
    (complexPullbackL2 h f) f
  simpa only [dist_eq_norm, complexPullbackL2_norm_sub] using ht

end RealMobius
end TransposeFollowup
