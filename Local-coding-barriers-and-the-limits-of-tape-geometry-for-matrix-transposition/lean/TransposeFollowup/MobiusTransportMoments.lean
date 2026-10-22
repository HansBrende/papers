import TransposeFollowup.MobiusDifferentialTransport

/-! Explicit spatial-moment bounds for the transported derivative.
No frequency support or global closeness of a Mobius map is assumed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
set_option autoImplicit false

theorem real_sub_sq_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

theorem real_sub_fourth_le (a b : ℝ) : (a - b) ^ 4 ≤ 8 * a ^ 4 + 8 * b ^ 4 := by
  have h := pow_le_pow_left₀ (sq_nonneg (a - b)) (real_sub_sq_le a b) 2
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

theorem norm_sub_sq_le_twice {E : Type*} [NormedAddCommGroup E] (v w : E) :
    ‖v - w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  calc
    _ ≤ (‖v‖ + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le v w) 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖v‖ - ‖w‖)]

theorem differentialTransport_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Group) (u du : ℝ → E) (y : ℝ) :
    ‖differentialTransport g u du y‖ ^ 2 ≤
      (16 * (g 0 0) ^ 4) * ‖du y‖ ^ 2 +
      (16 * (g 1 0) ^ 4) * (y ^ 4 * ‖du y‖ ^ 2) +
      (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * ‖u y‖ ^ 2 +
      (4 * (g 1 0) ^ 4) * (y ^ 2 * ‖u y‖ ^ 2) := by
  let a := g 0 0
  let c := g 1 0
  have h := norm_sub_sq_le_twice ((a - c * y) ^ 2 • du y) ((c * (a - c * y)) • u y)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
  have h4 := mul_le_mul_of_nonneg_right (real_sub_fourth_le a (c * y))
    (sq_nonneg ‖du y‖)
  have h2 := mul_le_mul_of_nonneg_right (real_sub_sq_le a (c * y))
    (mul_nonneg (sq_nonneg c) (sq_nonneg ‖u y‖))
  rw [differentialTransport_explicit]
  dsimp [a, c] at h h4 h2
  nlinarith

theorem integral_differentialTransport_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Group) (u du : ℝ → E)
    (hT : Integrable (fun y => ‖differentialTransport g u du y‖ ^ 2))
    (hd : Integrable (fun y => ‖du y‖ ^ 2))
    (hyd : Integrable (fun y => y ^ 4 * ‖du y‖ ^ 2))
    (hu : Integrable (fun y => ‖u y‖ ^ 2))
    (hyu : Integrable (fun y => y ^ 2 * ‖u y‖ ^ 2)) :
    (∫ y, ‖differentialTransport g u du y‖ ^ 2) ≤
      (16 * (g 0 0) ^ 4) * (∫ y, ‖du y‖ ^ 2) +
      (16 * (g 1 0) ^ 4) * (∫ y, y ^ 4 * ‖du y‖ ^ 2) +
      (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∫ y, ‖u y‖ ^ 2) +
      (4 * (g 1 0) ^ 4) * (∫ y, y ^ 2 * ‖u y‖ ^ 2) := by
  have h1 := hd.const_mul (16 * (g 0 0) ^ 4)
  have h2 := hyd.const_mul (16 * (g 1 0) ^ 4)
  have h3 := hu.const_mul (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2)
  have h4 := hyu.const_mul (4 * (g 1 0) ^ 4)
  calc
    _ ≤ ∫ y, (16 * (g 0 0) ^ 4) * ‖du y‖ ^ 2 +
        (16 * (g 1 0) ^ 4) * (y ^ 4 * ‖du y‖ ^ 2) +
        (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * ‖u y‖ ^ 2 +
        (4 * (g 1 0) ^ 4) * (y ^ 2 * ‖u y‖ ^ 2) :=
      integral_mono hT (((h1.add h2).add h3).add h4) (differentialTransport_norm_sq_le g u du)
    _ = _ := by
      rw [integral_add (f := fun y => (16 * (g 0 0) ^ 4) * ‖du y‖ ^ 2 +
          (16 * (g 1 0) ^ 4) * (y ^ 4 * ‖du y‖ ^ 2) +
          (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * ‖u y‖ ^ 2)
          (g := fun y => (4 * (g 1 0) ^ 4) * (y ^ 2 * ‖u y‖ ^ 2))
          ((h1.add h2).add h3) h4,
        integral_add (f := fun y => (16 * (g 0 0) ^ 4) * ‖du y‖ ^ 2 +
          (16 * (g 1 0) ^ 4) * (y ^ 4 * ‖du y‖ ^ 2))
          (g := fun y => (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * ‖u y‖ ^ 2)
          (h1.add h2) h3,
        integral_add h1 h2]
      simp only [integral_const_mul]

end TransposeFollowup.RealMobius
