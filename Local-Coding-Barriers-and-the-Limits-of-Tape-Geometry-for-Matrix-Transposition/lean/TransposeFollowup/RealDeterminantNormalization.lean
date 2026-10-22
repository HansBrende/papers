import TransposeFollowup.ScalarCentralizerProjection

/-! Restore determinant one by a positive scalar, with explicit entry
error. Scalar normalization preserves a common commuting algebra. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem real_matrix_det_error {x y : RMat} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i j, |x i j| ≤ B) (he : ∀ i j, |x i j - y i j| ≤ δ) :
    |y.det - x.det| ≤ 4 * B * δ + 2 * δ ^ 2 := by
  have hy (i j : Fin 2) : |y i j| ≤ B + δ := by
    have hh := abs_add_le (y i j - x i j) (x i j)
    rw [sub_add_cancel, abs_sub_comm] at hh
    linarith [hx i j, he i j]
  have hp (i j k l : Fin 2) : |y i j * y k l - x i j * x k l| ≤ 2 * B * δ + δ ^ 2 := by
    rw [show y i j * y k l - x i j * x k l =
      (y i j - x i j) * y k l + x i j * (y k l - x k l) by ring]
    calc
      _ ≤ |(y i j - x i j) * y k l| + |x i j * (y k l - x k l)| := abs_add_le _ _
      _ = |x i j - y i j| * |y k l| + |x i j| * |x k l - y k l| := by
        rw [abs_mul, abs_mul, abs_sub_comm (y i j), abs_sub_comm (y k l)]
      _ ≤ δ * (B + δ) + B * δ := add_le_add
        (mul_le_mul (he i j) (hy k l) (abs_nonneg _) hδ)
        (mul_le_mul (hx i j) (he k l) (abs_nonneg _) hB)
      _ = _ := by ring
  have hh := norm_sub_le (y 0 0 * y 1 1 - x 0 0 * x 1 1)
    (y 0 1 * y 1 0 - x 0 1 * x 1 0)
  simp only [Real.norm_eq_abs] at hh
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  have heq : y 0 0 * y 1 1 - y 0 1 * y 1 0 - (x 0 0 * x 1 1 - x 0 1 * x 1 0) =
      (y 0 0 * y 1 1 - x 0 0 * x 1 1) - (y 0 1 * y 1 0 - x 0 1 * x 1 0) := by ring
  rw [heq]
  linarith [hp 0 0 1 1, hp 0 1 1 0]

theorem inverse_sqrt_near_one {D : ℝ} (hD : 1 / 2 ≤ D) :
    0 < (Real.sqrt D)⁻¹ ∧ (Real.sqrt D)⁻¹ ≤ 2 ∧
      |(Real.sqrt D)⁻¹ - 1| ≤ 2 * |D - 1| := by
  have hD0 : 0 < D := by linarith
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD0
  have hsquare := Real.sq_sqrt hD0.le
  have hslo : 1 / 2 ≤ Real.sqrt D := by nlinarith
  have hi : (Real.sqrt D)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hs]
    linarith
  have he : |Real.sqrt D - 1| ≤ |D - 1| := by
    calc
      _ ≤ |Real.sqrt D - 1| * |Real.sqrt D + 1| :=
        le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
      _ = _ := by
        rw [← abs_mul]
        congr 1
        nlinarith only [hsquare]
  refine ⟨inv_pos.mpr hs, hi, ?_⟩
  calc
    _ = |Real.sqrt D - 1| / Real.sqrt D := by
      rw [abs_sub_comm (Real.sqrt D)⁻¹ 1,
        show 1 - (Real.sqrt D)⁻¹ = (Real.sqrt D - 1) / Real.sqrt D by field_simp,
        abs_div, abs_of_pos hs]
    _ ≤ |D - 1| / Real.sqrt D := div_le_div_of_nonneg_right he hs.le
    _ ≤ 2 * |D - 1| := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

theorem exists_sl2_scalar_normalization (x : G) (y : RMat) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hsmall : 12 * B * δ ≤ 1)
    (hx : ∀ i j, |x i j| ≤ B) (he : ∀ i j, |x i j - y i j| ≤ δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 2 ∧ (r • y).det = 1 ∧
      ∀ i j, |x i j - (r • y) i j| ≤ 25 * B ^ 2 * δ := by
  have hB0 : 0 ≤ B := by linarith
  have hδ1 : δ ≤ 1 := by nlinarith
  have heD : |y.det - 1| ≤ 6 * B * δ := by
    have hh := real_matrix_det_error hB0 hδ hx he
    rw [x.property] at hh
    have hsq : δ ^ 2 ≤ B * δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hB)]
    linarith
  have hD : 1 / 2 ≤ y.det := by
    have hh := (abs_le.mp heD).1
    linarith
  obtain ⟨hr, hr2, hrerr⟩ := inverse_sqrt_near_one hD
  let r := (Real.sqrt y.det)⁻¹
  have hdet : (r • y).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin]
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt (by linarith : 0 ≤ y.det), inv_mul_cancel₀ (by linarith)]
  have hrerr' : |r - 1| ≤ 12 * B * δ := by linarith
  have hy (i j : Fin 2) : |y i j| ≤ 2 * B := by
    have hh := abs_add_le (y i j - x i j) (x i j)
    rw [sub_add_cancel, abs_sub_comm] at hh
    linarith [hx i j, he i j]
  refine ⟨r, hr, hr2, hdet, ?_⟩
  intro i j
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  calc
    _ = |(x i j - y i j) + (1 - r) * y i j| := by
      congr 1
      change x i j - r * y i j = _
      ring
    _ ≤ |x i j - y i j| + |(1 - r) * y i j| := abs_add_le _ _
    _ = |x i j - y i j| + |r - 1| * |y i j| := by rw [abs_mul, abs_sub_comm 1 r]
    _ ≤ δ + (12 * B * δ) * (2 * B) := add_le_add (he i j)
      (mul_le_mul hrerr' (hy i j) (abs_nonneg _) (by positivity))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hB2 hδ]

end TransposeFollowup.SL2Projection
