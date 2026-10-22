import TransposeFollowup.MobiusDifferentialTransport

/-! A cubic decay hypothesis makes the weighted pullback vanish quadratically
near a pole. This is a spatial estimate, independent of Fourier localization. -/
namespace TransposeFollowup.RealMobius
open Classical
set_option autoImplicit false

theorem num_ne_zero_at_pole (g : Group) {p : ℝ} (hp : denom g p = 0) : num g p ≠ 0 := by
  have hcross : g 0 0 * denom g p - g 1 0 * num g p = 1 := by
    dsimp [denom, num]
    nlinarith only [determinant g]
  intro hn
  rw [hp, hn] at hcross
  norm_num at hcross

theorem denom_eq_mul_sub_at_pole (g : Group) {p : ℝ} (hp : denom g p = 0) (x : ℝ) :
    denom g x = g 1 0 * (x - p) := by
  dsimp [denom] at hp ⊢
  nlinarith only [hp]

theorem scaledPullback_at_pole {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u : ℝ → E) {p : ℝ} (hp : denom g p = 0) : scaledPullback g u p = 0 := by
  simp only [scaledPullback, hp, abs_zero, inv_zero, zero_smul]

theorem scaledPullback_norm_le_of_cubic_decay {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Group) (u : ℝ → E) {B η : ℝ} (hη : 0 < η)
    (hu : ∀ y : ℝ, |y| ^ 3 * ‖u y‖ ≤ B) {x : ℝ} (hx : η ≤ |num g x|) :
    ‖scaledPullback g u x‖ ≤ B / η ^ 3 * |denom g x| ^ 2 := by
  by_cases hd : denom g x = 0
  · simp only [scaledPullback_at_pole g u hd, hd, norm_zero, abs_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, le_refl]
  have hD : 0 < |denom g x| := abs_pos.mpr hd
  have h := hu (eval g x)
  rw [eval, abs_div, div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hD 3)] at h
  have hsmall : η ^ 3 * ‖u (eval g x)‖ ≤ B * |denom g x| ^ 3 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hη.le hx 3) (norm_nonneg _)).trans h
  calc
    _ = ‖u (eval g x)‖ / |denom g x| := by
      simp only [scaledPullback, norm_smul, Real.norm_eq_abs, abs_inv, abs_abs]
      ring
    _ ≤ (B * |denom g x| ^ 3 / η ^ 3) / |denom g x| :=
      div_le_div_of_nonneg_right ((le_div_iff₀ (pow_pos hη 3)).mpr (by nlinarith only [hsmall])) hD.le
    _ = _ := by field_simp

end TransposeFollowup.RealMobius
