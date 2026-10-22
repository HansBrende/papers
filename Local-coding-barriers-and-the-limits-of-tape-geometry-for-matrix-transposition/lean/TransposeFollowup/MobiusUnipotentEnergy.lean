import TransposeFollowup.ComplexMobiusComposition
import TransposeFollowup.MobiusUnipotentMatrices
import TransposeFollowup.TranslationDerivativeEnergy
import TransposeFollowup.SchwartzDyadicRegularity

/-! Quantitative upper and lower unipotent action bounds in actual L2.
Conjugation by inversion handles the lower flow across its moving pole. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

theorem complexPullbackL2_upper_energy_le (f : ComplexL2) {u du : ℝ → ℂ}
    (hfu : ⇑f =ᵐ[volume] u) (hu : ∀ x, HasDerivAt u (du x) x)
    (hdu : Continuous du) (he : Integrable (fun x => ‖du x‖ ^ 2)) (t : ℝ) :
    ‖complexPullbackL2 (upperUnipotent t) f - f‖ ^ 2 ≤ t ^ 2 * ∫ x, ‖du x‖ ^ 2 := by
  have hs := (complexPullbackL2_coe (upperUnipotent t) f).trans
    (scaledPullback_ae_congr (upperUnipotent t) hfu)
  rw [complexL2_norm_sq]
  calc
    _ = ∫ x, ‖u (x + t) - u x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (complexPullbackL2 (upperUnipotent t) f) f, hs, hfu]
        with x hx ht hf
      rw [scaledPullback_upperUnipotent] at ht
      rw [hx, Pi.sub_apply, ht, hf]
    _ ≤ _ := translation_difference_integral_energy_le hu hdu he t

theorem schwartz_upperUnipotent_energy_le (u : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖complexPullbackL2 (upperUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ^ 2 ≤
      t ^ 2 * ∫ x, ‖deriv u x‖ ^ 2 :=
  complexPullbackL2_upper_energy_le _ (u.coeFn_toLp 2 volume) u.hasDerivAt
    (SchwartzMap.derivCLM ℝ ℂ u).continuous
    (schwartz_integrable_norm_sq (SchwartzMap.derivCLM ℝ ℂ u)) t

theorem schwartz_upperUnipotent_regularity_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (upperUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ^ 2 ≤
      t ^ 2 * ((2 : ℝ) ^ j) ^ 2 * R := by
  have hd := (schwartzDyadicRegularityCost_deriv_energy_le j u).trans
    (mul_le_mul_of_nonneg_left hR (sq_nonneg _))
  have he : (∫ x, ‖deriv u x‖ ^ 2) ≤ ((2 : ℝ) ^ j) ^ 2 * R := by
    have hfour : 0 ≤ ∫ x, x ^ 4 * ‖deriv u x‖ ^ 2 := integral_nonneg (fun x => by positivity)
    linarith
  exact (schwartz_upperUnipotent_energy_le u t).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (sq_nonneg t))

theorem schwartz_transformed_upperUnipotent_energy_le (g : Group) (u : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ‖complexPullbackL2 (upperUnipotent t) (schwartzActionL2 g u) - schwartzActionL2 g u‖ ^ 2 ≤
      t ^ 2 * ∫ x, ‖deriv (scaledPullback g u) x‖ ^ 2 := by
  have hc : Continuous (deriv (scaledPullback g u)) := by
    rw [schwartz_scaledPullback_deriv]
    exact (schwartz_scaledPullback_differentiable g (schwartzDifferentialTransport g u)).continuous
  exact complexPullbackL2_upper_energy_le _ (schwartzActionL2_coe g u)
    (fun x => (schwartz_scaledPullback_differentiable g u x).hasDerivAt) hc
    (schwartz_scaledPullback_deriv_integrable_norm_sq g u) t

theorem complexPullbackL2_lower_difference (f : ComplexL2) (t : ℝ) :
    ‖complexPullbackL2 (lowerUnipotent t) f - f‖ =
      ‖complexPullbackL2 (upperUnipotent (-t)) (complexPullbackL2 inversionMatrix f) -
        complexPullbackL2 inversionMatrix f‖ := by
  have hs : complexPullbackL2 inversionMatrix⁻¹ (complexPullbackL2 inversionMatrix f) = f := by
    rw [← complexPullbackL2_mul, mul_inv_cancel, complexPullbackL2_one]
  rw [lowerUnipotent_eq_conjugate, complexPullbackL2_mul, complexPullbackL2_mul]
  conv_lhs => arg 1; arg 2; rw [← hs]
  exact complexPullbackL2_norm_sub _ _ _

theorem schwartz_lowerUnipotent_regularity_le (j : ℕ) (u : 𝓢(ℝ, ℂ)) {R : ℝ}
    (hR : schwartzDyadicRegularityCost j u ≤ R) (t : ℝ) :
    ‖complexPullbackL2 (lowerUnipotent t) (u.toLp 2 volume) - u.toLp 2 volume‖ ^ 2 ≤
      20 * t ^ 2 * ((2 : ℝ) ^ j) ^ 2 * R := by
  have hr : 0 ≤ R := (schwartzDyadicRegularityCost_nonneg j u).trans hR
  have hp : 1 ≤ ((2 : ℝ) ^ j) ^ 2 := by
    exact one_le_pow₀ (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hd := (schwartzDyadicRegularityCost_deriv_energy_le j u).trans
    (mul_le_mul_of_nonneg_left hR (sq_nonneg _))
  have hm := (schwartzDyadicRegularityCost_components_le j u).2.1.trans hR
  have hb := schwartz_scaledPullback_deriv_energy_le inversionMatrix u
  have h0 : inversionMatrix 0 0 = 0 := rfl
  have h1 : inversionMatrix 1 0 = 1 := rfl
  simp only [h0, h1, zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 2 ≠ 0),
    one_pow, mul_zero, zero_mul, zero_add, mul_one, add_zero] at hb
  have he : (∫ x, ‖deriv (scaledPullback inversionMatrix u) x‖ ^ 2) ≤
      20 * ((2 : ℝ) ^ j) ^ 2 * R := by
    have he0 : 0 ≤ ∫ x, ‖deriv u x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hrp := mul_le_mul_of_nonneg_right hp hr
    nlinarith
  rw [complexPullbackL2_lower_difference, complexPullbackL2_schwartz]
  have h := schwartz_transformed_upperUnipotent_energy_le inversionMatrix u (-t)
  rw [neg_sq] at h
  exact h.trans (by convert mul_le_mul_of_nonneg_left he (sq_nonneg t) using 1; ring)

end TransposeFollowup.RealMobius
