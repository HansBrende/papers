import TransposeFollowup.UnitSupportedFourierDerivatives
import TransposeFollowup.SchwartzSpatialMoments
import TransposeFollowup.SchwartzFourierDerivativeTest

/-! Exact Plancherel conversion between polynomial spatial moments and
frequency derivatives. No spatial support hypothesis is needed here. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
set_option autoImplicit false

theorem schwartz_polynomial_moment_integrable (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • u x) := by
  simpa only [SchwartzMap.smulLeftCLM_apply (g := fun x : ℝ => x ^ n) (by fun_prop)]
    using (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x ^ n) u).integrable

theorem schwartz_fourier_moment_energy (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ ξ, ‖iteratedDeriv n (⇑(𝓕 u : 𝓢(ℝ, ℂ))) ξ‖ ^ 2) =
      (2 * Real.pi) ^ (2 * n) * ∫ x, x ^ (2 * n) * ‖u x‖ ^ 2 := by
  let m : 𝓢(ℝ, ℂ) := (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
    SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x ^ n) u
  have hm : ⇑m = fourierSpatialMoment u n := by
    funext x
    change (-2 * (Real.pi : ℂ) * Complex.I) ^ n •
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x ^ n) u) x = _
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), fourierSpatialMoment_factor]
  have hd : iteratedDeriv n (⇑(𝓕 u : 𝓢(ℝ, ℂ))) = ⇑(𝓕 m : 𝓢(ℝ, ℂ)) := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hm]
    exact Real.iteratedDeriv_fourier (N := ⊤)
      (fun k _ => schwartz_polynomial_moment_integrable u k) (n := n) (by simp)
  rw [hd, SchwartzMap.integral_norm_sq_fourier]
  calc
    _ = ∫ x, (2 * Real.pi) ^ (2 * n) * (x ^ (2 * n) * ‖u x‖ ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show m x = fourierSpatialMoment u n x from congrFun hm x,
        fourierSpatialMoment_norm, norm_smul, Real.norm_eq_abs]
      simp only [mul_pow, sq_abs, ← pow_mul, Nat.mul_comm n 2]
    _ = _ := integral_const_mul _ _

theorem schwartz_spatial_moment_energy (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    (∫ x, x ^ (2 * n) * ‖u x‖ ^ 2) =
      ((2 * Real.pi) ^ (2 * n))⁻¹ *
        ∫ ξ, ‖iteratedDeriv n (⇑(𝓕 u : 𝓢(ℝ, ℂ))) ξ‖ ^ 2 := by
  rw [schwartz_fourier_moment_energy]
  have ht : (2 * Real.pi) ^ (2 * n) ≠ 0 := by positivity
  field_simp

theorem schwartz_first_spatial_moment_energy (u : 𝓢(ℝ, ℂ)) :
    (∫ x, x ^ 2 * ‖u x‖ ^ 2) = ((2 * Real.pi) ^ 2)⁻¹ *
      ∫ ξ, ‖deriv (⇑(𝓕 u : 𝓢(ℝ, ℂ))) ξ‖ ^ 2 := by
  simpa only [Nat.mul_one, iteratedDeriv_one] using schwartz_spatial_moment_energy u 1

theorem schwartz_second_spatial_moment_energy (u : 𝓢(ℝ, ℂ)) :
    (∫ x, x ^ 4 * ‖u x‖ ^ 2) = ((2 * Real.pi) ^ 4)⁻¹ *
      ∫ ξ, ‖iteratedDeriv 2 (⇑(𝓕 u : 𝓢(ℝ, ℂ))) ξ‖ ^ 2 := by
  simpa only [show 2 * 2 = 4 from rfl] using schwartz_spatial_moment_energy u 2

theorem schwartz_fourier_deriv (u : 𝓢(ℝ, ℂ)) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ u) = schwartzFrequencyDerivative (𝓕 u) := by
  ext ξ
  have hd : ⇑(SchwartzMap.derivCLM ℂ ℂ u) = deriv u := rfl
  rw [SchwartzMap.fourier_coe, hd, Real.fourier_deriv u.integrable u.differentiable
    (SchwartzMap.derivCLM ℂ ℂ u).integrable, schwartzFrequencyDerivative_apply]
  rfl

theorem schwartz_toLp_norm_sq (u : 𝓢(ℝ, ℂ)) :
    ‖u.toLp 2 volume‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [complexL2_norm_sq]
  exact integral_congr_ae ((u.coeFn_toLp 2 volume).mono
    (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))

end TransposeFollowup
