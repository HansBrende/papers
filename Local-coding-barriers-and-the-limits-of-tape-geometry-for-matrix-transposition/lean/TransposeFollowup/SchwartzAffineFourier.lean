import TransposeFollowup.SchwartzFourierMoments
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact Fourier formulas for positive rescaling and translation, and
translation Plancherel for the correlation of two actual Schwartz inputs. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem positive_rescaling_growth_bound {c : ℝ} (hc : 0 < c) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖c * x‖) ^ k := by
  refine ⟨1, c⁻¹, ?_⟩
  intro x
  rw [pow_one, norm_mul, Real.norm_eq_abs c, abs_of_pos hc, mul_add,
    mul_one, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  linarith

noncomputable def schwartzRescale (u : 𝓢(ℝ, ℂ)) (c : ℝ) (hc : 0 < c) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => c * x) (by fun_prop)
    (positive_rescaling_growth_bound hc) u

theorem schwartzRescale_apply (u : 𝓢(ℝ, ℂ)) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    schwartzRescale u c hc x = u (c * x) := rfl

theorem fourier_schwartzRescale (u : 𝓢(ℝ, ℂ)) (c : ℝ) (hc : 0 < c) (ξ : ℝ) :
    (𝓕 (schwartzRescale u c hc) : 𝓢(ℝ, ℂ)) ξ = c⁻¹ • (𝓕 u : 𝓢(ℝ, ℂ)) (c⁻¹ * ξ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  change (∫ x : ℝ, Real.fourierChar (-(x * ξ)) • u (c * x)) = _
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-((c * x) * (c⁻¹ * ξ))) • u (c * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have he : (c * x) * (c⁻¹ * ξ) = x * ξ := by field_simp
      rw [he]
    _ = |c⁻¹| • ∫ y : ℝ, Real.fourierChar (-(y * (c⁻¹ * ξ))) • u y :=
      Measure.integral_comp_mul_left (fun y : ℝ => Real.fourierChar (-(y * (c⁻¹ * ξ))) • u y) c
    _ = _ := by rw [abs_of_pos (inv_pos.mpr hc), SchwartzMap.fourier_coe, Real.fourier_real_eq]

theorem fourier_schwartzTranslate (u : 𝓢(ℝ, ℂ)) (t ξ : ℝ) :
    (𝓕 (u.compSubConstCLM ℂ t) : 𝓢(ℝ, ℂ)) ξ =
      Real.fourierChar (-(t * ξ)) • (𝓕 u : 𝓢(ℝ, ℂ)) ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℝ) (⇑u) (-t)) ξ
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
    Function.comp_def, SchwartzMap.compSubConstCLM_apply, sub_eq_add_neg,
    innerₗ_apply_apply, RCLike.inner_apply, mul_comm] using h

noncomputable def schwartzCorrelationSpectrum (u v : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    ((𝓕 v : 𝓢(ℝ, ℂ)).postcompCLM Complex.conjCLE.toContinuousLinearMap) (𝓕 u)

theorem schwartzCorrelationSpectrum_apply (u v : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    schwartzCorrelationSpectrum u v ξ =
      star ((𝓕 v : 𝓢(ℝ, ℂ)) ξ) * (𝓕 u : 𝓢(ℝ, ℂ)) ξ := rfl

theorem schwartz_translation_correlation_fourier (u v : 𝓢(ℝ, ℂ)) (t : ℝ) :
    inner ℂ (v.toLp 2 volume) ((u.compSubConstCLM ℂ t).toLp 2 volume) =
      (𝓕 (schwartzCorrelationSpectrum u v) : 𝓢(ℝ, ℂ)) t := by
  rw [SchwartzMap.inner_toL2_toL2_eq v (u.compSubConstCLM ℂ t) volume,
    ← SchwartzMap.integral_inner_fourier_fourier v (u.compSubConstCLM ℂ t),
    SchwartzMap.fourier_coe (schwartzCorrelationSpectrum u v), Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [fourier_schwartzTranslate, schwartzCorrelationSpectrum_apply]
  simp only [RCLike.inner_apply', Circle.smul_def, smul_eq_mul, starRingEnd_apply]
  rw [mul_comm ξ t]
  ring

theorem schwartz_translation_correlation_energy (u v : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, ‖inner ℂ (v.toLp 2 volume) ((u.compSubConstCLM ℂ t).toLp 2 volume)‖ ^ 2) =
      ∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 * ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 := by
  simp_rw [schwartz_translation_correlation_fourier]
  rw [SchwartzMap.integral_norm_sq_fourier]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [schwartzCorrelationSpectrum_apply, norm_mul, norm_star, mul_pow, mul_comm]

theorem schwartz_translation_correlation_integrable (u v : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ =>
      ‖inner ℂ (v.toLp 2 volume) ((u.compSubConstCLM ℂ t).toLp 2 volume)‖ ^ 2) := by
  simp_rw [schwartz_translation_correlation_fourier]
  exact schwartz_integrable_norm_sq _

end TransposeFollowup
