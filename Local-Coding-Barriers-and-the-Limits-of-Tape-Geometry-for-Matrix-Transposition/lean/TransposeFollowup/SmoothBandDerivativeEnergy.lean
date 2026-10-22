import TransposeFollowup.SmoothBandSpectrumDerivatives
import TransposeFollowup.MobiusTransportMoments

/-! First and second spectrum-derivative energies are bounded by products
of cutoff derivatives and input Fourier derivatives. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem schwartz_derivCLM_coe (φ : 𝓢(ℝ, ℂ)) :
    ⇑(SchwartzMap.derivCLM ℂ ℂ φ) = deriv φ := rfl

theorem norm_add_sq_le_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  simpa only [sub_neg_eq_add, norm_neg] using RealMobius.norm_sub_sq_le_twice a (-b)

theorem norm_add_three_sq_le_three {E : Type*} [NormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 + 3 * ‖b‖ ^ 2 + 3 * ‖c‖ ^ 2 := by
  have h := (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

theorem smoothBandSpectrum_deriv_energy_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    (∫ ξ, ‖deriv (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2) ≤
      2 * (∫ ξ, ‖χ ξ * deriv (𝓕 f) ξ‖ ^ 2) + 2 * (∫ ξ, ‖deriv χ ξ * 𝓕 f ξ‖ ^ 2) := by
  have hF0 : MemLp (𝓕 f) 2 volume := by
    simpa only [iteratedDeriv_zero] using unit_supported_fourier_derivative_memLp hf hs 0
  have hF1 : MemLp (deriv (𝓕 f)) 2 volume := by
    simpa only [iteratedDeriv_one] using unit_supported_fourier_derivative_memLp hf hs 1
  have hA := schwartz_multiplier_energy_integrable χ hF1
  have hB : Integrable (fun ξ => ‖deriv χ ξ * 𝓕 f ξ‖ ^ 2) :=
    schwartz_multiplier_energy_integrable (SchwartzMap.derivCLM ℂ ℂ χ) hF0
  have hL : Integrable (fun ξ => ‖deriv (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2) :=
    ((SchwartzMap.derivCLM ℂ ℂ (smoothBandSpectrum hf hs χ hc)).memLp 2 volume).integrable_norm_pow
      (by decide : 2 ≠ 0)
  calc
    _ ≤ ∫ ξ, 2 * ‖χ ξ * deriv (𝓕 f) ξ‖ ^ 2 + 2 * ‖deriv χ ξ * 𝓕 f ξ‖ ^ 2 := by
      apply integral_mono hL ((hA.const_mul 2).add (hB.const_mul 2))
      intro ξ
      change ‖deriv (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2 ≤
        2 * ‖χ ξ * deriv (𝓕 f) ξ‖ ^ 2 + 2 * ‖deriv χ ξ * 𝓕 f ξ‖ ^ 2
      rw [smoothBandSpectrum_deriv]
      exact norm_add_sq_le_two _ _
    _ = _ := by rw [integral_add (hA.const_mul 2) (hB.const_mul 2)]; simp only [integral_const_mul]

theorem smoothBandSpectrum_secondDeriv_energy_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    (∫ ξ, ‖iteratedDeriv 2 (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2) ≤
      3 * (∫ ξ, ‖χ ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2) +
      12 * (∫ ξ, ‖deriv χ ξ * deriv (𝓕 f) ξ‖ ^ 2) +
      3 * (∫ ξ, ‖iteratedDeriv 2 χ ξ * 𝓕 f ξ‖ ^ 2) := by
  have hF0 : MemLp (𝓕 f) 2 volume := by
    simpa only [iteratedDeriv_zero] using unit_supported_fourier_derivative_memLp hf hs 0
  have hF1 : MemLp (deriv (𝓕 f)) 2 volume := by
    simpa only [iteratedDeriv_one] using unit_supported_fourier_derivative_memLp hf hs 1
  have hF2 := unit_supported_fourier_derivative_memLp hf hs 2
  have hA := schwartz_multiplier_energy_integrable χ hF2
  have hB : Integrable (fun ξ => ‖deriv χ ξ * deriv (𝓕 f) ξ‖ ^ 2) :=
    schwartz_multiplier_energy_integrable (SchwartzMap.derivCLM ℂ ℂ χ) hF1
  have hC : Integrable (fun ξ => ‖iteratedDeriv 2 χ ξ * 𝓕 f ξ‖ ^ 2) := by
    simpa only [schwartz_derivCLM_coe, SchwartzMap.derivCLM_apply, iteratedDeriv_succ, iteratedDeriv_zero] using
      schwartz_multiplier_energy_integrable
        (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ χ)) hF0
  have hL : Integrable (fun ξ => ‖iteratedDeriv 2 (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2) := by
    simpa only [schwartz_derivCLM_coe, SchwartzMap.derivCLM_apply, iteratedDeriv_succ, iteratedDeriv_zero] using
      ((SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (smoothBandSpectrum hf hs χ hc))).memLp
        2 volume).integrable_norm_pow (by decide : 2 ≠ 0)
  calc
    _ ≤ ∫ ξ, 3 * ‖χ ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2 +
        12 * ‖deriv χ ξ * deriv (𝓕 f) ξ‖ ^ 2 + 3 * ‖iteratedDeriv 2 χ ξ * 𝓕 f ξ‖ ^ 2 := by
      apply integral_mono hL (((hA.const_mul 3).add (hB.const_mul 12)).add (hC.const_mul 3))
      intro ξ
      change ‖iteratedDeriv 2 (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2 ≤
        3 * ‖χ ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2 +
        12 * ‖deriv χ ξ * deriv (𝓕 f) ξ‖ ^ 2 + 3 * ‖iteratedDeriv 2 χ ξ * 𝓕 f ξ‖ ^ 2
      rw [smoothBandSpectrum_secondDeriv]
      have h := norm_add_three_sq_le_three (χ ξ * iteratedDeriv 2 (𝓕 f) ξ)
        (2 * (deriv χ ξ * deriv (𝓕 f) ξ)) (iteratedDeriv 2 χ ξ * 𝓕 f ξ)
      norm_num [← mul_assoc, norm_mul, mul_pow] at h ⊢
      exact h
    _ = _ := by
      rw [integral_add (f := fun ξ => 3 * ‖χ ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2 +
          12 * ‖deriv χ ξ * deriv (𝓕 f) ξ‖ ^ 2)
          ((hA.const_mul 3).add (hB.const_mul 12)) (hC.const_mul 3),
        integral_add (hA.const_mul 3) (hB.const_mul 12)]
      simp only [integral_const_mul]

end TransposeFollowup
