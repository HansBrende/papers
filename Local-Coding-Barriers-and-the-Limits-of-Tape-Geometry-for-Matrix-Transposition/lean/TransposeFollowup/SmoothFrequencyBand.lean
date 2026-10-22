import TransposeFollowup.UnitSupportedFourierDerivatives

/-! Actual Schwartz frequency-band pieces of a unit-supported L2 input.
The construction uses a smooth compactly supported frequency cutoff and
agrees with multiplication of the actual L2 Fourier representative. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap FourierTransform
open scoped FourierTransform ContDiff
set_option autoImplicit false

noncomputable def smoothBandSpectrum {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) : 𝓢(ℝ, ℂ) :=
  (hc.mul_right (f' := 𝓕 f)).toSchwartzMap ((χ.smooth ⊤).mul (unit_supported_fourier_smooth hf hs))

theorem smoothBandSpectrum_apply {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (ξ : ℝ) :
    smoothBandSpectrum hf hs χ hc ξ = χ ξ * 𝓕 f ξ := rfl

noncomputable def smoothBand {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (smoothBandSpectrum hf hs χ hc)

theorem smoothBand_fourier {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    𝓕 (smoothBand hf hs χ hc) = smoothBandSpectrum hf hs χ hc := fourier_fourierInv_eq _

theorem smoothBand_toLp_fourier {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2) =
      (smoothBandSpectrum hf hs χ hc).toLp 2 volume := by
  rw [SchwartzMap.toLp_fourier_eq, smoothBand_fourier]

theorem smoothBand_toLp_fourier_coe {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    ⇑(𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2) =ᵐ[volume]
      (fun ξ => χ ξ * (𝓕 (hf.toLp f) : ComplexL2) ξ) := by
  rw [smoothBand_toLp_fourier]
  filter_upwards [(smoothBandSpectrum hf hs χ hc).coeFn_toLp 2 volume,
    toLp_fourier_coe_ae (integrable_of_unit_supported_L2 hf hs) hf] with ξ hb hfξ
  rw [hb, hfξ, smoothBandSpectrum_apply]

theorem smoothBand_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    ‖(smoothBand hf hs χ hc).toLp 2 volume‖ ^ 2 =
      ∫ ξ, ‖χ ξ‖ ^ 2 * ‖(𝓕 (hf.toLp f) : ComplexL2) ξ‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq ((smoothBand hf hs χ hc).toLp 2 volume), complexL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [smoothBand_toLp_fourier_coe hf hs χ hc] with ξ hξ
  rw [hξ, norm_mul, mul_pow]

theorem smoothBand_weighted_energy_integrable {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    Integrable (fun ξ => ‖χ ξ‖ ^ 2 * ‖(𝓕 (hf.toLp f) : ComplexL2) ξ‖ ^ 2) := by
  apply ((Lp.memLp (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2)).integrable_norm_pow
    (by decide : 2 ≠ 0)).congr
  filter_upwards [smoothBand_toLp_fourier_coe hf hs χ hc] with ξ hξ
  rw [hξ, norm_mul, mul_pow]

theorem smoothBand_fourier_zero_on {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (s : Set ℝ) (hz : ∀ ξ ∈ s, χ ξ = 0) :
    ∀ᵐ ξ ∂volume, ξ ∈ s → (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2) ξ = 0 := by
  filter_upwards [smoothBand_toLp_fourier_coe hf hs χ hc] with ξ hξ hmem
  rw [hξ, hz ξ hmem, zero_mul]

theorem smoothBand_norm_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) {M : ℝ} (hM : 0 ≤ M)
    (hχ : ∀ ξ, ‖χ ξ‖ ≤ M) :
    ‖(smoothBand hf hs χ hc).toLp 2 volume‖ ≤ M * ‖hf.toLp f‖ := by
  have h : ‖(𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2)‖ ≤
      ‖M • (𝓕 (hf.toLp f) : ComplexL2)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [smoothBand_toLp_fourier_coe hf hs χ hc,
      Lp.coeFn_smul M (𝓕 (hf.toLp f) : ComplexL2)] with ξ hb hm
    rw [hb, hm]
    change ‖χ ξ * (𝓕 (hf.toLp f) : ComplexL2) ξ‖ ≤ ‖M • (𝓕 (hf.toLp f) : ComplexL2) ξ‖
    rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (hχ ξ) (norm_nonneg _)
  simpa only [Lp.norm_fourier_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hM] using h

end TransposeFollowup
