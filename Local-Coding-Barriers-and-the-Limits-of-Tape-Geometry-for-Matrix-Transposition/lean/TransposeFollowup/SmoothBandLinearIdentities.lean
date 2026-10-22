import TransposeFollowup.SmoothFrequencyBand

/-! Linear identities for the actual Schwartz bands and their L2 classes. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap FourierTransform
open scoped FourierTransform
set_option autoImplicit false

theorem smoothBand_congr {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ ψ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (hp : HasCompactSupport (⇑ψ))
    (he : χ = ψ) : smoothBand hf hs χ hc = smoothBand hf hs ψ hp := by
  subst ψ
  rfl

theorem smoothBandSpectrum_sub {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ ψ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (hp : HasCompactSupport (⇑ψ)) :
    smoothBandSpectrum hf hs (χ - ψ) (hc.sub hp) =
      smoothBandSpectrum hf hs χ hc - smoothBandSpectrum hf hs ψ hp := by
  ext ξ
  change (χ ξ - ψ ξ) * 𝓕 f ξ = χ ξ * 𝓕 f ξ - ψ ξ * 𝓕 f ξ
  ring

theorem smoothBand_sub {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ ψ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (hp : HasCompactSupport (⇑ψ)) :
    smoothBand hf hs (χ - ψ) (hc.sub hp) =
      smoothBand hf hs χ hc - smoothBand hf hs ψ hp := by
  unfold smoothBand
  rw [smoothBandSpectrum_sub, sub_eq_add_neg, fourierInv_add, fourierInv_neg, ← sub_eq_add_neg]

theorem smoothBand_sub_input_fourier_coe {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    ⇑(𝓕 ((smoothBand hf hs χ hc).toLp 2 volume - hf.toLp f) : ComplexL2) =ᵐ[volume]
      (fun ξ => (χ ξ - 1) * (𝓕 (hf.toLp f) : ComplexL2) ξ) := by
  have he : (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume - hf.toLp f) : ComplexL2) =
      𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) - 𝓕 (hf.toLp f) := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (_ - _) = _
    exact map_sub _ _ _
  rw [he]
  filter_upwards [Lp.coeFn_sub (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2)
    (𝓕 (hf.toLp f)), smoothBand_toLp_fourier_coe hf hs χ hc] with ξ hsub hχ
  rw [hsub]
  change (𝓕 ((smoothBand hf hs χ hc).toLp 2 volume) : ComplexL2) ξ - (𝓕 (hf.toLp f)) ξ = _
  rw [hχ]
  ring

theorem smoothBand_sub_input_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    ‖(smoothBand hf hs χ hc).toLp 2 volume - hf.toLp f‖ ^ 2 =
      ∫ ξ, ‖(χ ξ - 1) * (𝓕 (hf.toLp f) : ComplexL2) ξ‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq ((smoothBand hf hs χ hc).toLp 2 volume - hf.toLp f), complexL2_norm_sq]
  exact integral_congr_ae ((smoothBand_sub_input_fourier_coe hf hs χ hc).mono
    (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))

end TransposeFollowup
