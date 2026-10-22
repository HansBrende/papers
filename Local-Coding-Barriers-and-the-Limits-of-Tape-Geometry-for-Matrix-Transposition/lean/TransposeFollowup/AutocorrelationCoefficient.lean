import TransposeFollowup.AutocorrelationSupport
import TransposeFollowup.AutocorrelationAction
import TransposeFollowup.MobiusDensityAverage

/-! High-frequency coefficient control for the original smoothed action
using the density of its symmetric autocorrelation. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem smoothedAction_norm_four_le_of_autocorrelation (μ : Measure Group) [IsProbabilityMeasure μ]
    {η B D M : ℝ} (hη : 0 < η) (hD : 0 ≤ D) (hM : 0 < M)
    (hs : ∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B)
    (hb : ∀ᵐ g ∂(Measure.haar : Measure Group), mobiusSmoothedAutocorrelation μ η g ≤ ENNReal.ofReal D)
    (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖groupActionAverage (μ ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ 4 ≤
      8 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * B ^ 4 * D * M⁻¹ := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hl := groupActionAverage_autocorrelation_norm_lower (μ ∗ₘ mobiusHaarKernel η) _ hu
  have hp := pow_le_pow_left₀ (sq_nonneg _) hl 2
  have he := groupActionAverage_withDensity_norm_sq_le
    (mobiusSmoothedAutocorrelation_measurable μ η) (mobiusSmoothedAutocorrelation_lintegral μ hη)
    u (2 * B ^ 2) hD hM hb (smoothedAutocorrelation_ae_zero_outside μ η hs) hzero
  rw [← mobiusSmoothedAutocorrelation_withDensity, hu, one_pow, mul_one] at he
  calc
    _ = (‖groupActionAverage (μ ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ 2) ^ 2 := by ring
    _ ≤ _ := hp.trans he
    _ = _ := by ring

theorem smoothedWalk_norm_four_le_of_autocorrelation {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A η D M : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (hη : 0 < η) (hηone : η ≤ 1)
    (n : ℕ) (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1) (hD : 0 ≤ D) (hM : 0 < M)
    (hb : ∀ᵐ g ∂(Measure.haar : Measure Group),
      mobiusSmoothedAutocorrelation (generatorWalkMeasure G n) η g ≤ ENNReal.ofReal D)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖groupActionAverage (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ 4 ≤
      2048 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        (2 * A) ^ (4 * n) * D * M⁻¹ := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
  have h := smoothedAction_norm_four_le_of_autocorrelation (generatorWalkMeasure G n) hη hD hM
    (generatorWalk_smoothed_ae_entryBox G hc hG hη hηone n) hb u hu hzero
  calc
    _ ≤ _ := h
    _ = _ := by rw [show 4 * n = n * 4 by omega, pow_mul]; ring

end TransposeFollowup.RealMobius
