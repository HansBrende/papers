import TransposeFollowup.AutocorrelationIterates
import TransposeFollowup.AutocorrelationPowerAction
import TransposeFollowup.AutocorrelationCoefficient

/-! Support and coefficient bounds for all genuine dyadic autocorrelation
powers, linked to the action of the original one-sided smoothed measure. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem measureConvolutionPower_ae_entryBox (μ : Measure Group) [IsProbabilityMeasure μ]
    {B : ℝ} (hs : ∀ᵐ g ∂μ, g ∈ matrixEntryBox B) (n : ℕ) :
    ∀ᵐ g ∂measureConvolutionPower μ n, g ∈ matrixEntryBox ((2 * B) ^ n) := by
  induction n with
  | zero =>
    simp only [measureConvolutionPower, pow_zero]
    exact (ae_dirac_iff (matrixEntryBox_isCompact 1).isClosed.measurableSet).mpr one_mem_matrixEntryBox
  | succ n ih =>
    have : IsProbabilityMeasure (measureConvolutionPower μ n) := measureConvolutionPower_probability μ n
    simpa only [measureConvolutionPower, pow_succ'] using mconv_ae_matrixEntryBox μ _ hs ih

theorem smoothedAutocorrelationIterate_ae_zero_outside (μ : Measure Group) [IsProbabilityMeasure μ]
    {η B : ℝ} (hη : 0 < η) (hs : ∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B) (k : ℕ) :
    ∀ᵐ g ∂(Measure.haar : Measure Group),
      g ∉ matrixEntryBox ((4 * B ^ 2) ^ (2 ^ k)) → smoothedAutocorrelationIterate μ η k g = 0 := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  have hp := measureConvolutionPower_ae_entryBox _
    (autocorrelation_ae_matrixEntryBox (μ ∗ₘ mobiusHaarKernel η) hs) (2 ^ k)
  rw [← smoothedAutocorrelationIterate_withDensity μ hη,
    ae_withDensity_iff (smoothedAutocorrelationIterate_measurable μ η k),
    show 2 * (2 * B ^ 2) = 4 * B ^ 2 by ring] at hp
  exact hp.mono (fun _ hg hnot => by
    by_contra hn
    exact hnot (hg hn))

theorem smoothedAction_norm_power_le_of_autocorrelationIterate
    (μ : Measure Group) [IsProbabilityMeasure μ] {η B D M : ℝ}
    (hη : 0 < η) (hD : 0 ≤ D) (hM : 0 < M)
    (hs : ∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B) (k : ℕ)
    (hb : ∀ᵐ g ∂(Measure.haar : Measure Group), smoothedAutocorrelationIterate μ η k g ≤ ENNReal.ofReal D)
    (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖groupActionAverage (μ ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ (4 * 2 ^ k) ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        (4 * B ^ 2) ^ (2 * 2 ^ k) * D * M⁻¹ := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hl := autocorrelation_dyadic_power_norm_lower (μ ∗ₘ mobiusHaarKernel η) _ hu k
  have hp := pow_le_pow_left₀ (by positivity) hl 2
  have he := groupActionAverage_withDensity_norm_sq_le
    (smoothedAutocorrelationIterate_measurable μ η k) (smoothedAutocorrelationIterate_lintegral μ hη k)
    u ((4 * B ^ 2) ^ (2 ^ k)) hD hM hb
    (smoothedAutocorrelationIterate_ae_zero_outside μ hη hs k) hzero
  rw [smoothedAutocorrelationIterate_withDensity μ hη, hu, one_pow, mul_one] at he
  calc
    _ = (‖groupActionAverage (μ ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ (2 * 2 ^ k)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ _ := hp.trans he
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm (2 ^ k) 2]

theorem smoothedWalk_norm_power_le_of_autocorrelationIterate {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A η D M : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (hη : 0 < η) (hηone : η ≤ 1)
    (n k : ℕ) (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1) (hD : 0 ≤ D) (hM : 0 < M)
    (hb : ∀ᵐ g ∂(Measure.haar : Measure Group),
      smoothedAutocorrelationIterate (generatorWalkMeasure G n) η k g ≤ ENNReal.ofReal D)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖groupActionAverage (generatorWalkMeasure G n ∗ₘ mobiusHaarKernel η) (u.toLp 2 volume)‖ ^ (4 * 2 ^ k) ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        (64 * (2 * A) ^ (2 * n)) ^ (2 * 2 ^ k) * D * M⁻¹ := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
  have he : 4 * (4 * (2 * A) ^ n) ^ 2 = 64 * (2 * A) ^ (2 * n) := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
    ring
  simpa only [he] using smoothedAction_norm_power_le_of_autocorrelationIterate
    (generatorWalkMeasure G n) hη hD hM
    (generatorWalk_smoothed_ae_entryBox G hc hG hη hηone n) k hb u hu hzero

end TransposeFollowup.RealMobius
