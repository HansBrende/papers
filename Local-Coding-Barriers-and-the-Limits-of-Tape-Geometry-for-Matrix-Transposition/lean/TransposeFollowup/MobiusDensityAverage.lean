import TransposeFollowup.MobiusProbabilityCoefficient

/-! A bounded probability density supported in a matrix entry box gives a
quantitative high-frequency upper bound for the actual SL2 average. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem haar_withDensity_probability {κ : Group → ℝ≥0∞}
    (hmass : ∫⁻ g, κ g ∂(Measure.haar : Measure Group) = 1) :
    IsProbabilityMeasure ((Measure.haar : Measure Group).withDensity κ) := by
  constructor
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass

theorem density_coefficient_lintegral_le {κ : Group → ℝ≥0∞} (hκ : Measurable κ)
    (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) (B : ℝ) {D M : ℝ} (hD : 0 ≤ D) (hM : 0 < M)
    (hbound : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g ≤ ENNReal.ofReal D)
    (hsupport : ∀ᵐ g ∂(Measure.haar : Measure Group), g ∉ matrixEntryBox B → κ g = 0)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ g, ENNReal.ofReal (‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2)
      ∂(Measure.haar : Measure Group).withDensity κ) ≤
      ENNReal.ofReal (2 * Real.pi *
        (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * B ^ 2 * D *
          M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) := by
  let f : Group → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2)
  have hf : Measurable f :=
    (group_coefficient_energy_continuous (u.toLp 2 volume) v).measurable.ennreal_ofReal
  change (∫⁻ g, f g ∂(Measure.haar : Measure Group).withDensity κ) ≤ _
  rw [lintegral_withDensity_eq_lintegral_mul _ hκ hf]
  calc
    _ ≤ ∫⁻ g, ENNReal.ofReal D * (matrixEntryBox B).indicator f g
        ∂(Measure.haar : Measure Group) := by
      apply lintegral_mono_ae
      filter_upwards [hbound, hsupport] with g hg hs
      dsimp only [Pi.mul_apply]
      by_cases hmem : g ∈ matrixEntryBox B
      · rw [indicator_of_mem hmem]
        exact mul_le_mul' hg le_rfl
      · rw [indicator_of_notMem hmem, hs hmem, zero_mul, mul_zero]
    _ = ENNReal.ofReal D * ∫⁻ g in matrixEntryBox B, f g
        ∂(Measure.haar : Measure Group) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator (matrixEntryBox_isCompact B).isClosed.measurableSet]
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal (2 * Real.pi *
        (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * B ^ 2 *
          M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) :=
      mul_le_mul' le_rfl (group_coefficient_box_lintegral_le u v B hM hzero)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hD]
      congr 1
      ring

theorem density_coefficient_energy_le {κ : Group → ℝ≥0∞} (hκ : Measurable κ)
    (hmass : ∫⁻ g, κ g ∂(Measure.haar : Measure Group) = 1)
    (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) (B : ℝ) {D M : ℝ} (hD : 0 ≤ D) (hM : 0 < M)
    (hbound : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g ≤ ENNReal.ofReal D)
    (hsupport : ∀ᵐ g ∂(Measure.haar : Measure Group), g ∉ matrixEntryBox B → κ g = 0)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ g, ‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2
      ∂(Measure.haar : Measure Group).withDensity κ) ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        B ^ 2 * D * M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2 := by
  have : IsProbabilityMeasure ((Measure.haar : Measure Group).withDensity κ) :=
    haar_withDensity_probability hmass
  have hb := density_coefficient_lintegral_le hκ u v B hD hM hbound hsupport hzero
  rw [← ofReal_integral_eq_lintegral_ofReal
    (group_coefficient_energy_integrable _ (u.toLp 2 volume) v)
    (ae_of_all _ (fun _ => sq_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

theorem groupActionAverage_withDensity_norm_sq_le {κ : Group → ℝ≥0∞} (hκ : Measurable κ)
    (hmass : ∫⁻ g, κ g ∂(Measure.haar : Measure Group) = 1)
    (u : 𝓢(ℝ, ℂ)) (B : ℝ) {D M : ℝ} (hD : 0 ≤ D) (hM : 0 < M)
    (hbound : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g ≤ ENNReal.ofReal D)
    (hsupport : ∀ᵐ g ∂(Measure.haar : Measure Group), g ∉ matrixEntryBox B → κ g = 0)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖groupActionAverage ((Measure.haar : Measure Group).withDensity κ) (u.toLp 2 volume)‖ ^ 2 ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        B ^ 2 * D * M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 := by
  have : IsProbabilityMeasure ((Measure.haar : Measure Group).withDensity κ) :=
    haar_withDensity_probability hmass
  apply groupActionAverage_norm_sq_le_of_coefficient_energy _ _ (by positivity)
  intro v
  exact density_coefficient_energy_le hκ hmass u v B hD hM hbound hsupport hzero

theorem integrable_bounded_density_action {κ : Group → ℝ≥0∞} (hκ : Measurable κ)
    (hmass : ∫⁻ g, κ g ∂(Measure.haar : Measure Group) = 1) (u : ComplexL2)
    {D : ℝ} (hbound : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g ≤ ENNReal.ofReal D) :
    Integrable (fun g => (κ g).toReal • complexPullbackL2 g⁻¹ u) (Measure.haar : Measure Group) := by
  have : IsProbabilityMeasure ((Measure.haar : Measure Group).withDensity κ) :=
    haar_withDensity_probability hmass
  have ht : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g < ∞ :=
    hbound.mono (fun _ hg => hg.trans_lt ENNReal.ofReal_lt_top)
  exact (integrable_withDensity_iff_integrable_smul' hκ ht).mp
    (integrable_complexPullbackL2_inverse _ u)

theorem density_action_integral_norm_sq_le {κ : Group → ℝ≥0∞} (hκ : Measurable κ)
    (hmass : ∫⁻ g, κ g ∂(Measure.haar : Measure Group) = 1)
    (u : 𝓢(ℝ, ℂ)) (B : ℝ) {D M : ℝ} (hD : 0 ≤ D) (hM : 0 < M)
    (hbound : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g ≤ ENNReal.ofReal D)
    (hsupport : ∀ᵐ g ∂(Measure.haar : Measure Group), g ∉ matrixEntryBox B → κ g = 0)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    ‖∫ g, (κ g).toReal • complexPullbackL2 g⁻¹ (u.toLp 2 volume)
      ∂(Measure.haar : Measure Group)‖ ^ 2 ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) *
        B ^ 2 * D * M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 := by
  have ht : ∀ᵐ g ∂(Measure.haar : Measure Group), κ g < ∞ :=
    hbound.mono (fun _ hg => hg.trans_lt ENNReal.ofReal_lt_top)
  have hb := groupActionAverage_withDensity_norm_sq_le hκ hmass u B hD hM hbound hsupport hzero
  rw [groupActionAverage, integral_withDensity_eq_integral_toReal_smul hκ ht] at hb
  exact hb

end TransposeFollowup.RealMobius
