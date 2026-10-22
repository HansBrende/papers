import TransposeFollowup.MobiusPolarCoefficient
import TransposeFollowup.MobiusHaarEntryBox
import TransposeFollowup.MobiusGroupSmoothing

/-! A bounded-entry Haar coefficient estimate for the actual SL2 action.
The polar weight comparison is proved from the entry bounds; the energy
estimate is inherited from the proved affine wavelet inequality. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

theorem polarColumn_measurable : Measurable (fun p : ℝ × ℝ => polarColumn p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> dsimp [polarColumn] <;> fun_prop

variable [MeasurableSpace Group] [BorelSpace Group]

omit [MeasurableSpace Group] [BorelSpace Group] in
theorem polar_box_weight_le (f : Group → ℝ≥0∞) (B : ℝ)
    {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    ENNReal.ofReal a * ∫⁻ b : ℝ,
        (matrixEntryBox B).indicator f (columnChart (polarColumn a θ, b)) ≤
      ENNReal.ofReal (B ^ 2) * (ENNReal.ofReal (2 / a) *
        ∫⁻ b : ℝ, f (columnChart (polarColumn a θ, b))) := by
  rw [← mul_assoc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro b
  dsimp only
  by_cases hg : columnChart (polarColumn a θ, b) ∈ matrixEntryBox B
  · rw [indicator_of_mem hg]
    have hq := (matrixEntryBox_column_bounds hg).1
    rw [columnChart, dite_eq_left (polarColumn_ne_zero ha θ), firstColumn_columnMatrix,
      columnSqNorm_polarColumn] at hq
    have hw : a ≤ B ^ 2 * (2 / a) := by
      calc
        a ≤ (2 * B ^ 2) / a := (le_div_iff₀ ha).mpr (by nlinarith only [hq])
        _ = _ := by ring
    have he : ENNReal.ofReal a ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (2 / a) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg B)]
      exact ENNReal.ofReal_le_ofReal hw
    exact mul_le_mul' he le_rfl
  · simp only [indicator_of_notMem hg, mul_zero, zero_le]

theorem haar_entryBox_lintegral_le {f : Group → ℝ≥0∞} (hf : Measurable f)
    (B : ℝ) (K : ℝ≥0∞)
    (henergy : ∀ θ : ℝ, (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 / a) *
      ∫⁻ b : ℝ, f (columnChart (polarColumn a θ, b))) ≤ K) :
    (∫⁻ g in matrixEntryBox B, f g ∂(Measure.haar : Measure Group)) ≤
      (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
        (ENNReal.ofReal (2 * Real.pi * B ^ 2) * K) := by
  have hs := (matrixEntryBox_isCompact B).isClosed.measurableSet
  rw [← lintegral_indicator hs f, haar_lintegral_polar (hf.indicator hs)]
  have hm : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      f (columnChart (polarColumn z.1.1 z.1.2, z.2))) :=
    hf.comp (columnChart_measurable.comp
      ((polarColumn_measurable.comp measurable_fst).prodMk measurable_snd))
  have hk : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (2 / p.1) *
      ∫⁻ b : ℝ, f (columnChart (polarColumn p.1 p.2, b))) :=
    (measurable_const.div measurable_fst).ennreal_ofReal.mul hm.lintegral_prod_right'
  gcongr
  calc
    _ ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal (B ^ 2) *
        (ENNReal.ofReal (2 / p.1) * ∫⁻ b : ℝ, f (columnChart (polarColumn p.1 p.2, b))) := by
      apply setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact polar_box_weight_le f B hp.1 p.2
    _ = ENNReal.ofReal (B ^ 2) * ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 / a) *
          ∫⁻ b : ℝ, f (columnChart (polarColumn a θ, b)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact setLIntegral_prod_symm _ hk.aemeasurable
    _ ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ _θ in Ioo (-Real.pi) Real.pi, K := by
      gcongr with θ
      exact henergy θ
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
        show Real.pi - -Real.pi = 2 * Real.pi by ring]
      calc
        _ = (ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (2 * Real.pi)) * K := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (sq_nonneg B)]
          congr 2
          ring

omit [MeasurableSpace Group] [BorelSpace Group] in
theorem group_coefficient_energy_continuous (u v : ComplexL2) :
    Continuous (fun g : Group => ‖inner ℂ v (complexPullbackL2 g⁻¹ u)‖ ^ 2) :=
  (continuous_const.inner (complexPullbackL2_inverse_continuous u)).norm.pow 2

theorem group_coefficient_box_lintegral_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    (B : ℝ) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ g in matrixEntryBox B, ENNReal.ofReal
      (‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2)
        ∂(Measure.haar : Measure Group)) ≤
      ENNReal.ofReal (2 * Real.pi *
        (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * B ^ 2 *
          M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) := by
  have hb := haar_entryBox_lintegral_le
    (group_coefficient_energy_continuous (u.toLp 2 volume) v).measurable.ennreal_ofReal B
    (ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2))
    (fun θ => polar_group_coefficient_energy_le u v θ hM hzero)
  calc
    _ ≤ _ := hb
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
      congr 1
      ring

theorem group_coefficient_box_energy_integrable (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    (B : ℝ) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    Integrable (fun g : Group => ‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2)
      ((Measure.haar : Measure Group).restrict (matrixEntryBox B)) := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (group_coefficient_energy_continuous (u.toLp 2 volume) v).aestronglyMeasurable
    (ae_of_all _ (fun _ => sq_nonneg _))).mp
    (ne_of_lt ((group_coefficient_box_lintegral_le u v B hM hzero).trans_lt ENNReal.ofReal_lt_top))

theorem group_coefficient_box_energy_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    (B : ℝ) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ g in matrixEntryBox B, ‖inner ℂ v (complexPullbackL2 g⁻¹ (u.toLp 2 volume))‖ ^ 2
      ∂(Measure.haar : Measure Group)) ≤
      2 * Real.pi * (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * B ^ 2 *
        M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2 := by
  have hb := group_coefficient_box_lintegral_le u v B hM hzero
  rw [← ofReal_integral_eq_lintegral_ofReal
    (group_coefficient_box_energy_integrable u v B hM hzero)
    (ae_of_all _ (fun _ => sq_nonneg _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

end TransposeFollowup.RealMobius
