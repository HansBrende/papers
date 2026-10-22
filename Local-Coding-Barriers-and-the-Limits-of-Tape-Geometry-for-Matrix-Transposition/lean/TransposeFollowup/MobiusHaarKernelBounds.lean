import TransposeFollowup.MobiusSmallBallVolume
import TransposeFollowup.MobiusSmoothedDensity

/-! Exact squared L2 mass of the actual normalized Haar-ball kernel, and
its cubic bound. These provide the normalization input for flattening;
they do not give nontrivial flatness of a generator walk. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem haar_identityBall_inverse_le {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ ≤
      ENNReal.ofReal (512 /
        ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * η ^ 3)) := by
  have hc : (0 : ℝ) < (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) := by
    exact_mod_cast haar_column_factor_pos
  have hlo : ENNReal.ofReal
      ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * η ^ 3 / 512) ≤
        (Measure.haar : Measure Group) (mobiusIdentityBall η) := by
    calc
      _ = (Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ≥0∞) *
          ENNReal.ofReal (η ^ 3 / 512) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        congr 1
        ring
      _ ≤ _ := haar_identityBall_lower hη hηhalf
  have hi := ENNReal.inv_le_inv' hlo
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)] at hi
  convert hi using 1
  congr 1
  field_simp

theorem mobiusHaarKernelDensity_lt_top {η : ℝ} (hη : 0 < η) (g : Group) :
    mobiusHaarKernelDensity η g < ∞ :=
  (mobiusHaarKernelDensity_le η g).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (mobiusIdentityBall_haar_pos hη).ne'))

theorem mobiusHaarKernelDensity_lintegral_sq {η : ℝ} (hη : 0 < η) :
    (∫⁻ g, (mobiusHaarKernelDensity η g) ^ 2 ∂(Measure.haar : Measure Group)) =
      ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ := by
  have he : (fun g => (mobiusHaarKernelDensity η g) ^ 2) =
      (mobiusIdentityBall η).indicator (fun _ =>
        (((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹) ^ 2) := by
    funext g
    by_cases hg : g ∈ mobiusIdentityBall η <;> simp [mobiusHaarKernelDensity, hg]
  rw [he, lintegral_indicator (mobiusIdentityBall_isOpen η).measurableSet,
    lintegral_const, Measure.restrict_apply_univ, pow_two, mul_assoc,
    ENNReal.inv_mul_cancel (mobiusIdentityBall_haar_pos hη).ne'
      (mobiusIdentityBall_haar_lt_top hη).ne, mul_one]

theorem mobiusHaarKernelDensity_lintegral_ofReal_sq {η : ℝ} (hη : 0 < η) :
    (∫⁻ g, ENNReal.ofReal ((mobiusHaarKernelDensity η g).toReal ^ 2)
      ∂(Measure.haar : Measure Group)) =
        ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ := by
  calc
    _ = ∫⁻ g, (mobiusHaarKernelDensity η g) ^ 2 ∂(Measure.haar : Measure Group) := by
      apply lintegral_congr
      intro g
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (mobiusHaarKernelDensity_lt_top hη g).ne]
    _ = _ := mobiusHaarKernelDensity_lintegral_sq hη

theorem mobiusHaarKernelDensity_integrable_sq {η : ℝ} (hη : 0 < η) :
    Integrable (fun g => (mobiusHaarKernelDensity η g).toReal ^ 2) (Measure.haar : Measure Group) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((mobiusHaarKernelDensity_measurable η).ennreal_toReal.pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun _ => sq_nonneg _))).mp
  rw [mobiusHaarKernelDensity_lintegral_ofReal_sq hη]
  exact ENNReal.inv_ne_top.mpr (mobiusIdentityBall_haar_pos hη).ne'

theorem mobiusHaarKernelDensity_memLp_two {η : ℝ} (hη : 0 < η) :
    MemLp (fun g => (mobiusHaarKernelDensity η g).toReal) 2 (Measure.haar : Measure Group) :=
  (memLp_two_iff_integrable_sq
    (mobiusHaarKernelDensity_measurable η).ennreal_toReal.aestronglyMeasurable).mpr
      (mobiusHaarKernelDensity_integrable_sq hη)

theorem mobiusHaarKernelDensity_integral_sq {η : ℝ} (hη : 0 < η) :
    (∫ g, (mobiusHaarKernelDensity η g).toReal ^ 2 ∂(Measure.haar : Measure Group)) =
      (((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => sq_nonneg _))
    ((mobiusHaarKernelDensity_measurable η).ennreal_toReal.pow_const 2).aestronglyMeasurable,
    mobiusHaarKernelDensity_lintegral_ofReal_sq hη]

theorem mobiusHaarKernelDensity_integral_sq_le {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (∫ g, (mobiusHaarKernelDensity η g).toReal ^ 2 ∂(Measure.haar : Measure Group)) ≤
      512 / ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * η ^ 3) := by
  rw [mobiusHaarKernelDensity_integral_sq hη]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (haar_identityBall_inverse_le hη hηhalf)
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤
    512 / ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * η ^ 3))] at hb
  exact hb

theorem mobiusSmoothedDensity_cubic_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) (g : Group) :
    mobiusSmoothedDensity μ η g ≤ ENNReal.ofReal
      (512 / ((Measure.haarScalarFactor Measure.haar columnChartMeasure : ℝ) * η ^ 3)) :=
  (mobiusSmoothedDensity_le μ η g).trans (haar_identityBall_inverse_le hη hηhalf)

end TransposeFollowup.RealMobius
