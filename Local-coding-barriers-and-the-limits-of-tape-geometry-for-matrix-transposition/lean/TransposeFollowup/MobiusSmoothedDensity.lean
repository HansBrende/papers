import TransposeFollowup.MobiusHaarKernel
import TransposeFollowup.LeftConvolutionDensity

/-! The actual Haar density of a right-smoothed probability measure, including
the atomic generator walk. The weighted L2-valued integral is integrable. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def mobiusHaarKernelDensity (η : ℝ) : Group → ℝ≥0∞ :=
  (mobiusIdentityBall η).indicator (fun _ =>
    ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹)

noncomputable def mobiusSmoothedDensity (μ : Measure Group) (η : ℝ) : Group → ℝ≥0∞ :=
  leftConvolutionDensity μ (mobiusHaarKernelDensity η)

theorem mobiusHaarKernelDensity_measurable (η : ℝ) : Measurable (mobiusHaarKernelDensity η) :=
  measurable_const.indicator (mobiusIdentityBall_isOpen η).measurableSet

theorem mobiusHaarKernelDensity_le (η : ℝ) (g : Group) :
    mobiusHaarKernelDensity η g ≤ ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ := by
  by_cases hg : g ∈ mobiusIdentityBall η <;> simp [mobiusHaarKernelDensity, hg]

theorem mobiusSmoothedDensity_measurable (μ : Measure Group) [SFinite μ] (η : ℝ) :
    Measurable (mobiusSmoothedDensity μ η) :=
  leftConvolutionDensity_measurable μ (mobiusHaarKernelDensity_measurable η)

theorem mobiusSmoothedDensity_le (μ : Measure Group) [IsProbabilityMeasure μ] (η : ℝ) (g : Group) :
    mobiusSmoothedDensity μ η g ≤ ((Measure.haar : Measure Group) (mobiusIdentityBall η))⁻¹ :=
  leftConvolutionDensity_le μ (mobiusHaarKernelDensity_le η) g

theorem mobiusSmoothedDensity_lt_top (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (g : Group) : mobiusSmoothedDensity μ η g < ∞ :=
  (mobiusSmoothedDensity_le μ η g).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (mobiusIdentityBall_haar_pos hη).ne'))

theorem mconv_mobiusHaarKernel_eq_withDensity (μ : Measure Group) [SFinite μ] (η : ℝ) :
    μ ∗ₘ mobiusHaarKernel η =
      (Measure.haar : Measure Group).withDensity (mobiusSmoothedDensity μ η) := by
  rw [mobiusHaarKernel_eq_withDensity]
  exact mconv_withDensity_right μ Measure.haar (mobiusHaarKernelDensity_measurable η)

theorem mobiusSmoothedDensity_lintegral (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ g, mobiusSmoothedDensity μ η g ∂(Measure.haar : Measure Group) = 1 := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure
      ((Measure.haar : Measure Group).withDensity (mobiusSmoothedDensity μ η)) := by
    rw [← mconv_mobiusHaarKernel_eq_withDensity]
    infer_instance
  have hm : ((Measure.haar : Measure Group).withDensity (mobiusSmoothedDensity μ η)) univ = 1 :=
    measure_univ
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm

theorem integrable_mobiusSmoothedDensity_action (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (f : ComplexL2) :
    Integrable (fun g => (mobiusSmoothedDensity μ η g).toReal • complexPullbackL2 g⁻¹ f)
      (Measure.haar : Measure Group) := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hi := integrable_complexPullbackL2_inverse (μ ∗ₘ mobiusHaarKernel η) f
  rw [mconv_mobiusHaarKernel_eq_withDensity] at hi
  exact (integrable_withDensity_iff_integrable_smul' (mobiusSmoothedDensity_measurable μ η)
    (Filter.Eventually.of_forall (mobiusSmoothedDensity_lt_top μ hη))).mp hi

theorem groupActionAverage_mobiusHaarKernel_eq_integral (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (f : ComplexL2) :
    groupActionAverage (μ ∗ₘ mobiusHaarKernel η) f =
      ∫ g, (mobiusSmoothedDensity μ η g).toReal • complexPullbackL2 g⁻¹ f
        ∂(Measure.haar : Measure Group) := by
  unfold groupActionAverage
  rw [mconv_mobiusHaarKernel_eq_withDensity]
  exact integral_withDensity_eq_integral_toReal_smul (mobiusSmoothedDensity_measurable μ η)
    (Filter.Eventually.of_forall (mobiusSmoothedDensity_lt_top μ hη)) _

theorem generatorWalk_haar_integral_dyadic_norm_lower {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    (j : ℕ) (u : 𝓢(ℝ, ℂ)) (hu : ‖u.toLp 2 volume‖ = 1) {R r η : ℝ}
    (hr : 0 ≤ r) (hlarge : r ≤ ‖complexAverage G (u.toLp 2 volume)‖)
    (hR : schwartzDyadicRegularityCost j u ≤ R) (hηpos : 0 < η) (hη : η ≤ 1 / 2)
    (m : ℕ) (he : 29 * (2 : ℝ) ^ j * Real.sqrt R * η ≤ r ^ (2 ^ m) / 2) :
    r ^ (2 ^ m) / 2 ≤
      ‖∫ g, (mobiusSmoothedDensity (generatorWalkMeasure G (2 ^ m)) η g).toReal •
        complexPullbackL2 g⁻¹ (u.toLp 2 volume) ∂(Measure.haar : Measure Group)‖ := by
  have : IsProbabilityMeasure (generatorWalkMeasure G (2 ^ m)) := generatorWalkMeasure_probability G hc _
  rw [← groupActionAverage_mobiusHaarKernel_eq_integral _ hηpos]
  exact generatorWalk_haar_smoothed_dyadic_norm_lower G hc j u hu hr hlarge hR hηpos hη m he

end TransposeFollowup.RealMobius
