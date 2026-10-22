import TransposeFollowup.AutocorrelationAction
import TransposeFollowup.ProbabilityConvolutionPowers

/-! Actual convolution powers act by operator iteration. Dyadic powers of
an autocorrelation retain the original action with an explicit exponent. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def groupActionAverageCLM (μ : Measure Group) [IsFiniteMeasure μ] : ComplexL2 →L[ℝ] ComplexL2 :=
  ({ toFun := groupActionAverage μ
     map_add' := fun f h => by
       unfold groupActionAverage
       simp only [map_add]
       exact integral_add (integrable_complexPullbackL2_inverse μ f) (integrable_complexPullbackL2_inverse μ h)
     map_smul' := fun c f => by
       unfold groupActionAverage
       simp only [map_smul, integral_smul, RingHom.id_apply] } : ComplexL2 →ₗ[ℝ] ComplexL2).mkContinuous
    (μ.real univ) (groupActionAverage_norm_le_measure μ)

theorem groupActionAverageCLM_apply (μ : Measure Group) [IsFiniteMeasure μ] (f : ComplexL2) :
    groupActionAverageCLM μ f = groupActionAverage μ f := rfl

theorem groupActionAverage_convolutionPower (μ : Measure Group) [IsProbabilityMeasure μ]
    (n : ℕ) (f : ComplexL2) :
    groupActionAverage (measureConvolutionPower μ n) f = (groupActionAverage μ)^[n] f := by
  induction n with
  | zero => simp [measureConvolutionPower, groupActionAverage_dirac, complexPullbackL2_one]
  | succ n ih =>
    have : IsProbabilityMeasure (measureConvolutionPower μ n) := measureConvolutionPower_probability μ n
    rw [measureConvolutionPower, groupActionAverage_mconv, ih, Function.iterate_succ_apply']

theorem autocorrelation_dyadic_power_norm_lower (μ : Measure Group) [IsProbabilityMeasure μ]
    (f : ComplexL2) (hf : ‖f‖ = 1) (k : ℕ) :
    ‖groupActionAverage μ f‖ ^ (2 * 2 ^ k) ≤
      ‖groupActionAverage (measureConvolutionPower (μ.inv ∗ₘ μ) (2 ^ k)) f‖ := by
  have : IsProbabilityMeasure μ.inv := inv_measure_probability μ
  have h := symmetric_dyadic_iterate_norm_lower (groupActionAverageCLM (μ.inv ∗ₘ μ))
    (groupActionAverage_autocorrelation_symmetric μ) f hf (sq_nonneg _)
    (groupActionAverage_autocorrelation_norm_lower μ f hf) k
  change (‖groupActionAverage μ f‖ ^ 2) ^ (2 ^ k) ≤
    ‖(groupActionAverage (μ.inv ∗ₘ μ))^[2 ^ k] f‖ at h
  rw [← groupActionAverage_convolutionPower] at h
  simpa only [← pow_mul] using h

end TransposeFollowup.RealMobius
