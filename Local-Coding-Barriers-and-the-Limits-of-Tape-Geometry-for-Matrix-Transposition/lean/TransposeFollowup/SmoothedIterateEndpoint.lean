import TransposeFollowup.AutocorrelationIterates

/-! Every actual autocorrelation iterate retains a rightmost copy of
the original smoothing kernel. No commutation of factors is used. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem smoothedAutocorrelationIterate_split_last (μ : Measure Group)
    [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) (k : ℕ) :
    let σ := μ ∗ₘ mobiusHaarKernel η
    let a := σ.inv ∗ₘ σ
    (Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k) =
      (measureConvolutionPower a (2 ^ k - 1) ∗ₘ σ.inv) ∗ₘ σ := by
  dsimp only
  let σ := μ ∗ₘ mobiusHaarKernel η
  let a := σ.inv ∗ₘ σ
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure σ.inv := inv_measure_probability σ
  have : IsProbabilityMeasure a := inferInstance
  have : IsProbabilityMeasure (measureConvolutionPower a (2 ^ k - 1)) :=
    measureConvolutionPower_probability _ _
  rw [smoothedAutocorrelationIterate_withDensity μ hη]
  change measureConvolutionPower a (2 ^ k) = (measureConvolutionPower a (2 ^ k - 1) ∗ₘ σ.inv) ∗ₘ σ
  have he : 2 ^ k = (2 ^ k - 1) + 1 := by have := Nat.two_pow_pos k; omega
  conv_lhs => rw [he, measureConvolutionPower_succ_right]
  exact (Measure.mconv_assoc _ _ _).symm

theorem smoothedAutocorrelationIterate_right_kernel (μ : Measure Group)
    [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) (k : ℕ) :
    ∃ ν : Measure Group, IsProbabilityMeasure ν ∧
      (Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k) =
        ν ∗ₘ mobiusHaarKernel η := by
  let σ := μ ∗ₘ mobiusHaarKernel η
  let α := σ.inv ∗ₘ σ
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure σ := inferInstance
  have : IsProbabilityMeasure σ.inv := inv_measure_probability σ
  have : IsProbabilityMeasure α := inferInstance
  let β := measureConvolutionPower α (2 ^ k - 1)
  have : IsProbabilityMeasure β := measureConvolutionPower_probability _ _
  refine ⟨(β ∗ₘ σ.inv) ∗ₘ μ, inferInstance, ?_⟩
  rw [smoothedAutocorrelationIterate_split_last μ hη]
  change (β ∗ₘ σ.inv) ∗ₘ (μ ∗ₘ mobiusHaarKernel η) = _
  exact (Measure.mconv_assoc _ _ _).symm

end TransposeFollowup.RealMobius
