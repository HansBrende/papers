import TransposeFollowup.SmoothedAutocorrelationEnergy
import TransposeFollowup.ProbabilityConvolutionPowers

/-! Canonical symmetric densities for all dyadic powers of the actual
smoothed-walk autocorrelation. Each step is a genuine autocorrelation. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def smoothedAutocorrelationIterate (μ : Measure Group) (η : ℝ) : ℕ → Group → ℝ≥0∞
  | 0 => mobiusSmoothedAutocorrelation μ η
  | k + 1 => autocorrelationDensity Measure.haar (smoothedAutocorrelationIterate μ η k)

theorem smoothedAutocorrelationIterate_measurable (μ : Measure Group) [SFinite μ] (η : ℝ) (k : ℕ) :
    Measurable (smoothedAutocorrelationIterate μ η k) := by
  induction k with
  | zero => exact mobiusSmoothedAutocorrelation_measurable μ η
  | succ k ih => exact leftConvolutionDensity_measurable _ ih

theorem smoothedAutocorrelationIterate_inv (μ : Measure Group) [SFinite μ] (η : ℝ) (k : ℕ) (x : Group) :
    smoothedAutocorrelationIterate μ η k x⁻¹ = smoothedAutocorrelationIterate μ η k x := by
  cases k with
  | zero => exact mobiusSmoothedAutocorrelation_inv μ η x
  | succ k => exact autocorrelationDensity_inv Measure.haar (smoothedAutocorrelationIterate_measurable μ η k) x

theorem smoothedAutocorrelationIterate_withDensity (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k) =
      measureConvolutionPower ((μ ∗ₘ mobiusHaarKernel η).inv ∗ₘ (μ ∗ₘ mobiusHaarKernel η)) (2 ^ k) := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  induction k with
  | zero =>
    simp only [pow_zero, measureConvolutionPower_one, smoothedAutocorrelationIterate]
    exact (mobiusSmoothedAutocorrelation_withDensity μ η).symm
  | succ k ih =>
    rw [smoothedAutocorrelationIterate,
      ← autocorrelationDensity_withDensity Measure.haar (smoothedAutocorrelationIterate_measurable μ η k),
      ih, measureConvolutionPower_inv _ (inv_autocorrelation _), ← measureConvolutionPower_add]
    congr 1
    rw [pow_succ, mul_two]

theorem smoothedAutocorrelationIterate_probability (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    IsProbabilityMeasure ((Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k)) := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  rw [smoothedAutocorrelationIterate_withDensity μ hη]
  exact measureConvolutionPower_probability _ _

theorem smoothedAutocorrelationIterate_lintegral (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) (k : ℕ) :
    ∫⁻ x, smoothedAutocorrelationIterate μ η k x ∂(Measure.haar : Measure Group) = 1 := by
  have := smoothedAutocorrelationIterate_probability μ hη k
  have hm := measure_univ (μ := (Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k))
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm

theorem smoothedAutocorrelationIterate_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) {C : ℝ≥0∞} (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ C)
    (k : ℕ) (x : Group) : smoothedAutocorrelationIterate μ η k x ≤ C := by
  induction k generalizing x with
  | zero => exact mobiusSmoothedAutocorrelation_le μ hη hC x
  | succ k ih =>
    have := smoothedAutocorrelationIterate_probability μ hη k
    have : IsProbabilityMeasure
        ((Measure.haar : Measure Group).withDensity (smoothedAutocorrelationIterate μ η k)).inv :=
      inv_measure_probability _
    exact leftConvolutionDensity_le _ ih x

theorem smoothedAutocorrelationIterate_energy (μ : Measure Group) [SFinite μ] (η : ℝ) (k : ℕ) :
    smoothedAutocorrelationIterate μ η (k + 1) 1 =
      ∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group) :=
  autocorrelationDensity_one Measure.haar (smoothedAutocorrelationIterate_measurable μ η k)

theorem smoothedAutocorrelationIterate_lintegral_sq_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) {C : ℝ≥0∞} (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ C) (k : ℕ) :
    (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group)) ≤ C := by
  rw [← smoothedAutocorrelationIterate_energy]
  exact smoothedAutocorrelationIterate_le μ hη hC (k + 1) 1

end TransposeFollowup.RealMobius
