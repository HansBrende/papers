import TransposeFollowup.GeneratorWalkSymmetry
import TransposeFollowup.SmoothedDensityPropagation
import TransposeFollowup.RationalWalkInitialL2

/-! A symmetric density attached to the actual one-sided smoothed walk.
It is its autocorrelation, not an assertion that the original density is
symmetric. All convolution identities retain their noncommutative order. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

noncomputable def mobiusSmoothedAutocorrelation (μ : Measure Group) (η : ℝ) : Group → ℝ≥0∞ :=
  autocorrelationDensity Measure.haar (mobiusSmoothedDensity μ η)

theorem mobiusSmoothedAutocorrelation_eq_density (μ : Measure Group) [SFinite μ] (η : ℝ) :
    mobiusSmoothedAutocorrelation μ η =
      mobiusSmoothedDensity ((μ ∗ₘ mobiusHaarKernel η).inv ∗ₘ μ) η := by
  funext x
  unfold mobiusSmoothedAutocorrelation autocorrelationDensity
  rw [← mconv_mobiusHaarKernel_eq_withDensity]
  exact (leftConvolutionDensity_mconv _ μ (mobiusHaarKernelDensity_measurable η) x).symm

theorem mobiusSmoothedAutocorrelation_measurable (μ : Measure Group) [SFinite μ] (η : ℝ) :
    Measurable (mobiusSmoothedAutocorrelation μ η) := by
  exact leftConvolutionDensity_measurable _ (mobiusSmoothedDensity_measurable μ η)

theorem mobiusSmoothedAutocorrelation_inv (μ : Measure Group) [SFinite μ] (η : ℝ) (x : Group) :
    mobiusSmoothedAutocorrelation μ η x⁻¹ = mobiusSmoothedAutocorrelation μ η x :=
  autocorrelationDensity_inv Measure.haar (mobiusSmoothedDensity_measurable μ η) x

theorem mobiusSmoothedAutocorrelation_level_inv (μ : Measure Group) [SFinite μ] (η : ℝ)
    (a b : ℝ≥0∞) :
    {x | a ≤ mobiusSmoothedAutocorrelation μ η x ∧ mobiusSmoothedAutocorrelation μ η x < b}⁻¹ =
      {x | a ≤ mobiusSmoothedAutocorrelation μ η x ∧ mobiusSmoothedAutocorrelation μ η x < b} := by
  ext x
  simp only [Set.mem_inv, Set.mem_ofPred_eq, mobiusSmoothedAutocorrelation_inv]

theorem mobiusSmoothedAutocorrelation_one (μ : Measure Group) [SFinite μ] (η : ℝ) :
    mobiusSmoothedAutocorrelation μ η 1 =
      ∫⁻ x, (mobiusSmoothedDensity μ η x) ^ 2 ∂(Measure.haar : Measure Group) :=
  autocorrelationDensity_one Measure.haar (mobiusSmoothedDensity_measurable μ η)

theorem mobiusSmoothedAutocorrelation_withDensity (μ : Measure Group) [SFinite μ] (η : ℝ) :
    (μ ∗ₘ mobiusHaarKernel η).inv ∗ₘ (μ ∗ₘ mobiusHaarKernel η) =
      (Measure.haar : Measure Group).withDensity (mobiusSmoothedAutocorrelation μ η) := by
  rw [mconv_mobiusHaarKernel_eq_withDensity]
  exact autocorrelationDensity_withDensity Measure.haar (mobiusSmoothedDensity_measurable μ η)

theorem mobiusSmoothedAutocorrelation_lintegral (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) :
    ∫⁻ x, mobiusSmoothedAutocorrelation μ η x ∂(Measure.haar : Measure Group) = 1 := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  rw [mobiusSmoothedAutocorrelation_eq_density]
  exact mobiusSmoothedDensity_lintegral _ hη

theorem mobiusSmoothedAutocorrelation_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) {C : ℝ≥0∞} (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ C) (x : Group) :
    mobiusSmoothedAutocorrelation μ η x ≤ C := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  change leftConvolutionDensity ((Measure.haar : Measure Group).withDensity
    (mobiusSmoothedDensity μ η)).inv (mobiusSmoothedDensity μ η) x ≤ C
  rw [← mconv_mobiusHaarKernel_eq_withDensity]
  exact leftConvolutionDensity_le _ hC x

theorem mobiusSmoothedAutocorrelation_integrable_sq_and_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hbound : ∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C) :
    Integrable (fun x => (mobiusSmoothedAutocorrelation μ η x).toReal ^ 2)
      (Measure.haar : Measure Group) ∧
    (∫ x, (mobiusSmoothedAutocorrelation μ η x).toReal ^ 2 ∂(Measure.haar : Measure Group)) ≤ C := by
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have : IsProbabilityMeasure (μ ∗ₘ mobiusHaarKernel η).inv := inv_measure_probability _
  have hb := mobiusSmoothedAutocorrelation_le μ hη hbound
  rw [mobiusSmoothedAutocorrelation_eq_density] at hb ⊢
  exact mobiusSmoothedDensity_integrable_sq_and_le _ hη hC hb

theorem generatorWalk_autocorrelation_eq_sandwichDensity {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    (n : ℕ) {η : ℝ} (hη : 0 < η) :
    mobiusSmoothedAutocorrelation (generatorWalkMeasure G n) η =
      mobiusSmoothedDensity (mobiusHaarKernel η ∗ₘ generatorWalkMeasure G (2 * n)) η := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hm n
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  rw [mobiusSmoothedAutocorrelation_eq_density, inv_mconv, mobiusHaarKernel_inv,
    generatorWalkMeasure_inv G hm, Measure.mconv_assoc,
    ← generatorWalkMeasure_add G hm, ← two_mul]

end TransposeFollowup.RealMobius
