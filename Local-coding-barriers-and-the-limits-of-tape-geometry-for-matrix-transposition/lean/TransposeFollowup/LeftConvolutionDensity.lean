import Mathlib.MeasureTheory.Measure.WithDensity

/-! Right convolution by a density over a left-invariant base measure.
The first measure need not have a density; in particular it may be atomic. -/
namespace TransposeFollowup
open Classical MeasureTheory MeasureTheory.Measure
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

noncomputable def leftConvolutionDensity (μ : Measure H) (p : H → ℝ≥0∞) (g : H) : ℝ≥0∞ :=
  ∫⁻ h, p (h⁻¹ * g) ∂μ

theorem leftConvolutionDensity_measurable (μ : Measure H) [SFinite μ]
    {p : H → ℝ≥0∞} (hp : Measurable p) : Measurable (leftConvolutionDensity μ p) := by
  unfold leftConvolutionDensity
  exact Measurable.lintegral_prod_right (by fun_prop)

theorem mconv_withDensity_right (μ σ : Measure H) [SFinite μ] [SFinite σ]
    [IsMulLeftInvariant σ] {p : H → ℝ≥0∞} (hp : Measurable p) :
    μ ∗ₘ σ.withDensity p = σ.withDensity (leftConvolutionDensity μ p) := by
  refine ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_mconv hφ,
    lintegral_withDensity_eq_lintegral_mul σ (leftConvolutionDensity_measurable μ hp) hφ]
  calc
    _ = ∫⁻ h, ∫⁻ x, p x * φ (h * x) ∂σ ∂μ := by
      apply lintegral_congr
      intro h
      exact lintegral_withDensity_eq_lintegral_mul σ hp (by fun_prop)
    _ = ∫⁻ h, ∫⁻ x, p (h⁻¹ * x) * φ x ∂σ ∂μ := by
      apply lintegral_congr
      intro h
      simpa only [mul_inv_cancel_left] using
        (lintegral_mul_left_eq_self (μ := σ) (fun x => p x * φ (h * x)) h⁻¹).symm
    _ = ∫⁻ x, ∫⁻ h, p (h⁻¹ * x) * φ x ∂μ ∂σ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro x
      exact lintegral_mul_const (φ x) (by fun_prop)

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem leftConvolutionDensity_le (μ : Measure H) [IsProbabilityMeasure μ]
    {p : H → ℝ≥0∞} {C : ℝ≥0∞} (hp : ∀ h, p h ≤ C) (g : H) :
    leftConvolutionDensity μ p g ≤ C := by
  calc
    _ ≤ ∫⁻ _h, C ∂μ := lintegral_mono (fun h => hp (h⁻¹ * g))
    _ = C := by simp

end TransposeFollowup
