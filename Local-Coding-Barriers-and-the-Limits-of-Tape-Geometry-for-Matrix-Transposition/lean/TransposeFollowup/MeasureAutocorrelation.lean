import TransposeFollowup.LeftConvolutionDensity
import Mathlib.MeasureTheory.Group.LIntegral

/-! Inversion reverses convolution. Autocorrelation supplies an actually
inversion-symmetric measure; its density is symmetric for a bi-invariant
base measure, with its value at identity equal to the squared L2 mass. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

omit [MeasurableMul₂ H] in
theorem lintegral_inv_measure (μ : Measure H) (f : H → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ.inv = ∫⁻ x, f x⁻¹ ∂μ :=
  lintegral_map_equiv f (MeasurableEquiv.inv H)

theorem inv_mconv (μ ν : Measure H) [SFinite μ] [SFinite ν] :
    (μ ∗ₘ ν).inv = ν.inv ∗ₘ μ.inv := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_inv_measure, Measure.lintegral_mconv (by fun_prop),
    Measure.lintegral_mconv hf, lintegral_inv_measure]
  simp_rw [lintegral_inv_measure, mul_inv_rev]
  exact lintegral_lintegral_swap (by fun_prop)

theorem inv_autocorrelation (μ : Measure H) [SFinite μ] :
    (μ.inv ∗ₘ μ).inv = μ.inv ∗ₘ μ := by
  rw [inv_mconv, Measure.inv_inv]

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem inv_measure_probability (μ : Measure H) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure μ.inv := by
  change IsProbabilityMeasure (Measure.map Inv.inv μ)
  infer_instance

noncomputable def autocorrelationDensity (σ : Measure H) (f : H → ℝ≥0∞) : H → ℝ≥0∞ :=
  leftConvolutionDensity (σ.withDensity f).inv f

theorem autocorrelationDensity_eq_integral (σ : Measure H) {f : H → ℝ≥0∞}
    (hf : Measurable f) (x : H) :
    autocorrelationDensity σ f x = ∫⁻ y, f y * f (y * x) ∂σ := by
  unfold autocorrelationDensity leftConvolutionDensity
  rw [lintegral_inv_measure]
  simp only [inv_inv]
  exact lintegral_withDensity_eq_lintegral_mul σ hf (by fun_prop)

theorem autocorrelationDensity_one (σ : Measure H) {f : H → ℝ≥0∞} (hf : Measurable f) :
    autocorrelationDensity σ f 1 = ∫⁻ y, f y ^ 2 ∂σ := by
  rw [autocorrelationDensity_eq_integral σ hf]
  simp only [mul_one, pow_two]

theorem autocorrelationDensity_inv (σ : Measure H) [Measure.IsMulRightInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (x : H) :
    autocorrelationDensity σ f x⁻¹ = autocorrelationDensity σ f x := by
  rw [autocorrelationDensity_eq_integral σ hf, autocorrelationDensity_eq_integral σ hf]
  calc
    _ = ∫⁻ y, f (y * x) * f (y * x * x⁻¹) ∂σ :=
      (lintegral_mul_right_eq_self (μ := σ) (fun y => f y * f (y * x⁻¹)) x).symm
    _ = _ := by simp only [mul_inv_cancel_right, mul_comm]

theorem autocorrelationDensity_withDensity (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {f : H → ℝ≥0∞} (hf : Measurable f) :
    (σ.withDensity f).inv ∗ₘ σ.withDensity f = σ.withDensity (autocorrelationDensity σ f) := by
  exact mconv_withDensity_right _ σ hf

omit [MeasurableMul₂ H] in
theorem inv_withDensity (σ : Measure H) [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) :
    (σ.withDensity f).inv = σ.withDensity (fun x => f x⁻¹) := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_inv_measure, lintegral_withDensity_eq_lintegral_mul σ hf (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul σ (by fun_prop) hφ]
  simpa only [inv_inv, Pi.mul_apply] using
    (lintegral_inv_eq_self (μ := σ) (fun y => f y * φ y⁻¹)).symm

end TransposeFollowup
