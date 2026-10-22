import TransposeFollowup.MobiusSmoothedDensity

/-! Uniform density bounds persist under further left convolution by a
probability measure, with the original one-sided smoothing unchanged. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem leftConvolutionDensity_mconv (μ ν : Measure H) [SFinite ν]
    {p : H → ℝ≥0∞} (hp : Measurable p) (x : H) :
    leftConvolutionDensity (μ ∗ₘ ν) p x =
      leftConvolutionDensity μ (leftConvolutionDensity ν p) x := by
  change (∫⁻ z, p (z⁻¹ * x) ∂μ ∗ₘ ν) = ∫⁻ a, ∫⁻ b, p (b⁻¹ * (a⁻¹ * x)) ∂ν ∂μ
  rw [Measure.lintegral_mconv (by fun_prop)]
  simp only [mul_inv_rev, mul_assoc]

theorem leftConvolutionDensity_mconv_le (μ ν : Measure H) [IsProbabilityMeasure μ] [SFinite ν]
    {p : H → ℝ≥0∞} (hp : Measurable p) {C : ℝ≥0∞}
    (hC : ∀ x, leftConvolutionDensity ν p x ≤ C) (x : H) :
    leftConvolutionDensity (μ ∗ₘ ν) p x ≤ C := by
  rw [leftConvolutionDensity_mconv μ ν hp]
  exact leftConvolutionDensity_le μ hC x

end TransposeFollowup

namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mobiusSmoothedDensity_mconv_le (μ ν : Measure Group) [IsProbabilityMeasure μ] [SFinite ν]
    {η : ℝ} {C : ℝ≥0∞} (hC : ∀ x, mobiusSmoothedDensity ν η x ≤ C) (x : Group) :
    mobiusSmoothedDensity (μ ∗ₘ ν) η x ≤ C :=
  leftConvolutionDensity_mconv_le μ ν (mobiusHaarKernelDensity_measurable η) hC x

theorem generatorWalk_smoothedDensity_le_of_le {m : ℕ} (G : Fin m → Group) (hm : 0 < m)
    {n ell : ℕ} (hnell : n ≤ ell) {η : ℝ} {C : ℝ≥0∞}
    (hC : ∀ x, mobiusSmoothedDensity (generatorWalkMeasure G n) η x ≤ C) (x : Group) :
    mobiusSmoothedDensity (generatorWalkMeasure G ell) η x ≤ C := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnell
  clear hnell
  have : IsProbabilityMeasure (symmetricGeneratorMeasure G) := symmetricGeneratorMeasure_probability G hm
  induction t generalizing x with
  | zero => simpa only [Nat.add_zero] using hC x
  | succ t ih =>
    have : IsProbabilityMeasure (generatorWalkMeasure G (n + t)) := generatorWalkMeasure_probability G hm _
    change mobiusSmoothedDensity (symmetricGeneratorMeasure G ∗ₘ generatorWalkMeasure G (n + t)) η x ≤ C
    exact mobiusSmoothedDensity_mconv_le _ _ ih x

end TransposeFollowup.RealMobius
