import TransposeFollowup.MeasureAutocorrelation

/-! Genuine convolution powers of a probability measure, with exact
concatenation and inversion identities on a possibly noncommutative group. -/
namespace TransposeFollowup
open Classical MeasureTheory
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

noncomputable def measureConvolutionPower (μ : Measure H) : ℕ → Measure H
  | 0 => Measure.dirac 1
  | n + 1 => μ ∗ₘ measureConvolutionPower μ n

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem measureConvolutionPower_probability (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (measureConvolutionPower μ n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac (1 : H)); infer_instance
  | succ n ih =>
    have : IsProbabilityMeasure (measureConvolutionPower μ n) := ih
    change IsProbabilityMeasure (μ ∗ₘ measureConvolutionPower μ n)
    infer_instance

omit [MeasurableInv H] in
theorem measureConvolutionPower_one (μ : Measure H) [IsProbabilityMeasure μ] :
    measureConvolutionPower μ 1 = μ := by
  unfold measureConvolutionPower
  exact Measure.mconv_dirac_one μ

omit [MeasurableInv H] in
theorem measureConvolutionPower_add (μ : Measure H) [IsProbabilityMeasure μ] (n k : ℕ) :
    measureConvolutionPower μ (n + k) = measureConvolutionPower μ n ∗ₘ measureConvolutionPower μ k := by
  have : IsProbabilityMeasure (measureConvolutionPower μ k) := measureConvolutionPower_probability μ k
  induction n with
  | zero => simp only [Nat.zero_add, measureConvolutionPower, Measure.dirac_one_mconv]
  | succ n ih =>
    have : IsProbabilityMeasure (measureConvolutionPower μ n) := measureConvolutionPower_probability μ n
    rw [Nat.succ_add, measureConvolutionPower, ih, ← Measure.mconv_assoc]
    rfl

omit [MeasurableInv H] in
theorem measureConvolutionPower_comm (μ : Measure H) [IsProbabilityMeasure μ] (n k : ℕ) :
    measureConvolutionPower μ n ∗ₘ measureConvolutionPower μ k =
      measureConvolutionPower μ k ∗ₘ measureConvolutionPower μ n := by
  rw [← measureConvolutionPower_add, ← measureConvolutionPower_add, Nat.add_comm]

omit [MeasurableInv H] in
theorem measureConvolutionPower_succ_right (μ : Measure H) [IsProbabilityMeasure μ] (n : ℕ) :
    measureConvolutionPower μ (n + 1) = measureConvolutionPower μ n ∗ₘ μ := by
  rw [measureConvolutionPower_add, measureConvolutionPower_one]

theorem measureConvolutionPower_inv (μ : Measure H) [IsProbabilityMeasure μ]
    (hμ : μ.inv = μ) (n : ℕ) : (measureConvolutionPower μ n).inv = measureConvolutionPower μ n := by
  induction n with
  | zero => simp [measureConvolutionPower, Measure.inv_def, Measure.map_dirac' measurable_inv]
  | succ n ih =>
    have : IsProbabilityMeasure (measureConvolutionPower μ n) := measureConvolutionPower_probability μ n
    rw [measureConvolutionPower, inv_mconv, ih, hμ]
    simpa only [measureConvolutionPower_one] using measureConvolutionPower_comm μ n 1

end TransposeFollowup
