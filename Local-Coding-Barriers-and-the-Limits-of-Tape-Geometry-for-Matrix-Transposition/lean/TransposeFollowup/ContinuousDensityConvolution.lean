import TransposeFollowup.MeasureAutocorrelation

/-! Continuous density convolution, with its mass and elementary tail bounds.
These are Haar-integral statements; no finite discretization is implicit. -/
namespace TransposeFollowup
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

noncomputable def densityConvolution (σ : Measure H) (f g : H → ℝ≥0∞) (x : H) : ℝ≥0∞ :=
  ∫⁻ y, f y * g (y⁻¹ * x) ∂σ

theorem densityConvolution_measurable (σ : Measure H) [SFinite σ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    Measurable (densityConvolution σ f g) := by
  unfold densityConvolution
  exact Measurable.lintegral_prod_right (by fun_prop)

theorem densityConvolution_eq_leftConvolutionDensity (σ : Measure H)
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    densityConvolution σ f g = leftConvolutionDensity (σ.withDensity f) g := by
  funext x
  exact (lintegral_withDensity_eq_lintegral_mul σ hf (by fun_prop)).symm

theorem autocorrelationDensity_eq_densityConvolution (σ : Measure H) [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hs : ∀ x, f x⁻¹ = f x) :
    autocorrelationDensity σ f = densityConvolution σ f f := by
  rw [densityConvolution_eq_leftConvolutionDensity σ hf hf]
  unfold autocorrelationDensity
  rw [inv_withDensity σ hf]
  simp only [hs]

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem densityConvolution_mono (σ : Measure H) {f g F G : H → ℝ≥0∞}
    (hf : ∀ x, f x ≤ F x) (hg : ∀ x, g x ≤ G x) (x : H) :
    densityConvolution σ f g x ≤ densityConvolution σ F G x :=
  lintegral_mono fun y => mul_le_mul' (hf y) (hg (y⁻¹ * x))

theorem densityConvolution_lintegral (σ : Measure H) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {f g : H → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, densityConvolution σ f g x ∂σ = (∫⁻ x, f x ∂σ) * ∫⁻ x, g x ∂σ := by
  unfold densityConvolution
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ = ∫⁻ y, f y * (∫⁻ x, g x ∂σ) ∂σ := by
      apply lintegral_congr
      intro y
      rw [lintegral_const_mul _ (show Measurable (fun x => g (y⁻¹ * x)) from by fun_prop),
        lintegral_mul_left_eq_self (μ := σ) g]
    _ = _ := lintegral_mul_const _ hf

omit [MeasurableMul₂ H] [MeasurableInv H] in
theorem densityConvolution_le_of_right_le (σ : Measure H) {f g : H → ℝ≥0∞}
    (hf : Measurable f) {a : ℝ≥0∞} (hg : ∀ x, g x ≤ a) (x : H) :
    densityConvolution σ f g x ≤ (∫⁻ y, f y ∂σ) * a := by
  calc
    _ ≤ ∫⁻ y, f y * a ∂σ := lintegral_mono fun y => mul_le_mul' le_rfl (hg _)
    _ = _ := lintegral_mul_const _ hf

theorem densityConvolution_le_of_left_le (σ : Measure H) [Measure.IsInvInvariant σ]
    [Measure.IsMulRightInvariant σ] {f g : H → ℝ≥0∞} (hg : Measurable g)
    {a : ℝ≥0∞} (hf : ∀ x, f x ≤ a) (x : H) :
    densityConvolution σ f g x ≤ a * ∫⁻ y, g y ∂σ := by
  calc
    _ ≤ ∫⁻ y, a * g (y⁻¹ * x) ∂σ := lintegral_mono fun y => mul_le_mul' (hf y) le_rfl
    _ = a * ∫⁻ y, g (y⁻¹ * x) ∂σ := lintegral_const_mul _ (by fun_prop)
    _ = _ := by rw [lintegral_inv_eq_self (μ := σ) (fun y => g (y * x)),
      lintegral_mul_right_eq_self (μ := σ) g]

theorem densityConvolution_add_left (σ : Measure H) {f F g : H → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (x : H) :
    densityConvolution σ (fun y => f y + F y) g x =
      densityConvolution σ f g x + densityConvolution σ F g x := by
  simp only [densityConvolution, add_mul]
  exact lintegral_add_left (by fun_prop) _

theorem densityConvolution_add_right (σ : Measure H) {f g G : H → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (x : H) :
    densityConvolution σ f (fun y => g y + G y) x =
      densityConvolution σ f g x + densityConvolution σ f G x := by
  simp only [densityConvolution, mul_add]
  exact lintegral_add_left (by fun_prop) _

theorem densityConvolution_sum_left (σ : Measure H) {ι : Type*} (s : Finset ι)
    {f : ι → H → ℝ≥0∞} {g : H → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i))
    (hg : Measurable g) (x : H) :
    densityConvolution σ (fun y => ∑ i ∈ s, f i y) g x =
      ∑ i ∈ s, densityConvolution σ (f i) g x := by
  simp only [densityConvolution, Finset.sum_mul]
  exact lintegral_finsetSum s fun i hi => (hf i hi).mul (by fun_prop)

theorem densityConvolution_sum_right (σ : Measure H) {ι : Type*} (s : Finset ι)
    {f : H → ℝ≥0∞} {g : ι → H → ℝ≥0∞} (hf : Measurable f)
    (hg : ∀ i ∈ s, Measurable (g i)) (x : H) :
    densityConvolution σ f (fun y => ∑ i ∈ s, g i y) x =
      ∑ i ∈ s, densityConvolution σ f (g i) x := by
  simp only [densityConvolution, Finset.mul_sum]
  exact lintegral_finsetSum s fun i hi => hf.mul ((hg i hi).comp (by fun_prop))

theorem densityConvolution_const_mul (σ : Measure H) {f g : H → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (a b : ℝ≥0∞) (x : H) :
    densityConvolution σ (fun y => a * f y) (fun y => b * g y) x =
      (a * b) * densityConvolution σ f g x := by
  unfold densityConvolution
  simp_rw [show ∀ y, (a * f y) * (b * g (y⁻¹ * x)) =
    (a * b) * (f y * g (y⁻¹ * x)) from fun y => by ac_rfl]
  exact lintegral_const_mul _ (by fun_prop)

end TransposeFollowup
