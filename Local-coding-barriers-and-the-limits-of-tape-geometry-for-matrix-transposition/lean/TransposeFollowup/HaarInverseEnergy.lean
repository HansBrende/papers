import TransposeFollowup.HaarRuzsaBounds

/-! Autocorrelation as inverse convolution, and the trace symmetry
E(A,A^-1)=E(A^-1,A), without assuming that A is symmetric. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem autocorrelationDensity_eq_inverse_convolution (σ : Measure G) [Measure.IsInvInvariant σ]
    {f : G → ℝ≥0∞} (hf : Measurable f) :
    autocorrelationDensity σ f = densityConvolution σ (fun x => f x⁻¹) f := by
  have hfi : Measurable (fun x => f x⁻¹) := by fun_prop
  rw [densityConvolution_eq_leftConvolutionDensity σ hfi hf]
  unfold autocorrelationDensity
  rw [inv_withDensity σ hf]

theorem inverse_indicator_convolution_eq_autocorrelation (σ : Measure G) [Measure.IsInvInvariant σ]
    {A : Set G} (hA : MeasurableSet A) :
    densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) = autocorrelationDensity σ (A.indicator 1) := by
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  rw [autocorrelationDensity_eq_inverse_convolution σ hf]
  congr 1

theorem inverse_indicator_convolution_inv (σ : Measure G)
    [Measure.IsInvInvariant σ] [Measure.IsMulRightInvariant σ]
    {A : Set G} (hA : MeasurableSet A) (x : G) :
    densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) x⁻¹ =
      densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) x := by
  rw [inverse_indicator_convolution_eq_autocorrelation σ hA]
  exact autocorrelationDensity_inv σ (measurable_const.indicator hA) x

theorem haarMultiplicativeEnergy_inv_swap (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {A : Set G} (hA : MeasurableSet A) :
    haarMultiplicativeEnergy σ A A⁻¹ = haarMultiplicativeEnergy σ A⁻¹ A := by
  let f := A.indicator (1 : G → ℝ≥0∞)
  let g := (A⁻¹).indicator (1 : G → ℝ≥0∞)
  let F := densityConvolution σ f g
  let J := densityConvolution σ g f
  have hf : Measurable f := measurable_const.indicator hA
  have hg : Measurable g := measurable_const.indicator hA.inv
  have hF : Measurable F := densityConvolution_measurable σ hf hg
  have hJ : Measurable J := densityConvolution_measurable σ hg hf
  have hFs : (fun x => F x⁻¹) = F := by
    funext x
    simpa only [inv_inv] using inverse_indicator_convolution_inv σ hA.inv x
  have hJs : (fun x => J x⁻¹) = J := funext (inverse_indicator_convolution_inv σ hA)
  calc
    haarMultiplicativeEnergy σ A A⁻¹ = densityConvolution σ F F 1 := by
      change (∫⁻ x, F x ^ 2 ∂σ) = densityConvolution σ F F 1
      simpa only [hFs] using (densityConvolution_inverse_at_one σ F).symm
    _ = densityConvolution σ f (densityConvolution σ g F) 1 := densityConvolution_assoc σ hf hg hF 1
    _ = densityConvolution σ (densityConvolution σ g F) f 1 := densityConvolution_comm_at_one σ _ _
    _ = densityConvolution σ g (densityConvolution σ F f) 1 := densityConvolution_assoc σ hg hF hf 1
    _ = densityConvolution σ g (densityConvolution σ f J) 1 := by
      congr 1
      funext x
      exact densityConvolution_assoc σ hf hg hf x
    _ = densityConvolution σ J J 1 := (densityConvolution_assoc σ hg hf hJ 1).symm
    _ = haarMultiplicativeEnergy σ A⁻¹ A := by
      change densityConvolution σ J J 1 = ∫⁻ x, J x ^ 2 ∂σ
      simpa only [hJs] using densityConvolution_inverse_at_one σ J

end TransposeFollowup
