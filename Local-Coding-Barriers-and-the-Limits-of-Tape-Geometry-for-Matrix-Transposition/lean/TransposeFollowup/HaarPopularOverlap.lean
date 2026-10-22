import TransposeFollowup.HaarInverseEnergy

/-! A small quotient set forces a large popular right-overlap region.
The region is a strict convolution superlevel, suitable for open sets. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem inverse_indicator_convolution_eq_overlap (σ : Measure G) [Measure.IsInvInvariant σ]
    {A : Set G} (hA : MeasurableSet A) (x : G) :
    densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) x =
      ∫⁻ y, A.indicator (1 : G → ℝ≥0∞) y * A.indicator 1 (y * x) ∂σ := by
  rw [inverse_indicator_convolution_eq_autocorrelation σ hA]
  exact autocorrelationDensity_eq_integral σ (measurable_const.indicator hA) x

theorem popularOverlap_volume_bounds (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {A : Set G} (hA : MeasurableSet A) (hAA : MeasurableSet (A * A⁻¹))
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) {K : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤)
    (hsmall : σ (A * A⁻¹) ≤ K * σ A) :
    let T := popularProductSet σ A⁻¹ A (σ A / (2 * K))
    σ A ≤ 2 * K * σ T ∧ σ T ≤ 2 * K * σ A := by
  let a := σ A
  let t := a / (2 * K)
  let T := popularProductSet σ A⁻¹ A t
  let E := haarMultiplicativeEnergy σ A⁻¹ A
  let F := densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1)
  let M := ∫⁻ x in T, F x ∂σ
  have hElower : a ^ 3 ≤ K * E := by
    apply (ENNReal.mul_le_mul_iff_right hA0.ne' hAt.ne).mp
    calc
      a * a ^ 3 = (σ A * σ A⁻¹) ^ 2 := by rw [Measure.measure_inv]; ring
      _ ≤ haarMultiplicativeEnergy σ A A⁻¹ * σ (A * A⁻¹) :=
        haarMultiplicativeEnergy_product_lower σ hA hA.inv hAA
      _ ≤ haarMultiplicativeEnergy σ A A⁻¹ * (K * a) := mul_le_mul' le_rfl hsmall
      _ = a * (K * E) := by rw [haarMultiplicativeEnergy_inv_swap σ hA]; ring
  have hEt : E ≠ ⊤ := (haarMultiplicativeEnergy_lt_top σ hA.inv hA
    (by simpa only [Measure.measure_inv] using hAt) hAt).ne
  have hcancel : (2 * K) * t = a := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  have hhalf : 2 * (t * (a * a)) ≤ E := by
    apply (ENNReal.mul_le_mul_iff_right hK.ne' hKt).mp
    calc
      K * (2 * (t * (a * a))) = ((2 * K) * t) * a ^ 2 := by ring
      _ = a ^ 3 := by rw [hcancel]; ring
      _ ≤ K * E := hElower
  have htail : E ≤ 2 * (a * M) := ennreal_le_two_mul_of_small_add hEt hhalf (by
    simpa only [Measure.measure_inv] using haarEnergy_le_popular_tail_add σ hA.inv hA t)
  have hM : M ≤ a * σ T := by
    calc
      M ≤ ∫⁻ _x in T, a ∂σ := lintegral_mono fun x => by
        simpa only [Measure.measure_inv] using densityConvolution_indicator_le_left σ (B := A) hA.inv x
      _ = _ := by rw [setLIntegral_const]
  constructor
  · apply (ENNReal.mul_le_mul_iff_right (by positivity : a ^ 2 ≠ 0) (by finiteness)).mp
    calc
      a ^ 2 * a = a ^ 3 := by ring
      _ ≤ K * E := hElower
      _ ≤ K * (2 * (a * M)) := mul_le_mul' le_rfl htail
      _ ≤ K * (2 * (a * (a * σ T))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hM))
      _ = a ^ 2 * (2 * K * σ T) := by ring
  · have htbound : t * σ T ≤ a * a := by
      simpa only [Measure.measure_inv] using popularProductSet_threshold_measure_le σ hA.inv hA t
    apply (ENNReal.mul_le_mul_iff_right hA0.ne' hAt.ne).mp
    calc
      a * σ T = (2 * K) * (t * σ T) := by rw [← mul_assoc, hcancel]
      _ ≤ (2 * K) * (a * a) := mul_le_mul' le_rfl htbound
      _ = a * (2 * K * a) := by ring

end TransposeFollowup
