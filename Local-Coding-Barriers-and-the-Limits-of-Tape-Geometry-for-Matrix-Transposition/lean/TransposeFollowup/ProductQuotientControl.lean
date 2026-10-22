import TransposeFollowup.ProductFiberSelection
import TransposeFollowup.PopularProductEnergy

/-! Common product neighbors force a quotient into a global popular
difference region. Its volume follows from the existing Markov bound. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem densityConvolution_inverse_indicator_eq (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    (C : Set G) (d : G) :
    densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) d =
      ∫⁻ x, C.indicator (1 : G → ℝ≥0∞) (d * x) * C.indicator 1 x ∂σ := by
  calc
    _ = ∫⁻ x, C.indicator (1 : G → ℝ≥0∞) (d * x) *
        (C⁻¹).indicator 1 ((d * x)⁻¹ * d) ∂σ :=
      (lintegral_mul_left_eq_self (μ := σ)
        (fun y => C.indicator (1 : G → ℝ≥0∞) y * (C⁻¹).indicator 1 (y⁻¹ * d)) d).symm
    _ = _ := by
      apply lintegral_congr
      intro x
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, Set.indicator_apply,
        Set.mem_inv, inv_inv, Pi.one_apply]

omit [MeasurableInv G] in
theorem productCodegree_le_quotient_density (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    (B C : Set G) (a a' : G) :
    edgeCodegree (σ.restrict B) (productIncidence C) (a, a') ≤
      densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) (a * a'⁻¹) := by
  change (∫⁻ b in B, C.indicator (1 : G → ℝ≥0∞) (a * b) * C.indicator 1 (a' * b) ∂σ) ≤ _
  rw [densityConvolution_inverse_indicator_eq]
  calc
    _ ≤ ∫⁻ b, C.indicator (1 : G → ℝ≥0∞) (a * b) * C.indicator 1 (a' * b) ∂σ :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ b, C.indicator (1 : G → ℝ≥0∞) ((a * a'⁻¹) * (a' * b)) * C.indicator 1 (a' * b) ∂σ := by
      simp only [mul_assoc, inv_mul_cancel_left]
    _ = _ := lintegral_mul_left_eq_self (μ := σ)
      (fun x => C.indicator (1 : G → ℝ≥0∞) ((a * a'⁻¹) * x) * C.indicator 1 x) a'

theorem exists_productFiber_quotient_control (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A B C : Set G} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) (hB0 : 0 < σ B) (hBt : σ B < ⊤)
    {K ε : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤) (hε : 0 < ε) (hεt : ε ≠ ⊤)
    (hdense : σ A * σ B ≤ K * (σ.prod σ)
      {p : G × G | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ C}) :
    let t := ε * σ B / (2 * K ^ 2)
    let D := popularProductSet σ C C⁻¹ t
    ∃ b ∈ B, let S := productFiber A C b
      σ A ^ 2 < 4 * K ^ 2 * σ S ^ 2 ∧
      (σ.prod σ) {p : G × G | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 * p.2⁻¹ ∉ D} < ε * σ S ^ 2 ∧
      ε * σ B * σ D ≤ 2 * K ^ 2 * σ C ^ 2 := by
  let t := ε * σ B / (2 * K ^ 2)
  let D := popularProductSet σ C C⁻¹ t
  obtain ⟨b, hb, hsize, hbad⟩ := exists_large_productFiber_few_low_codegrees σ
    hB hC hA0 hAt hB0 hBt hK hKt hε hεt hdense
  refine ⟨b, hb, hsize, ?_, ?_⟩
  · apply lt_of_le_of_lt (measure_mono ?_) hbad
    intro p hp
    refine ⟨hp.1, hp.2.1, ?_⟩
    have hnot : densityConvolution σ (C.indicator 1) ((C⁻¹).indicator 1) (p.1 * p.2⁻¹) ≤ t :=
      le_of_not_gt hp.2.2
    exact (productCodegree_le_quotient_density σ B C p.1 p.2).trans hnot
  · have hm : t * σ D ≤ σ C ^ 2 := by
      simpa only [Measure.measure_inv, pow_two] using
        popularProductSet_threshold_measure_le σ hC hC.inv t
    have hc : (2 * K ^ 2) * t = ε * σ B :=
      ENNReal.mul_div_cancel (by positivity) (by finiteness)
    calc
      ε * σ B * σ D = (2 * K ^ 2) * (t * σ D) := by rw [← mul_assoc, hc]
      _ ≤ _ := mul_le_mul' le_rfl hm

end TransposeFollowup
