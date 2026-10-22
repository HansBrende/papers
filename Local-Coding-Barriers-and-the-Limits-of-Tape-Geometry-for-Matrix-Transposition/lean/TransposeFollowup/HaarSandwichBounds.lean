import TransposeFollowup.HaarSandwichRepresentations

/-! Quantitative popular-overlap sandwich bounds, and the elementary
translation comparisons used to extract tripling and one-sided products. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

omit [MeasurableInv G] in
theorem haar_measure_le_left_product (σ : Measure G) [Measure.IsMulLeftInvariant σ]
    {A : Set G} (hA : A.Nonempty) (B : Set G) : σ B ≤ σ (A * B) := by
  obtain ⟨a, ha⟩ := hA
  calc
    σ B ≤ σ ((fun b => a * b) ⁻¹' (A * B)) :=
      measure_mono (fun b hb => Set.mul_mem_mul ha hb)
    _ = _ := measure_preimage_mul σ a _

omit [MeasurableInv G] in
theorem haar_measure_le_right_product (σ : Measure G) [Measure.IsMulRightInvariant σ]
    (A : Set G) {B : Set G} (hB : B.Nonempty) : σ A ≤ σ (A * B) := by
  obtain ⟨b, hb⟩ := hB
  calc
    σ A ≤ σ ((fun a => a * b) ⁻¹' (A * B)) :=
      measure_mono (fun a ha => Set.mul_mem_mul ha hb)
    _ = _ := measure_preimage_mul_right σ b _

theorem popularOverlap_sandwich_volume (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A : Set G} (hA : MeasurableSet A) (hAA : MeasurableSet (A * A⁻¹))
    (hA0 : 0 < σ A) (hAt : σ A < ⊤) {K : ℝ≥0∞} (hK : 0 < K) (hKt : K ≠ ⊤)
    (hsmall : σ (A * A⁻¹) ≤ K * σ A) (n : ℕ)
    (hprod : MeasurableSet (A * (popularProductSet σ A⁻¹ A (σ A / (2 * K))) ^ n * A⁻¹)) :
    σ (A * (popularProductSet σ A⁻¹ A (σ A / (2 * K))) ^ n * A⁻¹) ≤
      2 ^ n * K ^ (2 * n + 1) * σ A := by
  let a := σ A
  let t := a / (2 * K)
  let T := popularProductSet σ A⁻¹ A t
  have ht : t ^ n * σ (A * T ^ n * A⁻¹) ≤ σ (A * A⁻¹) ^ (n + 1) :=
    sandwich_power_threshold_volume_le σ hA hAA
      (fun s hs => (show t < densityConvolution σ ((A⁻¹).indicator 1) (A.indicator 1) s from hs).le) n hprod
  have hc : (2 * K) * t = a := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  apply (ENNReal.mul_le_mul_iff_right (pow_ne_zero n hA0.ne') (by finiteness)).mp
  calc
    a ^ n * σ (A * T ^ n * A⁻¹) = (2 * K) ^ n * (t ^ n * σ (A * T ^ n * A⁻¹)) := by
      rw [← mul_assoc, ← mul_pow, hc]
    _ ≤ (2 * K) ^ n * σ (A * A⁻¹) ^ (n + 1) := mul_le_mul' le_rfl ht
    _ ≤ (2 * K) ^ n * (K * a) ^ (n + 1) := mul_le_mul' le_rfl (pow_le_pow_left' hsmall (n + 1))
    _ = a ^ n * (2 ^ n * K ^ (2 * n + 1) * a) := by
      rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
      simp only [mul_pow, pow_succ]
      ring

end TransposeFollowup
