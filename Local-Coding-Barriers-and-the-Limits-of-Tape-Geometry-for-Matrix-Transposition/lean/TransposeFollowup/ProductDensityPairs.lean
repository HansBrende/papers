import TransposeFollowup.ContinuousDensityConvolution

/-! Haar density mass on a product region equals the measure of the
actual pairs producing products there. No finite counting model is used. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem restrict_mconv_eq_withDensity (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    σ.restrict A ∗ₘ σ.restrict B =
      σ.withDensity (densityConvolution σ (A.indicator 1) (B.indicator 1)) := by
  have hf : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hA
  have hg : Measurable (B.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hB
  rw [densityConvolution_eq_leftConvolutionDensity σ hf hg,
    ← mconv_withDensity_right _ σ hg, withDensity_indicator_one hA, withDensity_indicator_one hB]

theorem setLIntegral_densityConvolution_eq_pair_measure (σ : Measure G) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] {A B C : Set G}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (∫⁻ x in C, densityConvolution σ (A.indicator 1) (B.indicator 1) x ∂σ) =
      (σ.prod σ) {p : G × G | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 * p.2 ∈ C} := by
  rw [← withDensity_apply _ hC, ← restrict_mconv_eq_withDensity σ hA hB,
    Measure.mconv, Measure.map_apply measurable_mul hC, Measure.prod_restrict,
    Measure.restrict_apply (hC.preimage measurable_mul)]
  congr 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq]
  tauto

end TransposeFollowup
