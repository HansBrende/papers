import TransposeFollowup.OpenRelationDegrees
import TransposeFollowup.ProductQuotientControl

/-! A common-neighbor representation controls every selected product.
All changes of variables retain the noncommutative multiplication order. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

theorem densityConvolution_product_neighbor_eq (σ : Measure G)
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    (D C : Set G) (a b : G) :
    densityConvolution σ (D.indicator 1) (C.indicator 1) (a * b) =
      ∫⁻ x, D.indicator (1 : G → ℝ≥0∞) (a * x⁻¹) * C.indicator 1 (x * b) ∂σ := by
  calc
    _ = ∫⁻ x, D.indicator (1 : G → ℝ≥0∞) (a * x) * C.indicator 1 ((a * x)⁻¹ * (a * b)) ∂σ :=
      (lintegral_mul_left_eq_self (μ := σ)
        (fun y => D.indicator (1 : G → ℝ≥0∞) y * C.indicator 1 (y⁻¹ * (a * b))) a).symm
    _ = ∫⁻ x, D.indicator (1 : G → ℝ≥0∞) (a * x) * C.indicator 1 (x⁻¹ * b) ∂σ := by
      simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    _ = _ := by
      simpa only [inv_inv] using (lintegral_inv_eq_self (μ := σ)
        (fun x => D.indicator (1 : G → ℝ≥0∞) (a * x) * C.indicator 1 (x⁻¹ * b))).symm

theorem productNeighbor_degree_le_density_add_bad (σ : Measure G)
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    (S : Set G) {C D : Set G} (hC : MeasurableSet C) (hD : MeasurableSet D) (a b : G) :
    edgeFiberMass (σ.restrict S) (productIncidence C) b ≤
      densityConvolution σ (D.indicator 1) (C.indicator 1) (a * b) +
        relationRowDegree (σ.restrict S) {p : G × G | p.1 * p.2⁻¹ ∉ D} a := by
  have hc : Measurable (C.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hC
  have hd : Measurable (D.indicator (1 : G → ℝ≥0∞)) := measurable_const.indicator hD
  calc
    _ ≤ ∫⁻ x in S, D.indicator (1 : G → ℝ≥0∞) (a * x⁻¹) * C.indicator 1 (x * b) +
        Dᶜ.indicator 1 (a * x⁻¹) ∂σ := by
      apply lintegral_mono
      intro x
      change C.indicator (1 : G → ℝ≥0∞) (x * b) ≤ _
      by_cases hd' : a * x⁻¹ ∈ D <;> by_cases hc' : x * b ∈ C <;> simp [hd', hc']
    _ = (∫⁻ x in S, D.indicator (1 : G → ℝ≥0∞) (a * x⁻¹) * C.indicator 1 (x * b) ∂σ) +
        relationRowDegree (σ.restrict S) {p : G × G | p.1 * p.2⁻¹ ∉ D} a := by
      rw [lintegral_add_left (show Measurable (fun x =>
        D.indicator (1 : G → ℝ≥0∞) (a * x⁻¹) * C.indicator 1 (x * b)) from by fun_prop)]
      rfl
    _ ≤ densityConvolution σ (D.indicator 1) (C.indicator 1) (a * b) +
        relationRowDegree (σ.restrict S) {p : G × G | p.1 * p.2⁻¹ ∉ D} a := by
      apply add_le_add _ le_rfl
      rw [densityConvolution_product_neighbor_eq]
      exact setLIntegral_le_lintegral _ _

end TransposeFollowup
