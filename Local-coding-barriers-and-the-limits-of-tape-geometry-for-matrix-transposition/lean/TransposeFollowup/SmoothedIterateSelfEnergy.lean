import TransposeFollowup.HaarSelfEnergyExtraction
import TransposeFollowup.SmoothedIterateLevelEnergy

/-! A single symmetric positive finite-volume level set with high
self-energy and controlled volume, extracted from a nonflattening step
of the actual smoothed-walk autocorrelation densities. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_nonflattening_self_energy
    (μ : Measure Group) [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) (k : ℕ)
    {C θ : ℝ} (hθ : 0 < θ) (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal θ *
        (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group)) ≤
      ∫⁻ x, smoothedAutocorrelationIterate μ η (k + 1) x ^ 2 ∂(Measure.haar : Measure Group)) :
    let f := smoothedAutocorrelationIterate μ η k
    let U := ∫⁻ x, f x ^ 2 ∂(Measure.haar : Measure Group)
    let τ := θ * U.toReal
    let a := ENNReal.ofReal (τ / 16)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / τ)) ∧
      ∃ i < N, let A := dyadicDensityLevel f a i
        MeasurableSet A ∧ (∀ x, x⁻¹ ∈ A ↔ x ∈ A) ∧
        0 < (Measure.haar : Measure Group) A ∧ (Measure.haar : Measure Group) A < ⊤ ∧
        ENNReal.ofReal θ ≤ 64 * (N : ℝ≥0∞) ^ 4 * U * (Measure.haar : Measure Group) A ∧
        ENNReal.ofReal θ * U * (Measure.haar : Measure Group) A ≤ 64 * (N : ℝ≥0∞) ^ 4 ∧
        ENNReal.ofReal θ ^ 2 * ((Measure.haar : Measure Group) A) ^ 3 ≤
          (64 * (N : ℝ≥0∞) ^ 4) ^ 2 * haarMultiplicativeEnergy Measure.haar A A := by
  rw [smoothedAutocorrelationIterate_succ_eq_densityConvolution] at hnonflat
  exact exists_symmetric_nonflattening_self_energy Measure.haar
    (smoothedAutocorrelationIterate_measurable μ η k)
    (smoothedAutocorrelationIterate_lintegral μ hη k)
    (smoothedAutocorrelationIterate_inv μ η k) hθ
    (smoothedAutocorrelationIterate_le μ hη hC k) hnonflat

end TransposeFollowup.RealMobius
