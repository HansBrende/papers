import TransposeFollowup.NonflatteningLevelPair
import TransposeFollowup.AutocorrelationIterates

/-! Apply continuous level-pair extraction to the actual canonical symmetric
densities. Mass, symmetry and the inherited bound are proved inputs from
the smoothed walk, not extra hypotheses about an unrelated density. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem smoothedAutocorrelationIterate_succ_eq_densityConvolution
    (μ : Measure Group) [SFinite μ] (η : ℝ) (k : ℕ) :
    smoothedAutocorrelationIterate μ η (k + 1) =
      densityConvolution Measure.haar (smoothedAutocorrelationIterate μ η k)
        (smoothedAutocorrelationIterate μ η k) :=
  autocorrelationDensity_eq_densityConvolution Measure.haar
    (smoothedAutocorrelationIterate_measurable μ η k) (smoothedAutocorrelationIterate_inv μ η k)

theorem exists_smoothedIterate_nonflattening_level_pair
    (μ : Measure Group) [IsProbabilityMeasure μ] {η : ℝ} (hη : 0 < η) (k : ℕ)
    {C τ : ℝ} (hτ : 0 < τ) (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal τ ≤
      ∫⁻ x, smoothedAutocorrelationIterate μ η (k + 1) x ^ 2 ∂(Measure.haar : Measure Group)) :
    let f := smoothedAutocorrelationIterate μ η k
    let a := ENNReal.ofReal (τ / 16)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / τ)) ∧
      ∃ i < N, ∃ j < N,
        MeasurableSet (dyadicDensityLevel f a i) ∧ MeasurableSet (dyadicDensityLevel f a j) ∧
        (∀ x, x⁻¹ ∈ dyadicDensityLevel f a i ↔ x ∈ dyadicDensityLevel f a i) ∧
        (∀ x, x⁻¹ ∈ dyadicDensityLevel f a j ↔ x ∈ dyadicDensityLevel f a j) ∧
        (a * 2 ^ i) * (Measure.haar : Measure Group) (dyadicDensityLevel f a i) ≤ 1 ∧
        (a * 2 ^ j) * (Measure.haar : Measure Group) (dyadicDensityLevel f a j) ≤ 1 ∧
        ENNReal.ofReal τ ≤ 4 * (N : ℝ≥0∞) ^ 4 *
          ((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
            haarMultiplicativeEnergy Measure.haar (dyadicDensityLevel f a i) (dyadicDensityLevel f a j) := by
  dsimp only
  have hf := smoothedAutocorrelationIterate_measurable μ η k
  have hm := (smoothedAutocorrelationIterate_lintegral μ hη k).le
  rw [smoothedAutocorrelationIterate_succ_eq_densityConvolution] at hnonflat
  obtain ⟨N, hN, hlog, i, hi, j, hj, hE⟩ := exists_nonflattening_level_pair Measure.haar hf hm
    hτ (smoothedAutocorrelationIterate_le μ hη hC k) hnonflat
  refine ⟨N, hN, hlog, i, hi, j, hj, dyadicDensityLevel_measurableSet hf _ _,
    dyadicDensityLevel_measurableSet hf _ _, ?_, ?_, ?_, ?_, hE⟩
  · exact dyadicDensityLevel_inv (smoothedAutocorrelationIterate_inv μ η k) _ _
  · exact dyadicDensityLevel_inv (smoothedAutocorrelationIterate_inv μ η k) _ _
  · exact (dyadicDensityLevel_mass_le Measure.haar hf _ _).trans hm
  · exact (dyadicDensityLevel_mass_le Measure.haar hf _ _).trans hm

end TransposeFollowup.RealMobius
