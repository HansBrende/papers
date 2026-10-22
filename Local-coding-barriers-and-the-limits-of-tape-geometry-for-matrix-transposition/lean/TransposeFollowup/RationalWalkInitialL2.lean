import TransposeFollowup.RationalWalkNonconcentration

/-! The initial squared L2 estimate for the actual Haar-smoothed walk,
including integrability of its real density. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem mobiusSmoothedDensity_lintegral_sq_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η : ℝ} (hη : 0 < η) {C : ℝ≥0∞} (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ C) :
    (∫⁻ x, (mobiusSmoothedDensity μ η x) ^ 2 ∂(Measure.haar : Measure Group)) ≤ C := by
  calc
    _ ≤ ∫⁻ x, C * mobiusSmoothedDensity μ η x ∂(Measure.haar : Measure Group) := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [pow_two]
      gcongr
      exact hC x
    _ = C := by
      rw [lintegral_const_mul _ (mobiusSmoothedDensity_measurable μ η),
        mobiusSmoothedDensity_lintegral μ hη, mul_one]

theorem mobiusSmoothedDensity_integrable_sq_and_le (μ : Measure Group) [IsProbabilityMeasure μ]
    {η C : ℝ} (hη : 0 < η) (hC0 : 0 ≤ C)
    (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C) :
    Integrable (fun x => (mobiusSmoothedDensity μ η x).toReal ^ 2) (Measure.haar : Measure Group) ∧
      (∫ x, (mobiusSmoothedDensity μ η x).toReal ^ 2 ∂(Measure.haar : Measure Group)) ≤ C := by
  have he : (∫⁻ x, ENNReal.ofReal ((mobiusSmoothedDensity μ η x).toReal ^ 2)
      ∂(Measure.haar : Measure Group)) =
      ∫⁻ x, (mobiusSmoothedDensity μ η x) ^ 2 ∂(Measure.haar : Measure Group) := by
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (mobiusSmoothedDensity_lt_top μ hη x).ne]
  have hb := mobiusSmoothedDensity_lintegral_sq_le μ hη hC
  have hmeas : AEStronglyMeasurable (fun x => (mobiusSmoothedDensity μ η x).toReal ^ 2)
      (Measure.haar : Measure Group) :=
    ((mobiusSmoothedDensity_measurable μ η).ennreal_toReal.pow_const 2).aestronglyMeasurable
  have hnonneg := ae_of_all (Measure.haar : Measure Group)
    (fun x => sq_nonneg (mobiusSmoothedDensity μ η x).toReal)
  have hi : Integrable (fun x => (mobiusSmoothedDensity μ η x).toReal ^ 2)
      (Measure.haar : Measure Group) := by
    apply (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp
    rw [he]
    exact (hb.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas, he]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [ENNReal.toReal_ofReal hC0] using h

end TransposeFollowup.RealMobius

namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem rationalWalk_initial_L2_bound {m Q : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hQ : 0 < Q) (hg : ∀ i, HasDenominator Q (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hmass : (1 / ε) ^ 3 ≤ (m : ℝ)) (n : ℕ)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hscale : 8 * η < 1 / (Q : ℝ) ^ (2 * n)) :
    Integrable (fun x => (RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) η x).toReal ^ 2)
        (Measure.haar : Measure RealMobius.Group) ∧
    (∫ x, (RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) η x).toReal ^ 2
        ∂(Measure.haar : Measure RealMobius.Group)) ≤
      512 * (2 * ε) ^ n /
        ((Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ) * η ^ 3) := by
  have : IsProbabilityMeasure (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) :=
    RealMobius.generatorWalkMeasure_probability _ hm n
  apply RealMobius.mobiusSmoothedDensity_integrable_sq_and_le _ hη
  · positivity
  · exact rationalWalk_smoothedDensity_epsilon_le g hm hQ hg hfree hε hε1 hmass n hη hηhalf hscale

end TransposeFollowup.RationalFreePair
