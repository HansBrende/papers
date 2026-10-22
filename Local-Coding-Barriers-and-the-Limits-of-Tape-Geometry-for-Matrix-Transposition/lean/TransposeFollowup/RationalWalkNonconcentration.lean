import TransposeFollowup.RationalWalkIsolation
import TransposeFollowup.GeneratorWalkAtoms
import TransposeFollowup.IsolatedHaarDensity

/-! Initial nonconcentration for the actual rational free-generator walk,
with explicit smoothing scale and Haar normalization. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem rationalWalk_smoothedDensity_le {m Q : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hQ : 0 < Q) (hg : ∀ i, HasDenominator Q (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {k : ℝ} (hk : 1 ≤ k) (hcard : k ^ 2 ≤ 2 * m) (n : ℕ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hscale : 8 * η < 1 / (Q : ℝ) ^ (2 * n)) (x : RealMobius.Group) :
    RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) η x ≤
        ENNReal.ofReal ((2 / k) ^ n) *
          ((Measure.haar : Measure RealMobius.Group) (RealMobius.mobiusIdentityBall η))⁻¹ := by
  apply RealMobius.mobiusSmoothedDensity_le_of_isolated_support _
    (generatorWalkMeasure_ae_denominatorCarrier g hm hg n)
    (RealMobius.generatorWalkMeasure_atom_le _ hm hfree hk hcard n) _ x
  intro a b y ha hb hay hby
  apply denominatorCarrier_smoothing_unique (pow_pos hQ n) hη hη1 _ ha hb hay hby
  simpa only [Nat.cast_pow, ← pow_mul, mul_comm n 2] using hscale

theorem rationalWalk_smoothedDensity_cubic_le {m Q : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hQ : 0 < Q) (hg : ∀ i, HasDenominator Q (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {k : ℝ} (hk : 1 ≤ k) (hcard : k ^ 2 ≤ 2 * m) (n : ℕ)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hscale : 8 * η < 1 / (Q : ℝ) ^ (2 * n)) (x : RealMobius.Group) :
    RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) η x ≤ ENNReal.ofReal
        (512 * (2 / k) ^ n /
          ((Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ) * η ^ 3)) := by
  have hk0 : 0 < k := by linarith
  calc
    _ ≤ ENNReal.ofReal ((2 / k) ^ n) *
        ((Measure.haar : Measure RealMobius.Group) (RealMobius.mobiusIdentityBall η))⁻¹ :=
      rationalWalk_smoothedDensity_le g hm hQ hg hfree hk hcard n hη (by linarith) hscale x
    _ ≤ ENNReal.ofReal ((2 / k) ^ n) * ENNReal.ofReal
        (512 / ((Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ) * η ^ 3)) :=
      by gcongr; exact RealMobius.haar_identityBall_inverse_le hη hηhalf
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 / k) ^ n)]
      congr 1
      ring

theorem rationalWalk_smoothedDensity_epsilon_le {m Q : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hQ : 0 < Q) (hg : ∀ i, HasDenominator Q (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hmass : (1 / ε) ^ 3 ≤ (m : ℝ)) (n : ℕ)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hscale : 8 * η < 1 / (Q : ℝ) ^ (2 * n)) (x : RealMobius.Group) :
    RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) n) η x ≤ ENNReal.ofReal
        (512 * (2 * ε) ^ n /
          ((Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ) * η ^ 3)) := by
  have hk : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hcard : (1 / ε) ^ 2 ≤ 2 * m := by
    have hp : (1 / ε) ^ 2 ≤ (1 / ε) ^ 3 := pow_le_pow_right₀ hk (by omega)
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  have h := rationalWalk_smoothedDensity_cubic_le g hm hQ hg hfree hk hcard n
    hη hηhalf hscale x
  simpa only [div_div_eq_mul_div, div_one] using h

end TransposeFollowup.RationalFreePair
