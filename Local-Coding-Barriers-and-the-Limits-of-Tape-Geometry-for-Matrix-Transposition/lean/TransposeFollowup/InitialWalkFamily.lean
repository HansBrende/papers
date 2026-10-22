import TransposeFollowup.InitialWalkRadiusGain
import TransposeFollowup.InitialWalkNormalization
import TransposeFollowup.SmoothedDensityPropagation

/-! A fixed rational free family at every small dyadic generator radius,
with normalized initial density/L2 gain for every sufficiently long walk. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem later_walk_density_radius_gain {r j ell : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j)
    (hell : initialWalkLength r j ≤ ell) (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ i, HasDenominator (dyadicDenominator r) (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g))) (x : RealMobius.Group) :
    RealMobius.mobiusSmoothedDensity (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell)
      ((1 / 4 : ℝ) ^ j) x ≤ ENNReal.ofReal
        ((512 / (Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ)) *
          ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 30720 : ℝ)) :=
  RealMobius.generatorWalk_smoothedDensity_le_of_le _ (by positivity) hell
    (initial_walk_density_radius_gain hr hj g hg hfree) x

theorem exists_initial_walk_family :
    ∃ J₀ : ℕ, ∀ r : ℕ, 5 ≤ r → ∃ g : Fin (2 ^ (3 * r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2 ^ (3 * r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2 ^ (3 * r) ∧
      (∀ i, HasDenominator (dyadicDenominator r) (g i) ∧
        realEmbedding (g i) ∈ RealMobius.mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g i))⁻¹ ∈ RealMobius.mobiusIdentityBall (dyadicRadius r)) ∧
      ∀ j : ℕ, max J₀ (7680 * r) ≤ j → ∀ ell : ℕ, initialWalkLength r j ≤ ell →
        (∀ x, RealMobius.mobiusSmoothedDensity (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell)
          ((1 / 4 : ℝ) ^ j) x ≤ ENNReal.ofReal (((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 61440 : ℝ))) ∧
        Integrable (fun x => (RealMobius.mobiusSmoothedDensity
          (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell) ((1 / 4 : ℝ) ^ j) x).toReal ^ 2)
          (Measure.haar : Measure RealMobius.Group) ∧
        (∫ x, (RealMobius.mobiusSmoothedDensity
          (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell) ((1 / 4 : ℝ) ^ j) x).toReal ^ 2
          ∂(Measure.haar : Measure RealMobius.Group)) ≤ ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 61440 : ℝ) := by
  obtain ⟨J₀, hJ₀⟩ := exists_initial_radius_prefactor_threshold
    (512 / (Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ))
  refine ⟨J₀, ?_⟩
  intro r hr
  obtain ⟨g, hg, hgr, hc, hcr, hn⟩ := exists_dyadic_free_family hr
  refine ⟨g, hg, hgr, hc, hcr, hn, ?_⟩
  intro j hj ell hell
  have hd := later_walk_density_radius_gain hr ((le_max_right _ _).trans hj) hell g
    (fun i => (hn i).1) hgr
  have hbound : ∀ x, RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell) ((1 / 4 : ℝ) ^ j) x ≤
        ENNReal.ofReal (((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 61440 : ℝ)) := by
    intro x
    exact (hd x).trans (ENNReal.ofReal_le_ofReal (hJ₀ j ((le_max_left _ _).trans hj)))
  have : IsProbabilityMeasure (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) ell) :=
    RealMobius.generatorWalkMeasure_probability _ (by positivity) ell
  exact ⟨hbound, RealMobius.mobiusSmoothedDensity_integrable_sq_and_le _
    (by positivity) (by positivity) hbound⟩

end TransposeFollowup.RationalFreePair
