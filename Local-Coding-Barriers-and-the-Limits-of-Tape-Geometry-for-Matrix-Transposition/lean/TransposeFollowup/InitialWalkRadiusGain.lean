import TransposeFollowup.InitialWalkScales
import TransposeFollowup.RationalWalkInitialL2

/-! Convert the initial endpoint-decay factor into a fixed positive power
of the smoothing radius, with the Haar prefactor left explicit. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem initial_walk_factor_radius_le {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j) :
    (2 * dyadicRadius r) ^ initialWalkLength r j ≤ ((1 / 4 : ℝ) ^ j) ^ (1 / 30720 : ℝ) := by
  have hε := dyadicRadius_pos r
  have hpow : ((2 * dyadicRadius r) ^ initialWalkLength r j) ^ 30720 ≤ (1 / 4 : ℝ) ^ j := by
    calc
      _ = (((2 * dyadicRadius r) ^ initialWalkLength r j) ^ 15360) ^ 2 := by
        conv_rhs => rw [← pow_mul]
      _ ≤ (1 / (2 : ℝ) ^ j) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (initial_walk_factor_power_le hr hj) _
      _ = _ := by rw [one_div_pow, quarter_pow_eq_inverse_square]
  have h := Real.rpow_le_rpow (by positivity) hpow
    (show (0 : ℝ) ≤ (30720 : ℝ)⁻¹ by positivity)
  have he : (((2 * dyadicRadius r) ^ initialWalkLength r j) ^ (30720 : ℕ)) ^
      ((30720 : ℝ)⁻¹) = (2 * dyadicRadius r) ^ initialWalkLength r j := by
    simpa only [Nat.cast_ofNat] using Real.pow_rpow_inv_natCast
      (x := (2 * dyadicRadius r) ^ initialWalkLength r j) (by positivity)
      (by norm_num : (30720 : ℕ) ≠ 0)
  rw [he] at h
  simpa only [one_div] using h

theorem initial_walk_cubic_to_radius {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j)
    {c : ℝ} (hc : 0 < c) :
    512 * (2 * dyadicRadius r) ^ initialWalkLength r j / (c * ((1 / 4 : ℝ) ^ j) ^ 3) ≤
      (512 / c) * ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 30720 : ℝ) := by
  calc
    _ ≤ 512 * (((1 / 4 : ℝ) ^ j) ^ (1 / 30720 : ℝ)) / (c * ((1 / 4 : ℝ) ^ j) ^ 3) := by
      gcongr
      exact initial_walk_factor_radius_le hr hj
    _ = _ := by
      rw [show (-3 + 1 / 30720 : ℝ) = (1 / 30720 : ℝ) - (3 : ℕ) by norm_num,
        Real.rpow_sub_natCast (by positivity : ((1 / 4 : ℝ) ^ j) ≠ 0)]
      ring

theorem dyadicFamily_mass (r : ℕ) :
    (1 / dyadicRadius r) ^ 3 = ((2 ^ (3 * r) : ℕ) : ℝ) := by
  simp only [dyadicRadius, one_div_one_div, Nat.cast_pow, Nat.cast_ofNat,
    ← pow_mul, mul_comm r 3]

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem initial_walk_density_radius_gain {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j)
    (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ i, HasDenominator (dyadicDenominator r) (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g))) (x : RealMobius.Group) :
    RealMobius.mobiusSmoothedDensity
      (RealMobius.generatorWalkMeasure (realEmbedding ∘ g) (initialWalkLength r j))
        ((1 / 4 : ℝ) ^ j) x ≤ ENNReal.ofReal
          ((512 / (Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ)) *
            ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 30720 : ℝ)) := by
  have hm : 0 < (2 : ℕ) ^ (3 * r) := by positivity
  have hc : (0 : ℝ) < (Measure.haarScalarFactor Measure.haar RealMobius.columnChartMeasure : ℝ) := by
    exact_mod_cast RealMobius.haar_column_factor_pos
  have h := rationalWalk_smoothedDensity_epsilon_le g hm (dyadicDenominator_pos r) hg hfree
    (dyadicRadius_pos r) (dyadicRadius_le_one r) (dyadicFamily_mass r).le (initialWalkLength r j)
    (by positivity) (initial_smoothing_radius_le_half (by omega) hj)
    (initial_walk_separation_scale hr hj) x
  exact h.trans (ENNReal.ofReal_le_ofReal (initial_walk_cubic_to_radius hr hj hc))

end TransposeFollowup.RationalFreePair
