import TransposeFollowup.SmoothedWalkSeparatedSubset
import TransposeFollowup.InitialWalkRadiusGain

/-! The existing dyadic short length gives a separated subset at the
requested dyadic scale, with a fixed positive cardinal-growth exponent.
The smoothing radius is independent of that requested scale. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

theorem initial_length_separation_radius {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j) :
    (1 / 4 : ℝ) ^ j ≤ 1 / (128 * (dyadicDenominator r : ℝ) ^ (2 * initialWalkLength r j)) := by
  have hP : (128 : ℝ) ≤ 2 ^ j := by
    calc
      _ = (2 : ℝ) ^ 7 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hD : (0 : ℝ) < dyadicDenominator r := by exact_mod_cast dyadicDenominator_pos r
  have hz : (0 : ℝ) < 2 ^ j := by positivity
  rw [quarter_pow_eq_inverse_square]
  apply one_div_le_one_div_of_le (by positivity)
  have hh := initial_denominator_power_le r j
  nlinarith only [mul_nonneg hz.le (sub_nonneg.mpr hP), hh]

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_dyadic_walk_separated_subset {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j)
    (g : Fin (2 ^ (3 * r)) → Group)
    (hg : ∀ i, HasDenominator (dyadicDenominator r) (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    {A : Set RealMobius.Group} (hA : MeasurableSet A) (hAb : A ⊆ matrixEntryBox 2)
    (w : RealMobius.Group) {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤)
    (hmass : p ≤ (generatorWalkMeasure (realEmbedding ∘ g) (initialWalkLength r j) ∗ₘ
      mobiusHaarKernel η) (w • A)) :
    ∃ F : Finset RealMobius.Group, (F : Set RealMobius.Group) ⊆ A ∧
      Metric.IsSeparated (ENNReal.ofReal ((1 / 4 : ℝ) ^ j))
        ((fun a : RealMobius.Group => (a : Matrix (Fin 2) (Fin 2) ℝ)) '' (F : Set RealMobius.Group)) ∧
      p ≤ 2 * (F.card : ℝ≥0∞) * ENNReal.ofReal (((1 / 4 : ℝ) ^ j) ^ (1 / 30720 : ℝ)) := by
  have hm : 0 < (2 : ℕ) ^ (3 * r) := by positivity
  have hε := dyadicRadius_pos r
  have hk : 1 ≤ 1 / dyadicRadius r := (le_div_iff₀ hε).mpr (by simpa using dyadicRadius_le_one r)
  have hcard : (1 / dyadicRadius r) ^ 2 ≤ 2 * ((2 ^ (3 * r) : ℕ) : ℝ) := by
    have hh := pow_le_pow_right₀ hk (by norm_num : (2 : ℕ) ≤ 3)
    rw [dyadicFamily_mass] at hh
    have hm0 : (0 : ℝ) ≤ ((2 ^ (3 * r) : ℕ) : ℝ) := by positivity
    linarith
  obtain ⟨F, hFA, hsep, hcount⟩ := exists_separated_subset_of_smoothed_walk_mass g hm
    (dyadicDenominator_pos r) hg hfree hk hcard (initialWalkLength r j) hη hηone hA hAb w hp hpt hmass
  refine ⟨F, hFA, hsep.anti (ENNReal.ofReal_le_ofReal (initial_length_separation_radius hr hj)), ?_⟩
  have hatom : (2 / (1 / dyadicRadius r)) ^ initialWalkLength r j ≤
      ((1 / 4 : ℝ) ^ j) ^ (1 / 30720 : ℝ) := by
    simpa only [div_div_eq_mul_div, div_one] using initial_walk_factor_radius_le hr hj
  exact hcount.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hatom))

end TransposeFollowup.RationalFreePair
