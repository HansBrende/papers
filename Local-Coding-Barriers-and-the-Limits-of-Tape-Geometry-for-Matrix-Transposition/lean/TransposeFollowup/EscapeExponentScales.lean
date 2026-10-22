import TransposeFollowup.InitialWalkScales
import TransposeFollowup.DyadicSeparationInterpolation

/-! Denominator bounds at a shorter scale and absorption of the fixed
quantitative escape constants into any requested positive radius exponent. -/
namespace TransposeFollowup.RationalFreePair
set_option autoImplicit false

theorem initial_escape_denominator_lower (r v : ℕ) :
    ((1 / 4 : ℝ) ^ v) ^ 17 ≤ 1 / (dyadicDenominator r : ℝ) ^ (34 * initialWalkLength r v) := by
  have hD : 0 < (dyadicDenominator r : ℝ) := by exact_mod_cast dyadicDenominator_pos r
  have hbase : (1 / 4 : ℝ) ^ v ≤ 1 / (dyadicDenominator r : ℝ) ^ (2 * initialWalkLength r v) := by
    calc
      _ = 1 / (4 : ℝ) ^ v := one_div_pow _ _
      _ ≤ 1 / (2 : ℝ) ^ v := one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (by norm_num) (by norm_num) v)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (initial_denominator_power_le r v)
  have hh := pow_le_pow_left₀ (by positivity) hbase 17
  simpa only [one_div_pow, ← pow_mul,
    show (2 * initialWalkLength r v) * 17 = 34 * initialWalkLength r v by omega] using hh

theorem initial_escape_gap_of_short_index (r j v : ℕ) {ε : ℝ}
    (hv : 34 * (v : ℝ) ≤ (j : ℝ) * ε) :
    ((1 / 4 : ℝ) ^ j) ^ (ε / 2) ≤
      1 / (dyadicDenominator r : ℝ) ^ (34 * initialWalkLength r v) := by
  calc
    _ = (1 / 4 : ℝ) ^ ((j : ℝ) * (ε / 2)) := by
      rw [← Real.rpow_natCast (1 / 4 : ℝ) j, ← Real.rpow_mul (by norm_num)]
    _ ≤ (1 / 4 : ℝ) ^ ((v : ℝ) * (17 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    _ = ((1 / 4 : ℝ) ^ v) ^ (17 : ℕ) := by
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
      exact Real.rpow_natCast ((1 / 4 : ℝ) ^ v) 17
    _ ≤ _ := initial_escape_denominator_lower r v

theorem exists_escape_prefactor_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ {z : ℝ}, ((1 / 4 : ℝ) ^ j) ^ (ε / 2) ≤ z →
      ((1 / 4 : ℝ) ^ j) ^ ε ≤ min (1 / (32 * (18 : ℝ) ^ 4))
        (z / ((2 : ℝ) ^ 44 * 18 ^ 21)) := by
  let C := min (1 / (32 * (18 : ℝ) ^ 4)) (1 / ((2 : ℝ) ^ 44 * 18 ^ 21))
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨Jc, hJc⟩ := exists_quarter_scale_threshold hC
  obtain ⟨J, hJ⟩ := exists_separation_window_threshold (by linarith : 0 < ε / 2) Jc
  refine ⟨J, ?_⟩
  intro j hj z hz
  let η := (1 / 4 : ℝ) ^ j
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηone : η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hh : η ^ (ε / 2) ≤ C := ((hJ j hj).trans (min_le_right _ _)).trans (hJc Jc le_rfl)
  have hleft := hh.trans (min_le_left _ _)
  have hright := hh.trans (min_le_right _ _)
  apply le_min
  · exact (Real.rpow_le_rpow_of_exponent_ge hη hηone (by linarith : ε / 2 ≤ ε)).trans hleft
  · calc
      _ = η ^ (ε / 2) * η ^ (ε / 2) := by rw [← Real.rpow_add hη]; congr 1; ring
      _ ≤ (1 / ((2 : ℝ) ^ 44 * 18 ^ 21)) * z :=
        mul_le_mul hright hz (Real.rpow_nonneg hη.le _) (by positivity)
      _ = _ := by ring

end TransposeFollowup.RationalFreePair
