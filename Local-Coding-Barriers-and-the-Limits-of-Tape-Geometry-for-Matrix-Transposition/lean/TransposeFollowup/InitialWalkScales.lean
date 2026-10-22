import TransposeFollowup.DyadicFreeFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! An explicit initial walk length at each dyadic smoothing radius. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

def initialWalkLength (r j : ℕ) : ℕ := j / (3840 * r)

theorem initialWalkLength_pos {r j : ℕ} (hr : 0 < r) (hj : 7680 * r ≤ j) :
    1 ≤ initialWalkLength r j := by
  unfold initialWalkLength
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3840 * r)).mpr
  omega

theorem initialWalkLength_upper (r j : ℕ) : 3840 * r * initialWalkLength r j ≤ j := by
  unfold initialWalkLength
  exact Nat.mul_div_le j (3840 * r)

theorem initialWalkLength_lower {r j : ℕ} (hr : 0 < r) (hj : 7680 * r ≤ j) :
    j ≤ 7680 * r * initialWalkLength r j := by
  have hn := initialWalkLength_pos hr hj
  have hmod := Nat.mod_lt j (show 0 < 3840 * r by omega)
  have he := Nat.mod_add_div j (3840 * r)
  change j % (3840 * r) + 3840 * r * initialWalkLength r j = j at he
  nlinarith

theorem initialWalkLength_decay_exponent {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j) :
    j ≤ 15360 * (r - 1) * initialWalkLength r j := by
  have h : 7680 * r ≤ 15360 * (r - 1) := by omega
  exact (initialWalkLength_lower (by omega) hj).trans (Nat.mul_le_mul_right _ h)

theorem quarter_pow_eq_inverse_square (j : ℕ) :
    (1 / 4 : ℝ) ^ j = 1 / ((2 : ℝ) ^ j) ^ 2 := by
  rw [one_div_pow]
  congr 1
  have h : ((2 : ℝ) ^ j) ^ 2 = ((2 : ℝ) ^ 2) ^ j := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  exact h.symm

theorem initial_smoothing_radius_le_half {r j : ℕ} (hr : 0 < r) (hj : 7680 * r ≤ j) :
    (1 / 4 : ℝ) ^ j ≤ 1 / 2 := by
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) (show 1 ≤ j by omega)
  norm_num only [pow_one] at h
  linarith

theorem initial_denominator_power_le (r j : ℕ) :
    (dyadicDenominator r : ℝ) ^ (2 * initialWalkLength r j) ≤ (2 : ℝ) ^ j := by
  have hQ : (dyadicDenominator r : ℝ) ≤ (2 : ℝ) ^ (1920 * r) := by
    exact_mod_cast dyadicDenominator_upper r
  calc
    _ ≤ ((2 : ℝ) ^ (1920 * r)) ^ (2 * initialWalkLength r j) :=
      pow_le_pow_left₀ (by positivity) hQ _
    _ = (2 : ℝ) ^ (3840 * r * initialWalkLength r j) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (initialWalkLength_upper r j)

theorem initial_walk_separation_scale {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j) :
    8 * (1 / 4 : ℝ) ^ j < 1 / (dyadicDenominator r : ℝ) ^ (2 * initialWalkLength r j) := by
  have hQ0 : 0 < (dyadicDenominator r : ℝ) := by exact_mod_cast dyadicDenominator_pos r
  have hP : (8 : ℝ) < 2 ^ j := by
    calc
      _ < (2 : ℝ) ^ 4 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hz : (0 : ℝ) < 2 ^ j := by positivity
  calc
    _ < 1 / (2 : ℝ) ^ j := by
      rw [quarter_pow_eq_inverse_square]
      rw [show 8 * (1 / ((2 : ℝ) ^ j) ^ 2) = 8 / ((2 : ℝ) ^ j) ^ 2 by ring]
      apply (div_lt_div_iff₀ (sq_pos_of_pos hz) hz).mpr
      nlinarith
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (initial_denominator_power_le r j)

theorem twice_dyadicRadius {r : ℕ} (hr : 1 ≤ r) :
    2 * dyadicRadius r = 1 / (2 : ℝ) ^ (r - 1) := by
  have he : (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [dyadicRadius, he]
  field_simp

theorem initial_walk_factor_power_le {r j : ℕ} (hr : 5 ≤ r) (hj : 7680 * r ≤ j) :
    ((2 * dyadicRadius r) ^ initialWalkLength r j) ^ 15360 ≤ 1 / (2 : ℝ) ^ j := by
  calc
    _ = 1 / (2 : ℝ) ^ (15360 * (r - 1) * initialWalkLength r j) := by
      rw [twice_dyadicRadius (by omega), one_div_pow, one_div_pow, ← pow_mul, ← pow_mul]
      congr 1
      congr 1
      ring
    _ ≤ _ := one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num) (initialWalkLength_decay_exponent hr hj))

end TransposeFollowup.RationalFreePair
