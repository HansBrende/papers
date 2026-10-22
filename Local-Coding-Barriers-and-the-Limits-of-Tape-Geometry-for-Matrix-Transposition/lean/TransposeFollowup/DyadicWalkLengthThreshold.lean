import TransposeFollowup.InitialWalkScales
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The logarithmic length threshold supplied by band selection, at the
actual dyadic generator radius, implies the initial density-gain length. -/
namespace TransposeFollowup.RationalFreePair
set_option autoImplicit false

theorem initialWalkLength_le_of_log_threshold {r j ell : ℕ} (hr : 0 < r)
    (hlog : Real.log (1 / (1 / 4 : ℝ) ^ j) /
        Real.log (1 / dyadicRadius r) < (ell : ℝ)) :
    initialWalkLength r j ≤ ell := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have he : Real.log (1 / (1 / 4 : ℝ) ^ j) /
      Real.log (1 / dyadicRadius r) = 2 * (j : ℝ) / r := by
    rw [one_div_pow, one_div_one_div, dyadicRadius, one_div_one_div,
      Real.log_pow, Real.log_pow, hlog4]
    field_simp
  rw [he] at hlog
  have hh := (div_lt_iff₀ hr').mp hlog
  have hi : 3840 * (r : ℝ) * (initialWalkLength r j : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast initialWalkLength_upper r j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hn : (0 : ℝ) ≤ initialWalkLength r j := Nat.cast_nonneg _
  have hb : (initialWalkLength r j : ℝ) ≤ (ell : ℝ) := by
    nlinarith
  exact_mod_cast hb

end TransposeFollowup.RationalFreePair
