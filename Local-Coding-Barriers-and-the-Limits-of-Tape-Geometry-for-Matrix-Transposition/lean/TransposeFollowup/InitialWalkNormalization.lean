import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-! Absorb a fixed prefactor into half of the initial radius exponent.
The threshold depends on the prefactor, not on the generator family. -/
namespace TransposeFollowup
open Classical
set_option autoImplicit false

theorem exists_initial_radius_prefactor_threshold (C : ℝ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      C * ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 30720 : ℝ) ≤
        ((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 61440 : ℝ) := by
  have hb : (1 : ℝ) < (1 / 4 : ℝ) ^ (-1 / 61440 : ℝ) :=
    Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨J, ?_⟩
  intro j hj
  have hC : C ≤ ((1 / 4 : ℝ) ^ j) ^ (-1 / 61440 : ℝ) := by
    calc
      _ ≤ ((1 / 4 : ℝ) ^ (-1 / 61440 : ℝ)) ^ J := hJ.le
      _ ≤ ((1 / 4 : ℝ) ^ (-1 / 61440 : ℝ)) ^ j := pow_le_pow_right₀ hb.le hj
      _ = _ := Real.rpow_pow_comm (by norm_num) _ _
  calc
    _ ≤ (((1 / 4 : ℝ) ^ j) ^ (-1 / 61440 : ℝ)) *
        (((1 / 4 : ℝ) ^ j) ^ (-3 + 1 / 30720 : ℝ)) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      norm_num

end TransposeFollowup
