import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! Conversion from a real binary correctness deficit to the integer
coentropy certificate used by the native tape obstruction. -/

namespace CascadeObstruction

set_option autoImplicit false

/-- The exact binary deficit of a nonempty set of `C` length-`L` words. -/
noncomputable def realDeficit (L C : ℕ) : ℝ :=
  (L : ℝ) - Real.logb 2 C

/-- Round the exact deficit upward for the native counting hypothesis. -/
noncomputable def roundedDeficit (L C : ℕ) : ℕ :=
  ⌈realDeficit L C⌉₊

/-- A subset of the binary cube has nonnegative real deficit. -/
theorem realDeficit_nonneg {L C : ℕ} (hC : 0 < C) (hcap : C ≤ 2 ^ L) :
    0 ≤ realDeficit L C := by
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (show (0 : ℝ) < C by exact_mod_cast hC)
    (show (C : ℝ) ≤ (2 : ℝ) ^ L by exact_mod_cast hcap)
  have hpow : Real.logb 2 ((2 : ℝ) ^ L) = L := by
    rw [Real.logb_pow]
    norm_num
  rw [hpow] at hlog
  exact sub_nonneg.mpr hlog

/-- Upward rounding always dominates the real deficit. -/
theorem realDeficit_le_rounded (L C : ℕ) :
    realDeficit L C ≤ (roundedDeficit L C : ℝ) :=
  Nat.le_ceil _

/-- Rounding costs less than one bit, including a full correctness set. -/
theorem roundedDeficit_lt_add_one {L C : ℕ} (hC : 0 < C) (hcap : C ≤ 2 ^ L) :
    (roundedDeficit L C : ℝ) < realDeficit L C + 1 :=
  Nat.ceil_lt_add_one (realDeficit_nonneg hC hcap)

/-- The rounded real deficit supplies the exact integer counting certificate.
Only nonemptiness is needed here; the cube-size bound is needed for the
less-than-one-bit error estimate. -/
theorem pow_le_roundedDeficit_mul {L C : ℕ} (hC : 0 < C) :
    2 ^ L ≤ 2 ^ roundedDeficit L C * C := by
  have hp : (0 : ℝ) < C := by exact_mod_cast hC
  have hlog : Real.logb 2 ((2 : ℝ) ^ L) ≤
      Real.logb 2 ((2 : ℝ) ^ roundedDeficit L C * C) := by
    rw [Real.logb_mul (by positivity) (ne_of_gt hp), Real.logb_pow,
      Real.logb_pow]
    norm_num only [Real.logb_self_eq_one, mul_one]
    have := realDeficit_le_rounded L C
    unfold realDeficit at this
    linarith
  have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity) (by positivity)).mp hlog
  exact_mod_cast h

end CascadeObstruction
