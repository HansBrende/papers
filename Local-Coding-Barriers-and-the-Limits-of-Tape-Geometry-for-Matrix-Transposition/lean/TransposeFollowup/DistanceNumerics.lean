import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Integer logarithmic budgets shared by packet distance consequences. -/

namespace TransposeFollowup

set_option autoImplicit false

theorem half_log_power_budget (D n : ℕ) (hD : 2 ≤ D) (hn : 0 < n) :
    (Nat.log D n / 2 + 1) * D ^ (Nat.log D n / 2) ≤ n := by
  let k := Nat.log D n / 2
  have hk : k + 1 ≤ D ^ k :=
    (Nat.succ_le_of_lt (show k < 2 ^ k from Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hD k)
  have hexp : 2 * k ≤ Nat.log D n := by dsimp [k]; omega
  calc
    _ ≤ D ^ k * D ^ k := Nat.mul_le_mul_right _ hk
    _ = D ^ (2 * k) := by rw [← pow_add]; congr 1; omega
    _ ≤ D ^ Nat.log D n := Nat.pow_le_pow_right (by omega) hexp
    _ ≤ n := Nat.pow_log_le_self D (Nat.ne_of_gt hn)

theorem log_le_twice_half_log (D n : ℕ) (hD : 2 ≤ D) (hn : 0 < n) :
    Real.log (n : ℝ) ≤ 2 * ((Nat.log D n / 2 : ℕ) + 2 : ℝ) * Real.log (D : ℝ) := by
  have hnat := Nat.lt_pow_succ_log_self (by omega : 1 < D) n
  have hlog := (Real.log_lt_log (by exact_mod_cast hn : 0 < (n : ℝ))
    (by exact_mod_cast hnat : (n : ℝ) < (D : ℝ) ^ (Nat.log D n + 1))).le
  rw [Real.log_pow] at hlog
  have hindex : ((Nat.log D n + 1 : ℕ) : ℝ) ≤ 2 * ((Nat.log D n / 2 : ℕ) + 2 : ℝ) := by
    exact_mod_cast (show Nat.log D n + 1 ≤ 2 * (Nat.log D n / 2 + 2) by omega)
  exact hlog.trans (mul_le_mul_of_nonneg_right hindex (Real.log_natCast_nonneg D))

end TransposeFollowup
