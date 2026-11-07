import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # A finite binomial lower-tail bound

The sharp exponential base at the half threshold follows termwise from
the geometric mean and the binomial theorem. No probability-space adapter
is needed to apply the result to exact finite tensor-basis counts.
-/

namespace LeanMachine.BinomialTail

open Finset
set_option autoImplicit false
noncomputable section

/-- A below-half monomial is bounded by the geometric mean to the total power. -/
theorem monomial_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x)
    {m a : ℕ} (ha : 2 * a ≤ m) :
    x ^ a * y ^ (m - a) ≤ Real.sqrt (x * y) ^ m := by
  have hx := hy.trans hxy
  have hp := mul_nonneg hx hy
  have hs : y ≤ Real.sqrt (x * y) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsplit : m - a = a + (m - 2 * a) := by omega
  calc
    _ = (x * y) ^ a * y ^ (m - 2 * a) := by rw [hsplit, pow_add, mul_pow]; ring
    _ ≤ (x * y) ^ a * Real.sqrt (x * y) ^ (m - 2 * a) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hs _) (pow_nonneg hp _)
    _ = Real.sqrt (x * y) ^ (2 * a) * Real.sqrt (x * y) ^ (m - 2 * a) := by
      rw [pow_mul, Real.sq_sqrt hp]
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Includes the midpoint when the number of trials is even. -/
theorem half_sum_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (m : ℕ) :
    ∑ a ∈ (range (m + 1)).filter (fun a => 2 * a ≤ m),
      (m.choose a : ℝ) * x ^ a * y ^ (m - a) ≤
        (2 * Real.sqrt (x * y)) ^ m := by
  have hsum : ∑ a ∈ range (m + 1), (m.choose a : ℝ) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  calc
    _ ≤ ∑ a ∈ (range (m + 1)).filter (fun a => 2 * a ≤ m),
        (m.choose a : ℝ) * Real.sqrt (x * y) ^ m := by
      apply sum_le_sum
      intro a ha
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (monomial_le hy hxy (mem_filter.mp ha).2)
        (Nat.cast_nonneg _)
    _ ≤ ∑ a ∈ range (m + 1), (m.choose a : ℝ) * Real.sqrt (x * y) ^ m :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by rw [← sum_mul, hsum, ← mul_pow]

/-- The exact exponential decay constant at the half threshold. -/
def decay (ρ : ℝ) : ℝ := -Real.log (2 * Real.sqrt (ρ * (1 - ρ)))

theorem decay_pos {ρ : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1) : 0 < decay ρ := by
  have hp : 0 < ρ * (1 - ρ) := mul_pos (by linarith) (by linarith)
  have hs := Real.sq_sqrt hp.le
  have hbase : 2 * Real.sqrt (ρ * (1 - ρ)) < 1 := by
    nlinarith [Real.sqrt_nonneg (ρ * (1 - ρ)), sq_pos_of_pos (show 0 < ρ - 1 / 2 by linarith)]
  exact neg_pos.mpr (Real.log_neg (by positivity) hbase)

/-- The same sharp constant works for every success parameter at least `ρ`. -/
theorem half_sum_le_exp {ρ r : ℝ} (hρ : 1 / 2 < ρ) (hρ1 : ρ < 1)
    (hr : ρ ≤ r) (hr1 : r ≤ 1) (m : ℕ) :
    ∑ a ∈ (range (m + 1)).filter (fun a => 2 * a ≤ m),
      (m.choose a : ℝ) * r ^ a * (1 - r) ^ (m - a) ≤
        Real.exp (-decay ρ * m) := by
  have hp : 0 < ρ * (1 - ρ) := mul_pos (by linarith) (by linarith)
  have hvar : r * (1 - r) ≤ ρ * (1 - ρ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ r + ρ - 1 by linarith)]
  calc
    _ ≤ (2 * Real.sqrt (r * (1 - r))) ^ m := half_sum_le (by linarith) (by linarith) m
    _ ≤ (2 * Real.sqrt (ρ * (1 - ρ))) ^ m :=
      pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num)) _
    _ = _ := by
      rw [decay, neg_neg, mul_comm (Real.log _), Real.exp_nat_mul,
        Real.exp_log (by positivity)]

end
end LeanMachine.BinomialTail
