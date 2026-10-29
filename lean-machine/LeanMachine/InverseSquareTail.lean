import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

/-!
# Inverse-square tail bounds

The finite reciprocal-square estimate gives the tail bound `H / R`.
Every nonnegative sequence under this envelope is summable, so the
comparison also applies without a separate summability hypothesis.
-/

namespace LeanMachine.InverseSquareTail

open scoped BigOperators

/-- An inverse-square envelope is summable for any real amplitude. -/
theorem summable (H : ℝ) :
    Summable (fun i : ℕ => H / (i + 1 : ℝ) ^ 2) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa [div_eq_mul_inv] using hs.mul_left H

/-- The tail beyond a positive natural cutoff is at most `H / R`. -/
theorem tsum_tail_le {H : ℝ} (hH : 0 ≤ H) {R : ℕ} (hR : 0 < R) :
    (∑' i : ℕ, H / ((i + R : ℕ) + 1 : ℝ) ^ 2) ≤ H / R := by
  apply Real.tsum_le_of_sum_range_le (fun i => by positivity)
  intro n
  have hs := (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := R) (n := R + n)
    (Nat.ne_of_gt hR) (Nat.le_add_right R n)).trans
      (sub_le_self _ (by positivity))
  rw [← Finset.Icc_add_one_left_eq_Ioc, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range] at hs
  rw [show R + n + 1 - (R + 1) = n by omega] at hs
  have hm := mul_le_mul_of_nonneg_left hs hH
  simpa [Finset.mul_sum, div_eq_mul_inv, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, add_assoc] using hm

/-- A nonnegative sequence under an inverse-square envelope is summable. -/
theorem summable_of_le {h : ℕ → ℝ} {H : ℝ} (h0 : ∀ i, 0 ≤ h i)
    (hbound : ∀ i, h i ≤ H / (i + 1 : ℝ) ^ 2) : Summable h :=
  Summable.of_nonneg_of_le h0 hbound (summable H)

/-- Pointwise domination transfers the inverse-square tail bound. -/
theorem tail_le {h : ℕ → ℝ} {H : ℝ} (hH : 0 ≤ H) (h0 : ∀ i, 0 ≤ h i)
    (hbound : ∀ i, h i ≤ H / (i + 1 : ℝ) ^ 2) {R : ℕ} (hR : 0 < R) :
    (∑' i : ℕ, h (i + R)) ≤ H / R := by
  exact ((summable_nat_add_iff R).mpr (summable_of_le h0 hbound)).tsum_le_tsum
    (fun i => hbound (i + R)) ((summable_nat_add_iff R).mpr (summable H))
    |>.trans (tsum_tail_le hH hR)

end LeanMachine.InverseSquareTail
