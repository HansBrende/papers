import Mathlib.Tactic

/-! Scalar accounting for the sharp finite cyclic-freezing bound. -/

namespace SourceCovers

open Finset
open scoped BigOperators

/-- Sum the actual per-column counts while retaining the stripe correction.
The radii are arbitrary here; their motion bound is supplied separately. -/
theorem cyclic_column_accounting {d b : ℕ} (hd : 0 < d)
    (A Q : ℕ → ℝ) (r : ℕ → ℕ)
    (hcolumn : ∀ j < d, (d : ℝ) * b * A j - (2 * r j + 1 / 2) / d -
      b * (1 - 1 / (d : ℝ)) / 2 ≤ Q j) :
    (d : ℝ) * b * (∑ j ∈ range d, A j) -
      2 * (∑ j ∈ range d, (r j : ℝ)) / d -
      ((d : ℝ) * b - b + 1) / 2 ≤ ∑ j ∈ range d, Q j := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have h := sum_le_sum fun j (hj : j ∈ range d) => hcolumn j (mem_range.mp hj)
  have he : (∑ j ∈ range d, ((d : ℝ) * b * A j -
        (2 * r j + 1 / 2) / d - b * (1 - 1 / (d : ℝ)) / 2)) =
      (d : ℝ) * b * (∑ j ∈ range d, A j) -
        2 * (∑ j ∈ range d, (r j : ℝ)) / d -
        ((d : ℝ) * b - b + 1) / 2 := by
    simp only [sum_sub_distrib, ← mul_sum, ← sum_div, sum_add_distrib,
      sum_const, card_range, nsmul_eq_mul]
    field_simp
    ring
  exact he ▸ h

end SourceCovers
