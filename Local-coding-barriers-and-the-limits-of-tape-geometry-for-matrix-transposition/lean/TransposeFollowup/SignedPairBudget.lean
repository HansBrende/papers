import TransposeFollowup.SignedPairRun
import TransposeFollowup.DenseOverlapScan

/-! The cost of the actual signed-pair comparison fits the dense row budget.
Surrounding updates, initialization and record generation are separate. -/

namespace TransposeFollowup.SignedPair
set_option autoImplicit false

theorem total_budget_le_input (A B n m : ℕ) (hn : 1 ≤ n)
    (hm : m ≤ A + B * (n + 1).size) :
    n * (n * (23 * m + 37)) ≤
      2 * ((23 * A + 37) + 3 * (23 * B)) * Transpose.inputLength n := by
  calc
    _ ≤ n * (n * ((23 * A + 37) + (23 * B) * (n + 1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      nlinarith
    _ ≤ _ := dense_scan_budget (23*A+37) (23*B) n hn

end TransposeFollowup.SignedPair
