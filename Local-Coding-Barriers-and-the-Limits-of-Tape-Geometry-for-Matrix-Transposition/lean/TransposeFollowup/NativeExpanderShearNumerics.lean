import Mathlib.Tactic.Linarith

/-! Absorb every setup, data-pass, and linking cost of the fixed native shear
controller into one constant times the raw input length. -/
namespace TransposeFollowup.NativeExpanderShearNumerics

set_option autoImplicit false

theorem total_budget_le (m W q A clock wordLength : ℕ)
    (hm : 1 ≤ m) (hW : 1 ≤ W)
    (hc : clock ≤ 1200 * W) (hl : wordLength ≤ m) :
    A * (2 * m * W) +
      (clock + 20 * wordLength + 2 * (4 * m * q) + m * (6 * q + 24) + 68 +
        2 * q * (6 * m * W + 9 * m + 17)) +
      (q * (8 * m * W + 8) + 24 * m * W + 28) + 2 ≤
      (A + 10000 * (q + 1)) * (2 * m * W) := by
  have hmW : m ≤ m * W := by nlinarith
  have hWm : W ≤ m * W := by nlinarith
  have hone : 1 ≤ m * W := by nlinarith
  have hqm : q * m ≤ q * (m * W) := Nat.mul_le_mul_left q hmW
  have hq : q ≤ q * (m * W) := by nlinarith
  nlinarith

end TransposeFollowup.NativeExpanderShearNumerics
