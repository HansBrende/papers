import Transpose.Statement
import TransposeFollowup.RationalHeight

/-! The padding generator has a quadratic-logarithmic input-size allowance.
A linear number of records may each use a linear number of bit-linear
arithmetic operations. This budget lemma does not construct those operations. -/

namespace TransposeFollowup
set_option autoImplicit false

theorem grid_size_bits (n : ℕ) : (n + 1).size ≤ Transpose.entryBits n + 2 := by
  have hn : n ≤ 2 ^ Transpose.entryBits n := by
    unfold Transpose.entryBits
    have := Nat.lt_log2_self (n := n - 1)
    omega
  have hp : 0 < 2 ^ Transpose.entryBits n := by positivity
  apply Nat.size_le.mpr
  rw [pow_add]
  norm_num
  omega

theorem linear_repetition_budget (A B n : ℕ) (hn : 1 ≤ n) :
    n * ((n + 1) * (A + B * (n + 1).size)) ≤
      2 * (A + 3 * B) * Transpose.inputLength n := by
  have hbits := grid_size_bits n
  have hb : 1 ≤ Transpose.entryBits n := by unfold Transpose.entryBits; omega
  have hwidth : A + B * (n + 1).size ≤ (A + 3 * B) * Transpose.entryBits n := by
    calc
      _ ≤ A + B * (Transpose.entryBits n + 2) := by gcongr
      _ ≤ (A + 3 * B) * Transpose.entryBits n := by nlinarith
  have hcount : n + 1 ≤ 2 * n := by omega
  calc
    _ ≤ n * ((2 * n) * ((A + 3 * B) * Transpose.entryBits n)) := by gcongr
    _ = 2 * (A + 3 * B) * Transpose.inputLength n := by
      unfold Transpose.inputLength
      ring

end TransposeFollowup
