import TransposeFollowup.RepeatedAddRun
import TransposeFollowup.LinearGenerationBudget

/-! Apply the original input-size budget to the assembled native machine,
including its physical counter, calls, jumps and recycled scratch storage. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
set_option autoImplicit false

theorem budget_le_record (C A B n : ℕ) (fuel x : List Bool)
    (hN : Counter.value fuel ≤ C * (n + 1))
    (hx : x.length ≤ A + B * (n + 1).size)
    (hf : fuel.length ≤ A + B * (n + 1).size) :
    budget fuel x ≤ (n + 1) *
      ((18 * C + 4) * A + 39 * C + 8 + (18 * C + 4) * B * (n + 1).size) := by
  let W := A + B * (n + 1).size
  have hbase : budget fuel x ≤ C * (n + 1) * (18 * W + 39) + (8 + 4 * W) := by
    calc
      budget fuel x = Counter.value fuel * (18 * x.length + 39) + (8 + 4 * fuel.length) := by
        unfold budget
        ring
      _ ≤ C * (n + 1) * (18 * W + 39) + (8 + 4 * W) := by gcongr
  have htail : 8 + 4 * W ≤ (n + 1) * (8 + 4 * W) :=
    Nat.le_mul_of_pos_left _ (by omega)
  calc
    _ ≤ C * (n + 1) * (18 * W + 39) + (8 + 4 * W) := hbase
    _ ≤ C * (n + 1) * (18 * W + 39) + (n + 1) * (8 + 4 * W) := by omega
    _ = _ := by dsimp [W]; ring

/-- A linear number of these native calls fits the original matrix input
length when the multiplier is O(n) and the two stored widths are O(log n).
This is only their cost: loading/generation around the calls is separate. -/
theorem total_budget_le_input (C A B n : ℕ) (hn : 1 ≤ n) (fuel x : List Bool)
    (hN : Counter.value fuel ≤ C * (n + 1))
    (hx : x.length ≤ A + B * (n + 1).size)
    (hf : fuel.length ≤ A + B * (n + 1).size) :
    n * budget fuel x ≤
      2 * (((18 * C + 4) * A + 39 * C + 8) + 3 * ((18 * C + 4) * B)) *
        Transpose.inputLength n := by
  exact (Nat.mul_le_mul_left n (budget_le_record C A B n fuel x hN hx hf)).trans
    (linear_repetition_budget ((18 * C + 4) * A + 39 * C + 8) ((18 * C + 4) * B) n hn)

end TransposeFollowup.RepeatedAdd
