import LeanMachine.WholeRow.WindowTwo

/-!
# Window-two target: compatibility import

The original `windowTwoBound`, `exists_cost_window_two_le` and square-case
declarations are now proved in `LeanMachine.WholeRow.WindowTwo`. There is
no remaining proof obligation in this file. The code-cardinality consumer
is `LeanMachine.WholeRow.OrderCode.card_le_window_two`.
-/
