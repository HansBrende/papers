import LeanMachine.WholeRow.OrderAverage

/-!
# Compatibility entry point: the proved row-order window bound

The former obligations `LeanMachine.WholeRow.AcyclicOrder.exists_cost_window_le`
and `minimumCost_window_le` are now theorems in the shared library, with the
same statements and no admitted proof. The maintained proof is in
`LeanMachine.WholeRow.OrderAverage`; the code-cardinality and uniform-rate
adapters are in Paper 21's `MatrixCoding.KnownBounds`.
-/
