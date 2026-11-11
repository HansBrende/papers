import LeanMachine.OrderConflictChart

/-! Paper-facing names for normalized finite order-conflict charts. The complete
construction, including the exact maximum defining the conflict, is shared. -/

namespace AdaptiveTransfer

alias finite_order_chart := LeanMachine.OrderConflictChart.exists_order_conflict_chart
alias order_conflict_le_two_error := LeanMachine.OrderConflictChart.orderConflict_le_two_error
alias coordinate_conflict_chart := LeanMachine.OrderConflictChart.exists_coordinate_chart

end AdaptiveTransfer
