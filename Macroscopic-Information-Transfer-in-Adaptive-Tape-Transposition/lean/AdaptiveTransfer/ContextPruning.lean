import LeanMachine.ContextPruning

/-! Paper-facing names for the shared finite weighted pruning theorem. -/

namespace AdaptiveTransfer

alias context_subset := LeanMachine.ContextPruning.exists_probability_context_subset
alias context_half_mass := LeanMachine.ContextPruning.exists_half_mass_context_subset
alias context_conditional_bound := LeanMachine.ContextPruning.conditional_mass_bound

end AdaptiveTransfer
