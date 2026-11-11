import LeanMachine.FiniteBoundedDifferences
import SharedDecoders.CapacityMaskProbability

/-! Paper-local names for the generic finite probability library.
The implementation and proofs live in `lean-machine`; no proof is duplicated. -/

namespace SharedDecoders.CapacityMaskProbability

export LeanMachine.FiniteProbability (
  BoundedChanges boundedChanges_cons_tail boundedChanges_cons_head avg_exp_boundedChanges_fin
  avg_exp_boundedChanges prob_upper_of_mgf boundedDifferences_upper boundedDifferences_lower
)

namespace BoundedChanges
export LeanMachine.FiniteProbability.BoundedChanges (add const_mul finset_sum div_const)
end BoundedChanges

end SharedDecoders.CapacityMaskProbability
