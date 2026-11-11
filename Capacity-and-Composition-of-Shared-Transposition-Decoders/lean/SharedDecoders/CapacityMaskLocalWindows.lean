import LeanMachine.FiniteUniformWindows
import SharedDecoders.CapacityMaskBoundedDifferences

/-! Paper-local names for the generic finite probability library.
The implementation and proofs live in `lean-machine`; no proof is duplicated. -/

namespace SharedDecoders.CapacityMaskProbability

export LeanMachine.FiniteProbability (
  avg_restrict prob_restrict prob_eq_value prob_pattern
  prob_or_of_disjoint windowSum windowSum_mean windowSum_boundedChanges
)

end SharedDecoders.CapacityMaskProbability
