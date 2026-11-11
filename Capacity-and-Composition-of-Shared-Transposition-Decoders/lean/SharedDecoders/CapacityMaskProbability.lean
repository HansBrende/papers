import LeanMachine.FiniteUniformProbability

/-! Paper-local names for the generic finite probability library.
The implementation and proofs live in `lean-machine`; no proof is duplicated. -/

namespace SharedDecoders.CapacityMaskProbability

export LeanMachine.FiniteProbability (
  avg_div avg_finset_sum
  avg avg_eq_sum_div_card avg_const avg_add
  avg_sub avg_const_mul avg_mul_const avg_neg
  avg_sum avg_mono avg_nonneg avg_le
  le_avg avg_equiv avg_product avg_cons
  uniform_integral_eq_avg avg_exp_centered_le prob prob_nonneg
  prob_le_one prob_mono prob_eq_card prob_exists_le_sum
)

end SharedDecoders.CapacityMaskProbability
