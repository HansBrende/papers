import LeanMachine.FiniteCodimension
import SharedDecoders.CapacityIntervals

/-! Forwarding names for the shared finite-codimension machinery. -/

namespace SharedDecoders

export LeanMachine.FiniteCodimension
  (finrank_comap_equiv
   finrank_inf_defect
   finrank_sup_defect
   finrank_finite_inf_defect
   finrank_double_kernel_support
   finrank_sup_comap_support)

end SharedDecoders
