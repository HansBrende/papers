import SoftRecovery.Decomposition
import DirectedReciprocity.ClassS

namespace SoftRecovery

open Finset HalfRate MotionDepthCodes DirectedReciprocity
set_option autoImplicit false

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The soft inequality on a relative Class S set; no validity assumption. -/
theorem classSOn_soft {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) {R : Finset V} (hR : ClassSOn N R) :
    2 * (h univ - h (univ \ R)) ≤
      (∑ v ∈ R, increment h (univ \ R) v) +
      ∑ v ∈ R, residual h N (univ \ R) v := by
  obtain ⟨pcs, hp⟩ := classSOn_decomp R hR
  simpa using decomp_ineq_soft hh hp

/-- Paper 10's entire Class S, with arbitrary recovery uncertainty. -/
theorem classS_soft {N : V → Finset V} {h : Finset V → ℝ}
    (hh : IsPolymatroid h) (hN : IsClassS N) :
    2 * h univ ≤ (∑ v, h {v}) + ∑ v, increment h (N v) v := by
  obtain ⟨pcs, hp⟩ := classS_decomp hN univ
  rw [sdiff_self] at hp
  exact soft_half hh hp

end SoftRecovery
