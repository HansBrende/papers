import HalfRate.N3
import SoftRecovery.Decomposition

/-!
# Reuse of the existing nonlinear subcubic half bound

Paper 7 already proves the weighted half bound for all valid polymatroids on
triangle-free subcubic graphs. Its existing decomposition, combined with the
soft-recovery memo, also retains each recovery error with coefficient one.
This file only composes those results and weakens the helper sets by
diminishing returns. No new graph theorem is proved here.

The helper sets may be asymmetric and recovery need not be linear. They must
lie in a common triangle-free graph of undirected degree at most three.
The directed degree/four-arc variants from the separate rank argument are
not asserted for arbitrary polymatroids. No native extraction is supplied.
-/

namespace LeanBacklog.SubcubicReuse

open Finset MotionDepthCodes SoftRecovery
open scoped BigOperators
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The existing exact weighted half bound, retained as a reuse endpoint. -/
theorem rateBound_subcubic (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    RateBound (nbhd G) (1 / 2) :=
  HalfRate.rateBound_n3 hcf hdeg

/-- Compose the existing shortest-cycle decomposition with the existing
soft theorem. There are no recovery equalities or singleton caps. -/
theorem soft_half_subcubic (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) :
    2 * h univ ≤ (∑ v, h {v}) + ∑ v, increment h (nbhd G v) v := by
  have hdeg' : ∀ v, (nbhd G v).card ≤ 3 := fun v => by
    have hv := hdeg v
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter] at hv
    exact hv
  obtain ⟨pcs, hD⟩ := HalfRate.n3_decomp hcf hdeg' univ
  rw [sdiff_self] at hD
  exact SoftRecovery.soft_half hh hD

/-- Directed helper subsets only increase their charged recovery errors. -/
theorem soft_half_of_helpers_subset
    (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3)
    (N : V → Finset V) (hN : ∀ v, N v ⊆ nbhd G v)
    {h : Finset V → ℝ} (hh : IsPolymatroid h) :
    2 * h univ ≤ (∑ v, h {v}) + ∑ v, increment h (N v) v :=
  (soft_half_subcubic G hcf hdeg hh).trans
    (add_le_add le_rfl (sum_le_sum fun v _ => increment_antitone hh (hN v) v))

/-- Exact recovery removes the errors, including for asymmetric helpers.
`RateBound` quantifies over all valid polymatroids, not only linear codes. -/
theorem rateBound_of_helpers_subset
    (hcf : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3)
    (N : V → Finset V) (hN : ∀ v, N v ⊆ nbhd G v) :
    RateBound N (1 / 2) := by
  intro h hh hv
  have hs := soft_half_of_helpers_subset G hcf hdeg N hN hh
  have he : ∀ v, increment h (N v) v = 0 := fun v => by
    rw [increment, hv v, sub_self]
  simp only [he, sum_const_zero, add_zero] at hs
  linarith

end LeanBacklog.SubcubicReuse

#print axioms LeanBacklog.SubcubicReuse.rateBound_subcubic
#print axioms LeanBacklog.SubcubicReuse.soft_half_subcubic
#print axioms LeanBacklog.SubcubicReuse.soft_half_of_helpers_subset
#print axioms LeanBacklog.SubcubicReuse.rateBound_of_helpers_subset
