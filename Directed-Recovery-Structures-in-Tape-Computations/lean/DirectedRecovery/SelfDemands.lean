import DirectedRecovery.IncidenceComponents
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Self-demands from disjoint one-edge transport

Each actual self-demand supplies a simple edge between its own two distinct
ports. These paths are vertex-disjoint without any incidence degree bound.
Only the native disjoint-path transport estimate remains a hypothesis.
-/

namespace DirectedRecovery

open Classical
set_option autoImplicit false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coordinates whose recovery neighborhood contains themselves. -/
def selfDemandCoordinates (N : V → Finset V) : Finset V :=
  Finset.univ.filter (fun p => p ∈ N p)

/-- The genuine own-port edge of a self-demand. -/
def selfDemandPath (N : V → Finset V) (i : selfDemandCoordinates N) :
    (pairedIncidenceGraph N).Walk (Sum.inl i.val) (Sum.inr i.val) :=
  SimpleGraph.Walk.cons (v := Sum.inr i.val)
    (show (pairedIncidenceGraph N).Adj (Sum.inl i.val) (Sum.inr i.val) from
      (Finset.mem_filter.mp i.property).2) .nil

theorem selfDemandPath_isPath (N : V → Finset V) (i : selfDemandCoordinates N) :
    (selfDemandPath N i).IsPath := by
  simp [selfDemandPath, SimpleGraph.Walk.cons_isPath_iff]

theorem selfDemandPath_length (N : V → Finset V) (i : selfDemandCoordinates N) :
    (selfDemandPath N i).length = 1 := rfl

/-- Distinct coordinates give disjoint two-port supports. -/
theorem selfDemandPaths_pairwiseDisjoint (N : V → Finset V) :
    (Set.univ : Set (selfDemandCoordinates N)).PairwiseDisjoint
      (fun i => (selfDemandPath N i).support.toFinset) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  cases v <;> simp_all [selfDemandPath]

/-- The finite self-demand consequence of the uniform one-edge transport
estimate. The hypothesis ranges over actual simple path families on arbitrary
coordinate subsets, and imposes no degree restriction. -/
theorem self_demands_count_of_disjoint_transport (N : V → Finset V) (M : ℝ)
    (htransport : ∀ S : Finset V,
      ∀ p : ∀ i : S, (pairedIncidenceGraph N).Walk (Sum.inl i.val) (Sum.inr i.val),
      (∀ i, (p i).IsPath) → (∀ i, (p i).length = 1) →
      (Set.univ : Set S).PairwiseDisjoint (fun i => (p i).support.toFinset) →
      (S.card : ℝ) ≤ M) :
    ((selfDemandCoordinates N).card : ℝ) ≤ M :=
  htransport (selfDemandCoordinates N) (selfDemandPath N)
    (selfDemandPath_isPath N) (selfDemandPath_length N)
    (selfDemandPaths_pairwiseDisjoint N)

end DirectedRecovery
