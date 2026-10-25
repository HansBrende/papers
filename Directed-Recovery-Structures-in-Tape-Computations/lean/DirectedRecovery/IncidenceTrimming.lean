import LeanMachine.IncidenceTrimming

/-!
# The finite counting part of paid degree reduction

This proves the finite incidence statement once the receiver-degree bound is
given. It does not formalize the native dependency-cone bound or the asymptotic
paired-distance theorem used later in the manuscript's corollary.
-/

namespace DirectedRecovery

open LeanMachine.IncidenceTrimming

/-- Heavy input reuse can be paid for by deleting the corresponding coordinates;
both incidence degrees of the retained relation are then bounded. -/
theorem paid_degree_trimming {V : Type*} [Fintype V] [DecidableEq V]
    (E : V → V → Prop) [DecidableRel E] (M B : ℕ) (hM : 0 < M)
    (hB : ∀ q, rightDegree E q ≤ B) :
    (heavy E M).card ≤ (B * Fintype.card V) / M ∧
      (∀ p ∈ retained E M, leftDegreeOn E (retained E M) p ≤ max B M) ∧
      (∀ q ∈ retained E M, rightDegreeOn E (retained E M) q ≤ max B M) :=
  degree_trimming E M B hM hB

end DirectedRecovery
