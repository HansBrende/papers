import AdaptiveTransfer.NativeClusterClasses
import AdaptiveTransfer.CoreLocalData

/-! Native slab classes for localized cuts. A finite maximum of actual return
counts supplies the unused import bound of the existing class API; no
small-return condition is imposed and no import field is charged. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

section Classes
variable {M : TM} {d b T W N H j : ℕ} {c error : ℝ}
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (charts : ∀ X : D, ClusterChart (trace M (List.ofFn X.val)).work
    (trace M (List.ofFn X.val)).haltTime error)
  (obs : ∀ X : D, ClusterObservation (charts X) T W N j)
  (X₀ : D) (same : ∀ X : D, (obs X).encode = (obs X₀).encode)

noncomputable def unrestrictedClusterReturnCap : ℕ :=
  univ.sup fun X : D => (offClusterReturns (trace M (List.ofFn X.val)).work
    (charts X).included (trace M (List.ofFn X.val)).haltTime H).card

theorem le_unrestrictedClusterReturnCap (X : D) :
    (offClusterReturns (trace M (List.ofFn X.val)).work (charts X).included
      (trace M (List.ofFn X.val)).haltTime H).card ≤ unrestrictedClusterReturnCap (H := H) D charts :=
  le_sup (f := fun X : D => (offClusterReturns (trace M (List.ofFn X.val)).work
    (charts X).included (trace M (List.ofFn X.val)).haltTime H).card) (mem_univ X)

noncomputable def unrestrictedClusterClass : CoreReplayClass M (d * d * b) (tposOf d b) :=
  constantClusterClass D correct charts obs (le_unrestrictedClusterReturnCap (H := H) D charts) X₀ same

theorem unrestrictedClusterClass_omitted (X : D) :
    (unrestrictedClusterClass (H := H) D correct charts obs X₀ same).omitted =
      (obs X).omittedGeometry (tposOf d b) :=
  ((obs X).omittedGeometry_eq_of_encode_eq (tposOf d b) (same X)).symm

theorem unrestrictedClusterCompletion
    (halt_le : ∀ X : D, (trace M (List.ofFn X.val)).haltTime ≤ T) :
    (unrestrictedClusterClass (H := H) D correct charts obs X₀ same).Completion where
  active X := (timely_native_data (correct X)).2.1
  finish_le := halt_le
  outer_start := (obs X₀).start_le

end Classes
end AdaptiveTransfer
