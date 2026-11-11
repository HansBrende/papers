import AdaptiveTransfer.SlabOmitted
import AdaptiveTransfer.LocalClassData

/-! Native slab classes for localized cuts. A finite maximum of actual return
counts supplies the unused import bound of the existing class API; no
small-return condition is imposed and no import field is charged. -/

namespace AdaptiveTransfer
open Transpose MergeDepth BoundedNesting NativeRelations Finset

section Classes
variable {M : TM} {d b T W N H : ℕ} {c : ℝ}
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (obs : ∀ X : D, SlabObservation (trace M (List.ofFn X.val)) T W N)
  (finish_le : ∀ X : D, (obs X).finish ≤ (trace M (List.ofFn X.val)).haltTime)
  (X₀ : D) (same : ∀ X : D, (obs X).encode = (obs X₀).encode)

noncomputable def unrestrictedReturnCap : ℕ :=
  univ.sup fun X : D => (offCarrierReturns (trace M (List.ofFn X.val)).work
    (obs X).free (trace M (List.ofFn X.val)).haltTime H).card

theorem le_unrestrictedReturnCap (X : D) :
    (offCarrierReturns (trace M (List.ofFn X.val)).work (obs X).free
      (trace M (List.ofFn X.val)).haltTime H).card ≤ unrestrictedReturnCap (H := H) D obs :=
  le_sup (f := fun X : D => (offCarrierReturns (trace M (List.ofFn X.val)).work
    (obs X).free (trace M (List.ofFn X.val)).haltTime H).card) (mem_univ X)

noncomputable def unrestrictedSlabClass : NativeReplayClass M (d * d * b) (tposOf d b) :=
  constantSlabClass D correct obs finish_le (le_unrestrictedReturnCap (H := H) D obs) X₀ same

theorem unrestrictedSlabClass_omitted (X : D) :
    (unrestrictedSlabClass (H := H) D correct obs finish_le X₀ same).omitted =
      (obs X).omittedGeometry (tposOf d b) :=
  ((obs X).omittedGeometry_eq_of_encode_eq (tposOf d b) (same X)).symm

theorem unrestrictedSlabCompletion
    (halt_le : ∀ X : D, (trace M (List.ofFn X.val)).haltTime ≤ T) :
    (unrestrictedSlabClass (H := H) D correct obs finish_le X₀ same).Completion where
  active X := (timely_native_data (correct X)).2.1
  finish_le := halt_le
  outer_start := (obs X₀).start_le

end Classes
end AdaptiveTransfer
