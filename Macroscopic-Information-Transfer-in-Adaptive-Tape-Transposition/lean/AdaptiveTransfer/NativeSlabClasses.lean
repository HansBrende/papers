import AdaptiveTransfer.ReplayMetadata
import AdaptiveTransfer.NativeTimelyData
import AdaptiveTransfer.NativeImportInformation

/-! Equal bounded metadata, with arbitrary input-dependent detailed traces,
gives an actual native replay class. The tag budget is derived from completed
long returns and every field equality comes from the computed metadata. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting
  NativeRelations Finset LeanMachine

namespace SlabObservation
variable {k T W N : ℕ} {τ τ' : Trace k}
  {g : SlabObservation τ T W N} {g' : SlabObservation τ' T W N}

theorem free_eq_of_encode_eq (he : g.encode = g'.encode) : g.free = g'.free :=
  congrArg ReplayMetadata.free he

theorem ell_eq_of_encode_eq (he : g.encode = g'.encode) : g.ell = g'.ell :=
  congrArg (fun m => m.ell.val) he

theorem start_eq_of_encode_eq (he : g.encode = g'.encode) : g.start = g'.start :=
  congrArg (fun m => m.start.val) he

theorem finish_eq_of_encode_eq (he : g.encode = g'.encode) : g.finish = g'.finish :=
  congrArg (fun m => m.finish.val) he

end SlabObservation

section Classes
variable {M : TM} {d b T W N H J : ℕ} {c : ℝ}
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (obs : ∀ X : D, SlabObservation (trace M (List.ofFn X.val)) T W N)
  (finish_le : ∀ X : D, (obs X).finish ≤ (trace M (List.ofFn X.val)).haltTime)
  (returns : ∀ X : D, (offCarrierReturns (trace M (List.ofFn X.val)).work
      (obs X).free (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
  (X₀ : D) (same : ∀ X : D, (obs X).encode = (obs X₀).encode)

private def classPrefix (X : D) : ExecutionPrefix M (List.ofFn X.val) (obs X₀).finish :=
  ExecutionPrefix.ofRun M (List.ofFn X.val) (obs X₀).finish fun t ht =>
    (timely_native_data (correct X)).2.1 t (lt_of_lt_of_le
      (by simpa only [SlabObservation.finish_eq_of_encode_eq (same X)] using ht) (finish_le X))

private theorem class_carrier (X : D) (t : ℕ)
    (ha : (obs X₀).start ≤ t) (ht : t < (obs X₀).finish) :
    t ∈ (obs X₀).times ↔
      ((classPrefix D correct obs finish_le X₀ same X).config t).workPos (obs X₀).free ∈
        Ico (obs X₀).ell ((obs X₀).ell + (W : ℤ)) := by
  change t ∈ (obs X₀).times ↔
    (run M (List.ofFn X.val) t).workPos (obs X₀).free ∈ _
  rw [workPos_eq_work, ← SlabObservation.free_eq_of_encode_eq (same X),
    ← (obs X).times_eq_of_encode_eq (same X)]
  simp only [SlabObservation.times, selectedSlab, mem_filter, mem_Ico,
    SlabObservation.start_eq_of_encode_eq (same X),
    SlabObservation.finish_eq_of_encode_eq (same X),
    SlabObservation.ell_eq_of_encode_eq (same X), ha, ht, true_and]

private theorem class_record (X : D) {r : ℕ} (hr : r ∈ runStarts (obs X₀).times) :
    (obs X).runRecord r (by rwa [(obs X).times_eq_of_encode_eq (same X)]) =
      (obs X₀).runRecord r hr :=
  (obs X).runRecord_eq_of_encode_eq (same X) _

include returns in
private theorem class_tags (X : D) :
    (recordSupport (fun _ => none)
      (incomingFields (classPrefix D correct obs finish_le X₀ same X) T H (obs X₀).times
        (replayEntry (obs X₀).times (obs X₀).finish (fun _t ht => (obs X₀).time_finish ht))
        (obs X₀).free)).card ≤ J := by
  have hb := incoming_support_le_returns (classPrefix D correct obs finish_le X₀ same X)
    T H (obs X₀).times
    (replayEntry (obs X₀).times (obs X₀).finish (fun _t ht => (obs X₀).time_finish ht))
    (obs X₀).free (fun _t ht => (obs X₀).time_finish ht)
    (fun _t ht => (replayEntry_spec (fun _t ht => (obs X₀).time_finish ht) ht).2.1)
  have hw : (fun h t => ((classPrefix D correct obs finish_le X₀ same X).config t).workPos h) =
      (trace M (List.ofFn X.val)).work := by
    funext h t
    exact workPos_eq_work h t
  rw [hw] at hb
  have hret : (offCarrierReturns (trace M (List.ofFn X.val)).work (obs X₀).free
      (trace M (List.ofFn X.val)).haltTime H).card ≤ J := by
    simpa only [SlabObservation.free_eq_of_encode_eq (same X)] using returns X
  exact hb.trans ((card_le_card (offCarrierReturns_mono _ _ H
    (by rw [← SlabObservation.finish_eq_of_encode_eq (same X)]; exact finish_le X))).trans hret)

/-- This class is constructed from native correct inputs and their computed
bounded metadata, with its support bound supplied by actual long returns. -/
noncomputable def constantSlabClass : NativeReplayClass M (d * d * b) (tposOf d b) where
  inputs := D
  horizon := (obs X₀).finish
  exec := classPrefix D correct obs finish_le X₀ same
  times := (obs X₀).times
  cells := Ico (obs X₀).ell ((obs X₀).ell + (W : ℤ))
  start := (obs X₀).start
  radius := H
  limit := T
  tags := J
  free := (obs X₀).free
  time_lt := fun _t ht => (obs X₀).time_finish ht
  time_start := fun _t ht => (obs X₀).time_start ht
  horizon_le := (obs X₀).finish_le
  carrier := class_carrier D correct obs finish_le X₀ same
  workEntry r h := (trace M (List.ofFn X₀.val)).work h r
  rawEntry := (trace M (List.ofFn X₀.val)).input
  rawLo := runRawLo (trace M (List.ofFn X₀.val)).input (obs X₀).times (obs X₀).finish
  rawHi := runRawHi (trace M (List.ofFn X₀.val)).input (obs X₀).times (obs X₀).finish
  outLo r := (appendList (trace M (List.ofFn X₀.val)) r).length
  outHi r := (appendList (trace M (List.ofFn X₀.val)) (runEnd (obs X₀).times (obs X₀).finish r)).length
  work_entry X r hr := by
    funext h
    change (run M (List.ofFn X.val) r).workPos h = _
    rw [workPos_eq_work]
    exact congrArg (fun v : RunMetadata M.k T => (v.work h).val) (class_record D obs X₀ same X hr)
  raw_entry X r hr := by
    change (run M (List.ofFn X.val) r).inPos = _
    rw [inPos_eq_input]
    exact congrArg (fun v : RunMetadata M.k T => v.raw.val) (class_record D obs X₀ same X hr)
  out_lo X r hr := by
    change (run M (List.ofFn X.val) r).outRev.length = _
    rw [native_output_count]
    exact congrArg (fun v : RunMetadata M.k T => v.outLo.val) (class_record D obs X₀ same X hr)
  out_hi X r hr := by
    change (run M (List.ofFn X.val) (runEnd (obs X₀).times (obs X₀).finish r)).outRev.length = _
    rw [native_output_count]
    have hh := congrArg (fun v : RunMetadata M.k T => v.outHi.val) (class_record D obs X₀ same X hr)
    simpa only [SlabObservation.runRecord, (obs X).times_eq_of_encode_eq (same X),
      SlabObservation.finish_eq_of_encode_eq (same X)] using hh
  extrema X r hr t ht := by
    change _ ≤ (run M (List.ofFn X.val) t).inPos ∧ (run M (List.ofFn X.val) t).inPos ≤ _
    rw [inPos_eq_input]
    have helo := congrArg (fun v : RunMetadata M.k T => v.rawLo.val) (class_record D obs X₀ same X hr)
    have hehi := congrArg (fun v : RunMetadata M.k T => v.rawHi.val) (class_record D obs X₀ same X hr)
    have hh := runRaw_extrema (x := (trace M (List.ofFn X.val)).input)
      (C := (obs X).times) (T := (obs X).finish) (r := r) (t := t)
      (by simpa only [(obs X).times_eq_of_encode_eq (same X),
        SlabObservation.finish_eq_of_encode_eq (same X)] using ht)
    simp only [SlabObservation.runRecord] at helo hehi
    rw [helo, hehi] at hh
    exact hh
  tag_bound := class_tags D correct obs finish_le returns X₀ same
  finish X := (trace M (List.ofFn X.val)).haltTime
  finish_ge X := by rw [← SlabObservation.finish_eq_of_encode_eq (same X)]; exact finish_le X
  output X := (timely_native_data (correct X)).2.2

/-- The native omitted set of the class is precisely the representative's
actual selected-slab omitted set, through its own complete halt horizon. -/
theorem constantSlabClass_omitted :
    (constantSlabClass D correct obs finish_le returns X₀ same).omitted =
    omittedSlabBits d b (trace M (List.ofFn X₀.val)).input
      (fun j => appendTime (trace M (List.ofFn X₀.val))
        (trace M (List.ofFn X₀.val)).haltTime j.val) (obs X₀).times := by
  have hP := (fibre_haltTime (mem_fibre.mpr rfl) (correct X₀)).2
  dsimp only [NativeReplayClass.omitted, constantSlabClass]
  have hout := recordedOrdinals_eq_outIn (trace M (List.ofFn X₀.val)) hP.ge
    (fun _t ht => ((obs X₀).time_finish ht).trans_le (finish_le X₀))
  have hraw := rawExtent_eq_visited (trace M (List.ofFn X₀.val)).abs_input_succ_sub_le
    (fun _t ht => (obs X₀).time_finish ht)
  rw [geometryOmitted, hraw]
  have hends : ∀ r ∈ runStarts (obs X₀).times,
      runEnd (obs X₀).times (obs X₀).finish r =
        runEnd (obs X₀).times (trace M (List.ofFn X₀.val)).haltTime r := by
    intro r hr
    have h₁ := runEnd_spec (fun _t ht => (obs X₀).time_finish ht) hr
    have h₂ := runEnd_spec (fun _t ht => ((obs X₀).time_finish ht).trans_le (finish_le X₀)) hr
    rcases lt_trichotomy (runEnd (obs X₀).times (obs X₀).finish r)
        (runEnd (obs X₀).times (trace M (List.ofFn X₀.val)).haltTime r) with hlt | heq | hgt
    · exact (h₁.2.2.1 (h₂.2.2.2 _ (mem_Ico.mpr ⟨h₁.1.le, hlt⟩))).elim
    · exact heq
    · exact (h₂.2.2.1 (h₁.2.2.2 _ (mem_Ico.mpr ⟨h₂.1.le, hgt⟩))).elim
  have hords : recordedOrdinals (d * d * b) (obs X₀).times
      (fun r => (appendList (trace M (List.ofFn X₀.val)) r).length)
      (fun r => (appendList (trace M (List.ofFn X₀.val))
        (runEnd (obs X₀).times (obs X₀).finish r)).length) =
      recordedOrdinals (d * d * b) (obs X₀).times
      (fun r => (appendList (trace M (List.ofFn X₀.val)) r).length)
      (fun r => (appendList (trace M (List.ofFn X₀.val))
        (runEnd (obs X₀).times (trace M (List.ofFn X₀.val)).haltTime r)).length) := by
    apply biUnion_congr rfl
    intro r hr
    dsimp only
    simp only [hends r hr]
  rw [hords, hout]
  simp only [omittedSlabBits, inCells, Set.mem_ofPred_eq]

end Classes
end AdaptiveTransfer
