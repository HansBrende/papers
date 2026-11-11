import AdaptiveTransfer.ClusterMetadata
import AdaptiveTransfer.ClusterNativeGeometry
import AdaptiveTransfer.CoreReplayClass
import AdaptiveTransfer.SlabOmitted

/-! Actual multi-core replay classes from computed rounded-chart metadata.
Charts and signs may vary by input; equality of the finite metadata recovers
only the selected sets and paid endpoints needed by native replay. -/

namespace AdaptiveTransfer
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth BoundedNesting
  NativeRelations Finset LeanMachine

namespace ClusterObservation
variable {k L T W N j : ℕ} {J : ℝ} {τ : Trace k} {chart : ClusterChart τ.work L J}
  (g : ClusterObservation chart T W N j)

noncomputable def omittedGeometry {P : ℕ} (π : Fin P → Fin P) : Finset (Fin P) :=
  geometryOmitted π g.times (fun r => (appendList τ r).length)
    (fun r => (appendList τ (runEnd g.times g.finish r)).length)
    (runRawLo τ.input g.times g.finish) (runRawHi τ.input g.times g.finish)

theorem omittedGeometry_eq_of_encode_eq {P L' : ℕ} {J' : ℝ} {τ' : Trace k}
    {chart' : ClusterChart τ'.work L' J'} (π : Fin P → Fin P)
    {h : ClusterObservation chart' T W N j} (he : g.encode = h.encode) :
    g.omittedGeometry π = h.omittedGeometry π := by
  have hC := g.times_eq_of_encode_eq he
  have hfinish := g.finish_eq_of_encode_eq he
  unfold omittedGeometry
  rw [← hC, ← hfinish]
  apply geometryOmitted_congr_records
  intro r hr
  have hh := g.runRecord_eq_of_encode_eq he hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun v : RunMetadata k T => v.outLo.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.outHi.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.rawLo.val) hh
  · simpa only [runRecord, ← hC, ← hfinish] using congrArg (fun v : RunMetadata k T => v.rawHi.val) hh

theorem omittedGeometry_eq_literal {d b finish : ℕ}
    (hfinish : g.finish ≤ finish) (hP : d * d * b ≤ (appendList τ finish).length) :
    g.omittedGeometry (tposOf d b) =
      omittedSlabBits d b τ.input (fun j => appendTime τ finish j.val) g.times := by
  have hCT : ∀ t ∈ g.times, t < finish := fun t ht => (g.time_finish ht).trans_le hfinish
  have he : g.omittedGeometry (tposOf d b) =
      geometryOmitted (tposOf d b) g.times (fun r => (appendList τ r).length)
        (fun r => (appendList τ (runEnd g.times finish r)).length)
        (runRawLo τ.input g.times finish) (runRawHi τ.input g.times finish) := by
    apply geometryOmitted_congr_records
    intro r hr
    have he := runEnd_eq_of_time_bounds (fun _t ht => g.time_finish ht) hCT hr
    exact ⟨rfl, by rw [he], by simp only [runRawLo, he], by simp only [runRawHi, he]⟩
  exact he.trans (geometryOmitted_eq_omittedSlabBits τ hP hCT)

end ClusterObservation

section Classes
variable {M : TM} {d b T W N H J j : ℕ} {c error : ℝ}
  (D : Finset (Fin (d * d * b) → Bool))
  (correct : ∀ X : D, TransposesInput M d b c X.val)
  (charts : ∀ X : D, ClusterChart (trace M (List.ofFn X.val)).work
    (trace M (List.ofFn X.val)).haltTime error)
  (obs : ∀ X : D, ClusterObservation (charts X) T W N j)
  (returns : ∀ X : D, (offClusterReturns (trace M (List.ofFn X.val)).work
    (charts X).included (trace M (List.ofFn X.val)).haltTime H).card ≤ J)
  (X₀ : D) (same : ∀ X : D, (obs X).encode = (obs X₀).encode)

private def classPrefix (X : D) : ExecutionPrefix M (List.ofFn X.val) (obs X₀).finish :=
  ExecutionPrefix.ofRun M (List.ofFn X.val) (obs X₀).finish fun t ht =>
    (timely_native_data (correct X)).2.1 t (lt_of_lt_of_le
      (by simpa only [(obs X).finish_eq_of_encode_eq (same X)] using ht) (obs X).live_le)

include obs same in
private theorem class_included (X : D) : (charts X).included = (charts X₀).included := by
  simp only [ClusterChart.included, (obs X).signature_eq_of_encode_eq (same X)]

private theorem class_outside (X : D) (t : ℕ)
    (ha : (obs X₀).start ≤ t) (ht : t < (obs X₀).finish) (htC : t ∉ (obs X₀).times)
    (h : Fin M.k) (_hh : h ∈ (charts X₀).included) :
    ((classPrefix D correct charts obs X₀ same X).config t).workPos h ∉
      (charts X₀).core (obs X₀).ell W j h := by
  change (run M (List.ofFn X.val) t).workPos h ∉ _
  rw [workPos_eq_work, ← (obs X).core_eq_of_encode_eq (same X) h]
  have hat : (obs X).start ≤ t := by rwa [(obs X).start_eq_of_encode_eq (same X)]
  have htf : t < (obs X).finish := by rwa [(obs X).finish_eq_of_encode_eq (same X)]
  have hn : t ∉ (obs X).times := by rwa [(obs X).times_eq_of_encode_eq (same X)]
  apply (charts X).outside_avoids (htf.trans_le (obs X).live_le) (obs X).error_le
  have hs : ¬ ((obs X).ell ≤ (charts X).carrier t ∧ (charts X).carrier t < (obs X).ell + W) := by
    intro hs
    exact hn (mem_filter.mpr ⟨mem_Ico.mpr ⟨hat, htf⟩, hs⟩)
  omega

private theorem class_selected (X : D) (t : ℕ) (ht : t ∈ (obs X₀).times)
    (h : Fin M.k) (hh : h ∈ (charts X₀).included) :
    ((classPrefix D correct charts obs X₀ same X).config t).workPos h ∈
      (charts X₀).core (obs X₀).ell W j h ∪ (charts X₀).fringe (obs X₀).ell W j h := by
  change (run M (List.ofFn X.val) t).workPos h ∈ _
  rw [workPos_eq_work, ← (obs X).core_eq_of_encode_eq (same X) h,
    ← (obs X).fringe_eq_of_encode_eq (same X) h]
  have ht' : t ∈ (obs X).times := by rwa [(obs X).times_eq_of_encode_eq (same X)]
  apply (charts X).selected_read ((obs X).time_live ht') (obs X).error_le ((obs X).selected ht')
  have hinc := class_included D charts obs X₀ same X
  rw [← hinc] at hh
  exact (mem_filter.mp hh).2

private theorem class_record (X : D) {r : ℕ} (hr : r ∈ runStarts (obs X₀).times) :
    (obs X).runRecord r (by rwa [(obs X).times_eq_of_encode_eq (same X)]) =
      (obs X₀).runRecord r hr := (obs X).runRecord_eq_of_encode_eq (same X) _

include returns in
private theorem class_tags (X : D) :
    (recordSupport (fun _ => none)
      (clusterIncomingFields (classPrefix D correct charts obs X₀ same X) T H (obs X₀).times
        (replayEntry (obs X₀).times (obs X₀).finish (fun _t ht => (obs X₀).time_finish ht))
        (charts X₀).included)).card ≤ J := by
  have hb := cluster_incoming_support_le_returns (classPrefix D correct charts obs X₀ same X)
    T H (obs X₀).times
    (replayEntry (obs X₀).times (obs X₀).finish (fun _t ht => (obs X₀).time_finish ht))
    (charts X₀).included (fun _t ht => (obs X₀).time_finish ht)
    (fun _t ht => (replayEntry_spec (fun _t ht => (obs X₀).time_finish ht) ht).2.1)
  have hw : (fun h t => ((classPrefix D correct charts obs X₀ same X).config t).workPos h) =
      (trace M (List.ofFn X.val)).work := by
    funext h t
    exact workPos_eq_work h t
  rw [hw, ← class_included D charts obs X₀ same X] at hb
  have hsub : offClusterReturns (trace M (List.ofFn X.val)).work (charts X).included (obs X₀).finish H ⊆
      offClusterReturns (trace M (List.ofFn X.val)).work (charts X).included
        (trace M (List.ofFn X.val)).haltTime H := by
    have hTU : (obs X₀).finish ≤ (trace M (List.ofFn X.val)).haltTime := by
      rw [← (obs X).finish_eq_of_encode_eq (same X)]
      exact (obs X).live_le
    intro e he
    obtain ⟨hh, hfree, hfar⟩ := mem_filter.mp he
    have hop := mem_allHops.mp hh
    exact mem_filter.mpr ⟨mem_allHops.mpr ⟨hop.1, hop.2.1.trans_le hTU, hop.2.2⟩, hfree, hfar⟩
  simpa only [class_included D charts obs X₀ same X] using
    hb.trans ((card_le_card hsub).trans (returns X))

/-- Constructed from actual correct inputs and actual chart observations.
Every class field, including imported-symbol support, is derived natively. -/
noncomputable def constantClusterClass : CoreReplayClass M (d * d * b) (tposOf d b) where
  inputs := D
  horizon := (obs X₀).finish
  exec := classPrefix D correct charts obs X₀ same
  times := (obs X₀).times
  cluster := (charts X₀).included
  core := (charts X₀).core (obs X₀).ell W j
  fringe := (charts X₀).fringe (obs X₀).ell W j
  start := (obs X₀).start
  radius := H
  limit := T
  tags := J
  time_lt := fun _t ht => (obs X₀).time_finish ht
  time_start := fun _t ht => (obs X₀).time_start ht
  horizon_le := (obs X₀).finish_le
  outside := class_outside D correct charts obs X₀ same
  selected := class_selected D correct charts obs X₀ same
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
    exact congrArg (fun v : RunMetadata M.k T => (v.work h).val) (class_record D charts obs X₀ same X hr)
  raw_entry X r hr := by
    change (run M (List.ofFn X.val) r).inPos = _
    rw [inPos_eq_input]
    exact congrArg (fun v : RunMetadata M.k T => v.raw.val) (class_record D charts obs X₀ same X hr)
  out_lo X r hr := by
    change (run M (List.ofFn X.val) r).outRev.length = _
    rw [native_output_count]
    exact congrArg (fun v : RunMetadata M.k T => v.outLo.val) (class_record D charts obs X₀ same X hr)
  out_hi X r hr := by
    change (run M (List.ofFn X.val) (runEnd (obs X₀).times (obs X₀).finish r)).outRev.length = _
    rw [native_output_count]
    have hh := congrArg (fun v : RunMetadata M.k T => v.outHi.val) (class_record D charts obs X₀ same X hr)
    simpa only [ClusterObservation.runRecord, (obs X).times_eq_of_encode_eq (same X),
      (obs X).finish_eq_of_encode_eq (same X)] using hh
  extrema X r hr t ht := by
    change _ ≤ (run M (List.ofFn X.val) t).inPos ∧ (run M (List.ofFn X.val) t).inPos ≤ _
    rw [inPos_eq_input]
    have helo := congrArg (fun v : RunMetadata M.k T => v.rawLo.val) (class_record D charts obs X₀ same X hr)
    have hehi := congrArg (fun v : RunMetadata M.k T => v.rawHi.val) (class_record D charts obs X₀ same X hr)
    have hh := runRaw_extrema (x := (trace M (List.ofFn X.val)).input)
      (C := (obs X).times) (T := (obs X).finish) (r := r) (t := t)
      (by simpa only [(obs X).times_eq_of_encode_eq (same X), (obs X).finish_eq_of_encode_eq (same X)] using ht)
    simp only [ClusterObservation.runRecord] at helo hehi
    rw [helo, hehi] at hh
    exact hh
  tag_bound := class_tags D correct charts obs returns X₀ same
  finish X := (trace M (List.ofFn X.val)).haltTime
  finish_ge X := by rw [← (obs X).finish_eq_of_encode_eq (same X)]; exact (obs X).live_le
  output X := (timely_native_data (correct X)).2.2

theorem constantClusterClass_omitted :
    (constantClusterClass D correct charts obs returns X₀ same).omitted =
      (obs X₀).omittedGeometry (tposOf d b) := rfl

end Classes
end AdaptiveTransfer
