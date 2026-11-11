import AdaptiveTransfer.TransferFIFO
import AdaptiveTransfer.NativeTimelyData

/-! Correct designated raw-bit roots on an actual common simulator trace.
Only finite OutputsTranspose is required. Different inputs may have different
source traces and source halting times; their complete simulator trace fixes
its own common horizon and append ordinals. -/
namespace AdaptiveTransfer.TransferCorrect
open Transpose Transpose.Tape Transpose.Tape.Impl MergeDepth Finset
open TapeStorageRates TapeStorageRates.Native AdaptiveTransfer.TransferFIFO

/-- Whole-word correctness at any actual source halt, without a time budget. -/
theorem correct_source_word {M : TM} {d b t : ℕ} {X : Fin (d * d * b) → Bool}
    (H : HaltsAt M (List.ofFn X) t) (hcorrect : OutputsTranspose M d b X) :
    (run M (List.ofFn X) t).outRev.reverse = List.ofFn (fun j => X (tposOf d b j)) := by
  obtain ⟨u, hhalt, hlen, hout⟩ := hcorrect.output
  have he : u = t := haltsAt_unique hhalt H
  subst u
  apply List.ext_getElem?
  intro n
  by_cases hn : n < d * d * b
  · have hh := hout (tposOf d b ⟨n, hn⟩)
    have ht : Transpose.Tape.tpos d b (tposOf d b ⟨n, hn⟩) = n :=
      congrArg Fin.val (tposOf_tposOf d b ⟨n, hn⟩)
    rw [ht] at hh
    simpa only [List.getElem?_ofFn, dite_eq_left hn] using hh
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem correct_source_count {M : TM} {d b t : ℕ} {X : Fin (d * d * b) → Bool}
    (H : HaltsAt M (List.ofFn X) t) (hcorrect : OutputsTranspose M d b X) :
    outputCount M (List.ofFn X) t = d * d * b := by
  have hh := congrArg List.length (correct_source_word H hcorrect)
  simpa only [outputCount, List.length_reverse, List.length_ofFn] using hh

/-- Literal append-time correctness follows from the final word and exact
ordinal counter. It does not identify roots by their Boolean values. -/
theorem sourceRoot_output {M : TM} {P t : ℕ} {w : List Bool} (f : Fin P → Bool)
    (hout : (run M w t).outRev.reverse = List.ofFn f) (i : Fin P) :
    sourceRoot M w t i.val < t ∧ (outBit M w (sourceRoot M w t i.val)).getD false = f i := by
  have hlen : outputCount M w t = P := by
    simpa only [outputCount, List.length_reverse, List.length_ofFn] using congrArg List.length hout
  have hi : i.val < outputCount M w t := hlen ▸ i.isLt
  have hc := sourceRoot_counts M w hi
  have hi' : i.val < (appendList (trace M w) t).length := by
    simpa only [outputCount, outRev_length_eq_appendList] using hi
  have hmem : sourceRoot M w t i.val ∈ appendList (trace M w) t := by
    rw [sourceRoot, appendTime_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hflag : (outBit M w (sourceRoot M w t i.val)).isSome := by
    rw [outBit_isSome_eq]
    exact (List.mem_filter.mp hmem).2
  have he := output_nth_eq_outBit w hc.1 hflag
  change (nth (run M w t).outRev.reverse (outputCount M w (sourceRoot M w t i.val))) = _ at he
  rw [hout, hc.2.1, nth_ofFn f i.isLt] at he
  exact ⟨hc.1, by simpa only [Option.getD_some] using congrArg (fun x => x.getD false) he.symm⟩

theorem correct_simulator_word {M : TM} {d b s t : ℕ} {X : Fin (d * d * b) → Bool}
    (hs : 0 < s) (H : HaltsAt M (List.ofFn X) t) (hcorrect : OutputsTranspose M d b X) :
    (run (machine M hs) (List.ofFn X) (alignedTime s t)).outRev.reverse =
      List.ofFn (fun j => X (tposOf d b j)) :=
  (congrArg List.reverse (simulates_halt M hs _ H).2).trans (correct_source_word H hcorrect)

theorem correct_simulator_root {M : TM} {d b s t : ℕ} {X : Fin (d * d * b) → Bool}
    (hs : 0 < s) (H : HaltsAt M (List.ofFn X) t) (hcorrect : OutputsTranspose M d b X)
    (p : Fin (d * d * b)) :
    simulatorRoot M hs (List.ofFn X) t (tposOf d b p).val < alignedTime s t ∧
      (outBit (machine M hs) (List.ofFn X)
        (simulatorRoot M hs (List.ofFn X) t (tposOf d b p).val)).getD false = X p := by
  simpa only [simulatorRoot, tposOf_tposOf] using
    sourceRoot_output (fun j => X (tposOf d b j)) (correct_simulator_word hs H hcorrect) (tposOf d b p)

/-- Finite correct inputs halt at their own canonical source time. -/
theorem correct_haltsAt {M : TM} {d b : ℕ} {X : Fin (d * d * b) → Bool}
    (hcorrect : OutputsTranspose M d b X) :
    HaltsAt M (List.ofFn X) (trace M (List.ofFn X)).haltTime := by
  obtain ⟨u, hu, _⟩ := hcorrect.output
  have hτ := (haltsAt_iff_trace u).mp hu
  exact (haltsAt_iff_trace _).mpr
    ((trace M (List.ofFn X)).haltsAt_haltTime ⟨u, hτ.2⟩)

/-- Complete common simulator traces fix the simulator horizon, while the
original successful executions may stop at different source times. -/
theorem common_simulator_word {M : TM} {d b s t : ℕ} {X Y : Fin (d * d * b) → Bool}
    (hs : 0 < s) (H : HaltsAt M (List.ofFn X) t) (hcorrectY : OutputsTranspose M d b Y)
    (htrace : trace (machine M hs) (List.ofFn Y) = trace (machine M hs) (List.ofFn X)) :
    (run (machine M hs) (List.ofFn Y) (alignedTime s t)).outRev.reverse =
      List.ofFn (fun j => Y (tposOf d b j)) := by
  let u := (trace M (List.ofFn Y)).haltTime
  have HY : HaltsAt M (List.ofFn Y) u := correct_haltsAt hcorrectY
  have hY := (haltsAt_iff_trace _).mp (simulates_halt M hs _ HY).1
  have hX := (haltsAt_iff_trace _).mp (simulates_halt M hs _ H).1
  rw [htrace] at hY
  have he : alignedTime s u = alignedTime s t := hY.unique hX
  rw [← he]
  exact correct_simulator_word hs HY hcorrectY

/-- At the reference simulator's designated root, every correct input with
that complete simulator trace emits its own demanded raw bit. -/
theorem common_simulator_root {M : TM} {d b s t : ℕ} {X Y : Fin (d * d * b) → Bool}
    (hs : 0 < s) (H : HaltsAt M (List.ofFn X) t) (hcorrectY : OutputsTranspose M d b Y)
    (htrace : trace (machine M hs) (List.ofFn Y) = trace (machine M hs) (List.ofFn X))
    (p : Fin (d * d * b)) :
    (outBit (machine M hs) (List.ofFn Y)
      (simulatorRoot M hs (List.ofFn X) t (tposOf d b p).val)).getD false = Y p := by
  have hh := (sourceRoot_output (fun j => Y (tposOf d b j))
    (common_simulator_word hs H hcorrectY htrace) (tposOf d b p)).2
  simp only [tposOf_tposOf] at hh
  change (outBit (machine M hs) (List.ofFn Y)
    (appendTime (trace (machine M hs) (List.ofFn Y)) (alignedTime s t) (tposOf d b p).val)).getD false = _ at hh
  rw [htrace] at hh
  exact hh

end AdaptiveTransfer.TransferCorrect
