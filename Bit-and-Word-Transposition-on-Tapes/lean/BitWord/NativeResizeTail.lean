import BitWord.NativeResizeRecord

namespace BitWord.NativeResizeScan
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

/-- Entire padding rows are emitted (or discarded) by the same controller's
tail fragment. The short-width ruler is present but unchanged. -/
theorem tail_record_trace (expand : Bool) (a : ℕ) (extra : List Bool)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 5*extra.length+11,TraceCore expand false t
      (cfg .pad ⟨sl,tailInput expand extra sr⟩ (NativeSealBack.openWord pre)
        (markedRuler a) (markedRuler extra.length) pos).denote
      (cfg .begin ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutput expand extra))
        (markedRuler a) (markedRuler extra.length)
        (positions pos (consumed expand extra).length (tailOutput expand extra).length 0 0)).denote := by
  have hr := tail_run expand extra sl sr [.start] [.stop] (markedRuler a) pre pos false
  have hstop := pad_stop expand
    ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
    (NativeSealBack.openWord (pre++tailOutput expand extra)) (markedRuler a) extra.length
    (positions pos (consumed expand extra).length (tailOutput expand extra).length 0 extra.length) false
  have hrun : NativeZipper.run (programCore expand false) ((if expand then 2 else 3)*extra.length+1)
      (cfg .pad ⟨sl,tailInput expand extra sr⟩ (NativeSealBack.openWord pre)
        (markedRuler a) (markedRuler extra.length) pos)=
      cfg (.rewind false .back) ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutput expand extra)) (markedRuler a)
        (endRuler extra.length)
        (positions pos (consumed expand extra).length (tailOutput expand extra).length 0 extra.length) := by
    rw [NativeZipper.run_add]
    rw [show markedRuler extra.length=⟨[.start],unary extra.length++[.stop]⟩ from markedRuler_def _]
    rw [hr]
    exact hstop
  let src : Tape Bool := ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
  let out := NativeSealBack.openWord (pre++tailOutput expand extra)
  let b0 : Bank := ![src,out,markedRuler a,endRuler extra.length]
  let b1 : Bank := ![src,out,markedRuler a,markedRuler extra.length]
  let p0 := positions pos (consumed expand extra).length (tailOutput expand extra).length 0 extra.length
  let p1 := positions pos (consumed expand extra).length (tailOutput expand extra).length 0 0
  obtain ⟨t0,h0,tr0⟩ := NativeZipper.trace_of_run (programCore expand false) hrun
  obtain ⟨t1,h1,tr1⟩ : ∃ t ≤ 4,TraceCore expand false t
      (workCfg (.rewind false .back) b0 p0) (workCfg (.rewind false .done) b0 p0) :=
    NativeTapeCalls.rewind_start (programCore expand false) 2 (Label.rewind false)
      (rewind_code expand false false) b0 p0 (List.replicate a false) rfl
  have j1 : TraceCore expand false 1 (workCfg (.rewind false .done) b0 p0)
      (workCfg (.rewind true .back) b0 p0) := NativeMicrocode.jump_trace _ _ _ rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t ≤ 2*extra.length+4,TraceCore expand false t
      (workCfg (.rewind true .back) b0 p0) (workCfg (.rewind true .done) b1 p1) := by
    simpa [b0,b1,p0,p1,positions,markedRuler] using
      NativeTapeCalls.rewind (programCore expand false) 3 (Label.rewind true)
        (rewind_code expand true false) b0 p0 (List.replicate extra.length false) (by simp [b0])
  have j2 : TraceCore expand false 1 (workCfg (.rewind true .done) b1 p1)
      (workCfg .begin b1 p1) := NativeMicrocode.jump_trace _ _ _ rfl
  have tr01 := trace_trans tr0 tr1
  have tr1j := trace_trans tr01 j1
  have tr12 := trace_trans tr1j tr2
  have tr := trace_trans tr12 j2
  refine ⟨_,?_,tr⟩
  cases expand <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h0 <;> omega

end BitWord.NativeResizeScan
