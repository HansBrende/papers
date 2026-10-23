import BitWord.NativeResizeScan

namespace BitWord.NativeResizeScan
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop

abbrev Bank := Port → Tape Bool
abbrev TraceCore (expand loop : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (programCore expand loop)) (NativeMicrocode.Active (programCore expand loop))
abbrev Trace (expand : Bool) := TraceCore expand true

def inputRecord (expand : Bool) (xs extra : List Bool) := xs++consumed expand extra

def outputRecord (expand : Bool) (xs extra : List Bool) := xs++tailOutput expand extra

def markedRuler (n : ℕ) := Counter.marked (List.replicate n false)
def endRuler (n : ℕ) : Tape Bool := ⟨unary n++[.start],[.stop]⟩

@[simp] theorem markedRuler_def (n : ℕ) : markedRuler n=⟨[.start],unary n++[.stop]⟩ := by
  simp [markedRuler,Counter.marked,symbols,unary]

@[simp] theorem endRuler_def (n : ℕ) : endRuler n=⟨(symbols (List.replicate n false)).reverse++[.start],[.stop]⟩ := by
  simp [endRuler,symbols,unary]

theorem copy_stop (expand : Bool) (src out long : Tape Bool) (a : ℕ) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) 1 (cfg .copy src out ⟨unary a++[.start],[.stop]⟩ long pos)=
      cfg .pad src out ⟨unary a++[.start],[.stop]⟩ long pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    programCore,cfg,Tape.read]

theorem pad_stop (expand : Bool) (src out short : Tape Bool) (b : ℕ) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) 1 (cfg .pad src out short ⟨unary b++[.start],[.stop]⟩ pos)=
      cfg (.rewind false .back) src out short ⟨unary b++[.start],[.stop]⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    programCore,cfg,Tape.read]

def startRecord (pc : Label) (expand : Bool) (xs extra : List Bool)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :=
  cfg pc ⟨sl,symbols (inputRecord expand xs extra)++sr⟩ (NativeSealBack.openWord pre)
    (markedRuler xs.length) (markedRuler (xs.length+extra.length)) pos

def endRecord (pc : Label) (expand : Bool) (xs extra : List Bool)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) :=
  cfg pc ⟨(symbols (inputRecord expand xs extra)).reverse++sl,sr⟩
    (NativeSealBack.openWord (pre++outputRecord expand xs extra))
    (markedRuler xs.length) (markedRuler (xs.length+extra.length))
    (positions pos (inputRecord expand xs extra).length (outputRecord expand xs extra).length 0 0)

/-- Literal forward scan for one record, before the paid ruler rewinds. -/
theorem record_scan_run (expand : Bool) (xs extra : List Bool)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) (3*xs.length+1+(if expand then 2 else 3)*extra.length+1)
      (startRecord .copy expand xs extra sl sr pre pos)=
      cfg (.rewind false .back) ⟨(symbols (inputRecord expand xs extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++outputRecord expand xs extra))
        (endRuler xs.length) (endRuler (xs.length+extra.length))
        (positions pos (inputRecord expand xs extra).length (outputRecord expand xs extra).length
          xs.length (xs.length+extra.length)) := by
  have hinput : symbols (inputRecord expand xs extra)++sr=symbols xs++tailInput expand extra sr := by
    cases expand <;> simp [inputRecord,consumed,tailInput,symbols,List.append_assoc]
  have hs : startRecord .copy expand xs extra sl sr pre pos=
      cfg .copy ⟨sl,symbols xs++tailInput expand extra sr⟩ (NativeSealBack.openWord pre)
        ⟨[.start],unary xs.length++[.stop]⟩
        ⟨[.start],unary xs.length++(unary extra.length++[.stop])⟩ pos := by
    simp [startRecord,markedRuler_def,hinput,unary_append,List.append_assoc]
  rw [hs,show 3*xs.length+1+(if expand then 2 else 3)*extra.length+1=
    3*xs.length+(1+((if expand then 2 else 3)*extra.length+1)) by omega,
    NativeZipper.run_add,copy_run (loop := loop),NativeZipper.run_add]
  rw [copy_stop expand _ _ _ xs.length _ loop,NativeZipper.run_add,tail_run (loop := loop),positions_add]
  have hend : unary extra.length++(unary xs.length++[.start])=
      unary (xs.length+extra.length)++[.start] := by
    rw [← List.append_assoc,← unary_append,Nat.add_comm extra.length]
  rw [hend]
  rw [pad_stop expand _ _ _ (xs.length+extra.length) _ loop]
  cases expand <;> simp [inputRecord,outputRecord,consumed,tailOutput,symbols,
    List.reverse_append,List.append_assoc,endRuler]

theorem rewind_code (expand long : Bool) (loop : Bool := true) :
    NativeTapeCalls.Code (programCore expand loop) (ruler long) (Label.rewind long) NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [programCore,NativeSealBack.program,FinitePortBinding.instruction_eq]

@[simp] theorem update_four_two {A : Type*} (a b c d x : A) :
    Function.update ![a,b,c,d] (2:Fin 4) x=![a,b,x,d] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_four_three {A : Type*} (a b c d x : A) :
    Function.update ![a,b,c,d] (3:Fin 4) x=![a,b,c,x] := by funext i; fin_cases i <;> rfl

/-- The physical rulers are restored after each record, including their heads. -/
theorem record_trace (expand : Bool) (xs extra : List Bool)
    (sl sr : List (Sym Bool)) (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    ∃ t ≤ 7*(xs.length+extra.length)+12,TraceCore expand loop t
      (startRecord .copy expand xs extra sl sr pre pos).denote
      (endRecord .begin expand xs extra sl sr pre pos).denote := by
  let a := xs.length
  let b := xs.length+extra.length
  let src : Tape Bool := ⟨(symbols (inputRecord expand xs extra)).reverse++sl,sr⟩
  let out := NativeSealBack.openWord (pre++outputRecord expand xs extra)
  let bank0 : Bank := ![src,out,endRuler a,endRuler b]
  let bank1 : Bank := ![src,out,markedRuler a,endRuler b]
  let bank2 : Bank := ![src,out,markedRuler a,markedRuler b]
  let n := (inputRecord expand xs extra).length
  let m := (outputRecord expand xs extra).length
  let p0 := positions pos n m a b
  let p1 := positions pos n m 0 b
  let p2 := positions pos n m 0 0
  obtain ⟨t0,h0,tr0⟩ := NativeZipper.trace_of_run (programCore expand loop) (record_scan_run expand xs extra sl sr pre pos loop)
  obtain ⟨t1,h1,tr1⟩ : ∃ t ≤ 2*a+4,TraceCore expand loop t
      (workCfg (.rewind false .back) bank0 p0) (workCfg (.rewind false .done) bank1 p1) := by
    simpa [bank0,bank1,p0,p1,positions,markedRuler] using
      NativeTapeCalls.rewind (programCore expand loop) 2 (Label.rewind false) (rewind_code expand false loop)
        bank0 p0 (List.replicate a false) (by simp [bank0])
  have j1 : TraceCore expand loop 1 (workCfg (.rewind false .done) bank1 p1)
      (workCfg (.rewind true .back) bank1 p1) := NativeMicrocode.jump_trace _ _ _ rfl
  obtain ⟨t2,h2,tr2⟩ : ∃ t ≤ 2*b+4,TraceCore expand loop t
      (workCfg (.rewind true .back) bank1 p1) (workCfg (.rewind true .done) bank2 p2) := by
    simpa [bank1,bank2,p1,p2,positions,markedRuler] using
      NativeTapeCalls.rewind (programCore expand loop) 3 (Label.rewind true) (rewind_code expand true loop)
        bank1 p1 (List.replicate b false) (by simp [bank1])
  have j2 : TraceCore expand loop 1 (workCfg (.rewind true .done) bank2 p2)
      (workCfg .begin bank2 p2) := NativeMicrocode.jump_trace _ _ _ rfl
  have tr01 := trace_trans tr0 tr1
  have tr1j := trace_trans tr01 j1
  have tr12 := trace_trans tr1j tr2
  have tr := trace_trans tr12 j2
  refine ⟨_,?_,tr⟩
  change t1 ≤ 2*xs.length+4 at h1
  change t2 ≤ 2*(xs.length+extra.length)+4 at h2
  cases expand <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h0 <;> omega

end BitWord.NativeResizeScan
