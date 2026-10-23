import BitWord.NativeSquare

namespace BitWord.NativeSquare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop
open NativeResizeScan (unary markedRuler endRuler inputRecord outputRecord inputRows outputRows consumed tailOutput)

def cursor (remaining passed : ℕ) : Tape Bool :=
  ⟨unary passed++[.start],unary remaining++[.stop]⟩

def zcfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc,s⟩,pos⟩

@[simp] theorem zcfg_denote (pc : Label) (s : Bank) (pos : Port → ℤ) :
    (zcfg pc s pos).denote=cfg pc s pos := rfl

@[simp] theorem cursor_zero (n : ℕ) : cursor n 0=markedRuler n := by
  simp [cursor,markedRuler,unary,Counter.marked,symbols,List.map_replicate]

@[simp] theorem cursor_end (n : ℕ) : cursor 0 n=endRuler n := by
  simp [cursor,endRuler,unary]

theorem rows_check (expand : Bool) (src out : Tape Bool) (a b r t u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1
      (zcfg .checkRows (bank src out a b (cursor (r+1) u) (cursor t v)) pos)=
      zcfg (.row .copy) (bank src out a b (cursor (r+1) u) (cursor t v)) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,NativeResizeScan.unary_succ,Tape.read]

theorem rows_advance (expand : Bool) (src out : Tape Bool) (a b r t u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 2
      (zcfg (.row .begin) (bank src out a b (cursor (r+1) u) (cursor (t+1) v)) pos)=
      zcfg .checkRows (bank src out a b (cursor r (u+1)) (cursor t (v+1)))
        (positions pos 0 0 1 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,NativeResizeScan.unary_succ,Tape.read,
    Microcode.Action.apply,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext i <;> fin_cases i <;> simp [positions]

theorem rows_stop (expand : Bool) (src out : Tape Bool) (a b t u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1
      (zcfg .checkRows (bank src out a b (cursor 0 u) (cursor t v)) pos)=
      zcfg .checkTail (bank src out a b (cursor 0 u) (cursor t v)) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,Tape.read]

theorem tail_check (expand : Bool) (src out : Tape Bool) (a b t u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1
      (zcfg .checkTail (bank src out a b (cursor 0 u) (cursor (t+1) v)) pos)=
      zcfg (.padding .pad) (bank src out a b (cursor 0 u) (cursor (t+1) v)) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,NativeResizeScan.unary_succ,Tape.read]

theorem tail_advance (expand : Bool) (src out : Tape Bool) (a b t u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 2
      (zcfg (.padding .begin) (bank src out a b (cursor 0 u) (cursor (t+1) v)) pos)=
      zcfg .checkTail (bank src out a b (cursor 0 u) (cursor t (v+1)))
        (positions pos 0 0 0 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,NativeResizeScan.unary_succ,Tape.read,
    Microcode.Action.apply,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext i <;> fin_cases i <;> simp [positions]

theorem tail_stop (expand : Bool) (src out : Tape Bool) (a b u v : ℕ) (pos : Port → ℤ) :
    NativeZipper.run (program expand) 1
      (zcfg .checkTail (bank src out a b (cursor 0 u) (cursor 0 v)) pos)=
      zcfg (.seal .seal) (bank src out a b (cursor 0 u) (cursor 0 v)) pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    program,zcfg,bank,cursor,Tape.read]

/-- Main rows are counted by a physical ruler, independently of their contents. -/
theorem rows_trace (expand : Bool) (a e : ℕ)
    (rows : List (List Bool × List Bool))
    (hlen : ∀ r ∈ rows, r.1.length=a ∧ r.2.length=e)
    (tailCount passedShort passedLong : ℕ) (sl sr : List (Sym Bool))
    (pre : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ rows.length*(7*(a+e)+15)+1,Trace expand t
      (cfg .checkRows (bank ⟨sl,symbols (inputRows expand rows)++sr⟩
        (NativeSealBack.openWord pre) a (a+e)
        (cursor rows.length passedShort) (cursor (rows.length+tailCount) passedLong)) pos)
      (cfg .checkTail (bank ⟨(symbols (inputRows expand rows)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++outputRows expand rows)) a (a+e)
        (cursor 0 (passedShort+rows.length)) (cursor tailCount (passedLong+rows.length)))
        (positions pos (inputRows expand rows).length (outputRows expand rows).length rows.length rows.length)) := by
  induction rows generalizing sl pre pos passedShort passedLong with
  | nil =>
    simpa [inputRows,outputRows,symbols] using
      NativeZipper.trace_of_run (program expand)
        (rows_stop expand ⟨sl,sr⟩ (NativeSealBack.openWord pre) a (a+e) tailCount passedShort passedLong pos)
  | cons r rows ih =>
    obtain ⟨hr,he⟩ := hlen r (by simp)
    have htail : ∀ r ∈ rows,r.1.length=a ∧ r.2.length=e := by
      intro r h; exact hlen r (by simp [h])
    let srcTail := symbols (inputRows expand rows)++sr
    let src := (⟨sl,symbols (inputRecord expand r.1 r.2)++srcTail⟩ : Tape Bool)
    let sout := NativeSealBack.openWord pre
    let short := cursor (rows.length+1) passedShort
    let long := cursor (rows.length+tailCount+1) passedLong
    obtain ⟨t0,h0,tr0⟩ := NativeZipper.trace_of_run (program expand)
      (rows_check expand src sout a (a+e) rows.length (rows.length+tailCount+1) passedShort passedLong pos)
    obtain ⟨t1,h1,tr1⟩ := row_call expand r.1 r.2 sl srcTail pre short long pos
    let nextLeft := (symbols (inputRecord expand r.1 r.2)).reverse++sl
    let nextPre := pre++outputRecord expand r.1 r.2
    let scanPos := positions pos (inputRecord expand r.1 r.2).length (outputRecord expand r.1 r.2).length 0 0
    obtain ⟨t2,h2,tr2⟩ := NativeZipper.trace_of_run (program expand)
      (rows_advance expand ⟨nextLeft,srcTail⟩ (NativeSealBack.openWord nextPre)
        a (a+e) rows.length (rows.length+tailCount) passedShort passedLong scanPos)
    let nextPos := positions scanPos 0 0 1 1
    obtain ⟨t3,h3,tr3⟩ := ih htail (passedShort+1) (passedLong+1) nextLeft nextPre nextPos
    simp only [zcfg_denote] at tr0 tr2
    have tr01 := trace_trans tr0 (by simpa only [hr,he] using tr1)
    have tr012 := trace_trans tr01 tr2
    have tr3' : Trace expand t3
        (cfg .checkRows (bank ⟨nextLeft,srcTail⟩ (NativeSealBack.openWord nextPre)
          a (a+e) (cursor rows.length (passedShort+1))
          (cursor (rows.length+tailCount) (passedLong+1))) nextPos)
        (cfg .checkTail (bank ⟨(symbols (inputRows expand (r::rows))).reverse++sl,sr⟩
          (NativeSealBack.openWord (pre++outputRows expand (r::rows))) a (a+e)
          (cursor 0 (passedShort+(r::rows).length)) (cursor tailCount (passedLong+(r::rows).length)))
          (positions pos (inputRows expand (r::rows)).length (outputRows expand (r::rows)).length
            (r::rows).length (r::rows).length)) := by
      simpa [inputRows,outputRows,List.flatMap_cons,symbols,List.map_append,
        List.reverse_append,List.append_assoc,nextLeft,nextPre,nextPos,scanPos,srcTail,
        positions_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tr3
    have tr := trace_trans tr012 tr3'
    refine ⟨t0+t1+t2+t3,?_,?_⟩
    · simp only [hr,he] at h1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa [inputRows,List.flatMap_cons,symbols,List.map_append,List.append_assoc,
        src,srcTail,sout,short,long,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tr

end BitWord.NativeSquare
