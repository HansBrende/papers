import BitWord.NativeResizeTail
import BitWord.NativeResizeRows

/-! A fixed six-tape rectangular padding/cropping controller. The four rulers
specify short/long row widths and short/long row counts. -/
namespace BitWord.NativeSquare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames
open NativeResizeScan (markedRuler endRuler inputRecord outputRecord inputRows outputRows consumed tailOutput)

abbrev Port := Fin 6
abbrev Bank := Port → Tape Bool

def coreBinding : FinitePortBinding (Fin 4) Port where
  ports := ⟨fun i => ⟨i.val,by omega⟩,by intro i j h; exact Fin.ext (congrArg (fun x : Fin 6 => x.val) h)⟩
  decode := ![some 0,some 1,some 2,some 3,none,none]
  decode_spec := by intro p i; fin_cases p <;> fin_cases i <;> decide

@[simp] theorem core_values {A : Type*} (x : Fin 4 → A) (s : Port → A) :
    coreBinding.values x s=![x 0,x 1,x 2,x 3,s 4,s 5] := by
  funext i; fin_cases i <;> rfl

inductive Label
  | init (pc : NativeBuffer.Label)
  | checkRows | row (pc : NativeResizeScan.Label) | advanceRows
  | checkTail | padding (pc : NativeResizeScan.Label) | advanceTail
  | seal (pc : NativeSealBack.Label)
  | rewind (port : Port) (pc : NativeSealBack.Label)
  | done | reject
  deriving DecidableEq, Fintype

def start : Label := .init (.erase 0)

def program (expand : Bool) : Microcode.Program Port Label
  | .init .done => .jump .checkRows
  | .init pc => (singleBinding 1).instruction Label.init (NativeBuffer.program pc)
  | .checkRows => .read 4 (fun s => match s with | .data _ => .row .copy | .stop => .checkTail | _ => .reject)
  | .row .begin => .jump .advanceRows
  | .row pc => coreBinding.instruction Label.row (NativeResizeScan.programCore expand false pc)
  | .advanceRows => .act (fun p => if p=4 ∨ p=5 then ⟨none,.right⟩ else ⟨none,.stay⟩) .checkRows
  | .checkTail => .read 5 (fun s => match s with | .data _ => .padding .pad | .stop => .seal .seal | _ => .reject)
  | .padding .begin => .jump .advanceTail
  | .padding pc => coreBinding.instruction Label.padding (NativeResizeScan.programCore expand false pc)
  | .advanceTail => .act (fun p => if p=5 then ⟨none,.right⟩ else ⟨none,.stay⟩) .checkTail
  | .seal .done => .jump (.rewind 0 .back)
  | .seal pc => (singleBinding 1).instruction Label.seal (NativeSealBack.program pc)
  | .rewind p .done => .jump (if p=0 then .rewind 4 .back else if p=4 then .rewind 5 .back else .done)
  | .rewind p pc => (singleBinding p).instruction (Label.rewind p) (NativeSealBack.program pc)
  | .done => .halt
  | .reject => .reject

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace (expand : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program expand)) (NativeMicrocode.Active (program expand))

theorem init_code (expand : Bool) :
    NativeTapeCalls.Code (program expand) 1 Label.init NativeBuffer.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem row_code (expand : Bool) (pc : NativeResizeScan.Label)
    (hh : NativeResizeScan.programCore expand false pc ≠ .halt)
    (_ : NativeResizeScan.programCore expand false pc ≠ .reject) :
    program expand (.row pc)=MicrocodeEmbedding.instruction coreBinding.ports Label.row
      (NativeResizeScan.programCore expand false pc) := by
  cases pc <;> simp_all [program,NativeResizeScan.programCore,FinitePortBinding.instruction_eq]

theorem padding_code (expand : Bool) (pc : NativeResizeScan.Label)
    (hh : NativeResizeScan.programCore expand false pc ≠ .halt)
    (_ : NativeResizeScan.programCore expand false pc ≠ .reject) :
    program expand (.padding pc)=MicrocodeEmbedding.instruction coreBinding.ports Label.padding
      (NativeResizeScan.programCore expand false pc) := by
  cases pc <;> simp_all [program,NativeResizeScan.programCore,FinitePortBinding.instruction_eq]

theorem seal_code (expand : Bool) :
    NativeTapeCalls.Code (program expand) 1 Label.seal NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem rewind_code (expand : Bool) (p : Port) :
    NativeTapeCalls.Code (program expand) p (Label.rewind p) NativeSealBack.program := by
  intro pc hh _
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

def bank (src out : Tape Bool) (a b : ℕ) (shortRows longRows : Tape Bool) : Bank :=
  ![src,out,markedRuler a,markedRuler b,shortRows,longRows]

def positions (pos : Port → ℤ) (n m r t : ℕ) : Port → ℤ :=
  ![pos 0+n,pos 1+m,pos 2,pos 3,pos 4+r,pos 5+t]

@[simp] theorem positions_zero (pos : Port → ℤ) : positions pos 0 0 0 0=pos := by
  funext i; fin_cases i <;> simp [positions]

theorem positions_add (pos : Port → ℤ) (n m r t n' m' r' t' : ℕ) :
    positions (positions pos n m r t) n' m' r' t'=
      positions pos (n+n') (m+m') (r+r') (t+t') := by
  funext i; fin_cases i <;> simp [positions,Nat.cast_add] <;> ring

/-- Call the checked one-record converter while retaining the row-count rulers. -/
theorem row_call (expand : Bool) (xs extra : List Bool) (sl sr : List (Sym Bool))
    (pre : List Bool) (shortRows longRows : Tape Bool) (pos : Port → ℤ) :
    ∃ t ≤ 7*(xs.length+extra.length)+12,Trace expand t
      (cfg (.row .copy) (bank ⟨sl,symbols (inputRecord expand xs extra)++sr⟩
        (NativeSealBack.openWord pre) xs.length (xs.length+extra.length) shortRows longRows) pos)
      (cfg (.row .begin) (bank ⟨(symbols (inputRecord expand xs extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++outputRecord expand xs extra))
        xs.length (xs.length+extra.length) shortRows longRows)
        (positions pos (inputRecord expand xs extra).length (outputRecord expand xs extra).length 0 0)) := by
  let s := bank ⟨sl,symbols (inputRecord expand xs extra)++sr⟩
    (NativeSealBack.openWord pre) xs.length (xs.length+extra.length) shortRows longRows
  let p : Fin 4 → ℤ := ![pos 0,pos 1,pos 2,pos 3]
  obtain ⟨t,ht,htr⟩ := NativeResizeScan.record_trace expand xs extra sl sr pre p false
  have hh := MicrocodeEmbedding.trace_embed coreBinding.ports Label.row
    (NativeResizeScan.programCore expand false) (program expand) (frame s pos) (row_code expand) htr
  change Trace expand t
    (MicrocodeEmbedding.embed coreBinding.ports Label.row
      (workCfg .copy ![⟨sl,symbols (inputRecord expand xs extra)++sr⟩,
        NativeSealBack.openWord pre,markedRuler xs.length,markedRuler (xs.length+extra.length)] p) _)
    (MicrocodeEmbedding.embed coreBinding.ports Label.row
      (workCfg .begin ![⟨(symbols (inputRecord expand xs extra)).reverse++sl,sr⟩,
        NativeSealBack.openWord (pre++outputRecord expand xs extra),
        markedRuler xs.length,markedRuler (xs.length+extra.length)]
        (NativeResizeScan.positions p (inputRecord expand xs extra).length
          (outputRecord expand xs extra).length 0 0)) _) at hh
  rw [embed_work,embed_work] at hh
  refine ⟨t,ht,?_⟩
  have hpos : coreBinding.values p pos=pos := by funext i; fin_cases i <;> rfl
  have hend : coreBinding.values (NativeResizeScan.positions p (inputRecord expand xs extra).length
      (outputRecord expand xs extra).length 0 0) pos=
      positions pos (inputRecord expand xs extra).length (outputRecord expand xs extra).length 0 0 := by
    simp [core_values,p,NativeResizeScan.positions,positions]
  simpa [hpos,hend,core_values,s,bank] using hh

/-- Emit or discard one entire extra row, keeping both count rulers. -/
theorem padding_call (expand : Bool) (a : ℕ) (extra : List Bool) (sl sr : List (Sym Bool))
    (pre : List Bool) (shortRows longRows : Tape Bool) (pos : Port → ℤ) :
    ∃ t ≤ 5*extra.length+11,Trace expand t
      (cfg (.padding .pad) (bank ⟨sl,NativeResizeScan.tailInput expand extra sr⟩
        (NativeSealBack.openWord pre) a extra.length shortRows longRows) pos)
      (cfg (.padding .begin) (bank ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutput expand extra)) a extra.length shortRows longRows)
        (positions pos (consumed expand extra).length (tailOutput expand extra).length 0 0)) := by
  let s := bank ⟨sl,NativeResizeScan.tailInput expand extra sr⟩
    (NativeSealBack.openWord pre) a extra.length shortRows longRows
  let p : Fin 4 → ℤ := ![pos 0,pos 1,pos 2,pos 3]
  obtain ⟨t,ht,htr⟩ := NativeResizeScan.tail_record_trace expand a extra sl sr pre p
  have hh := MicrocodeEmbedding.trace_embed coreBinding.ports Label.padding
    (NativeResizeScan.programCore expand false) (program expand) (frame s pos) (padding_code expand) htr
  change Trace expand t
    (MicrocodeEmbedding.embed coreBinding.ports Label.padding
      (workCfg .pad ![⟨sl,NativeResizeScan.tailInput expand extra sr⟩,
        NativeSealBack.openWord pre,markedRuler a,markedRuler extra.length] p) _)
    (MicrocodeEmbedding.embed coreBinding.ports Label.padding
      (workCfg .begin ![⟨(symbols (consumed expand extra)).reverse++sl,sr⟩,
        NativeSealBack.openWord (pre++tailOutput expand extra),markedRuler a,markedRuler extra.length]
        (NativeResizeScan.positions p (consumed expand extra).length (tailOutput expand extra).length 0 0)) _) at hh
  rw [embed_work,embed_work] at hh
  refine ⟨t,ht,?_⟩
  have hpos : coreBinding.values p pos=pos := by funext i; fin_cases i <;> rfl
  have hend : coreBinding.values (NativeResizeScan.positions p (consumed expand extra).length
      (tailOutput expand extra).length 0 0) pos=
      positions pos (consumed expand extra).length (tailOutput expand extra).length 0 0 := by
    simp [core_values,p,NativeResizeScan.positions,positions]
  simpa [hpos,hend,core_values,s,bank] using hh

end BitWord.NativeSquare
