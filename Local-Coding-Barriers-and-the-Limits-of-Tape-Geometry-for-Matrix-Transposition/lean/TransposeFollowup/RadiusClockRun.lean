import TransposeFollowup.PortBindingFrame
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.NativeSealBack
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.NativeErase
import TransposeFollowup.SevenPhaseClock
import TransposeFollowup.EntryBitsRun
import TransposeFollowup.NativeDivideThreeRun
import TransposeFollowup.DimensionScaleMeaning
import TransposeFollowup.FixedMultipleRun
import TransposeFollowup.SeedMultipleMeaning
import TransposeFollowup.NativeBatchErase
import TransposeFollowup.NativeUnprepare
import Transpose.Tape.MStarTM

/-! A fixed two-tape routine appends a fixed number of equal bits for each
unit of a physical binary counter. The counter is consumed and ends all ones.
Counter loading, the output START marker and sealing are caller obligations. -/
namespace TransposeFollowup.CountedFill
open FixedTapeCompiler
open CopyMachine (Tape Sym symbols)
set_option autoImplicit false

def counterBinding : FinitePortBinding (Fin 1) (Fin 2) where
  ports := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=0 then some 0 else none
  decode_spec := by intro p i;fin_cases p <;> fin_cases i <;> decide

inductive Label (m : ℕ)
  | counter (pc : Microcode.DecrementFamily.Label)
  | emit (i : Fin (m+1))
  deriving DecidableEq, Fintype

def program (m : ℕ) (bit : Bool) : Microcode.Program (Fin 2) (Label m)
  | .counter pc => if pc=11 then .jump (.emit 0)
      else counterBinding.instruction Label.counter (Microcode.DecrementFamily.program pc)
  | .emit i => if h : i.val < m then
      .act (Microcode.single 1 ⟨some (.data bit), .right⟩) (.emit ⟨i.val+1,by omega⟩)
      else .jump (.counter 0)

theorem counter_code (m : ℕ) (bit : Bool) (pc : Microcode.DecrementFamily.Label)
    (hh : Microcode.DecrementFamily.program pc≠.halt) (_ : Microcode.DecrementFamily.program pc≠.reject) :
    program m bit (.counter pc)=MicrocodeEmbedding.instruction counterBinding.ports
      Label.counter (Microcode.DecrementFamily.program pc) := by
  have hn : pc ≠ 11 := by intro h;subst pc;exact hh rfl
  simp [program,hn,FinitePortBinding.instruction_eq]

def bank (fuel : List Bool) (acc : List Bool) (p : Fin 2) : Tape Bool :=
  if p=0 then Counter.marked fuel else NativeSealBack.openWord acc

def positions (origin : Fin 2 → ℤ) (acc : List Bool) (p : Fin 2) : ℤ :=
  origin p+if p=1 then (acc.length : ℤ) else 0

def cfg {m : ℕ} (pc : Label m) (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    NativeZipper.Config (Fin 2) (Label m) := ⟨⟨pc,bank fuel acc⟩,positions origin acc⟩

def frame (origin : Fin 2 → ℤ) (acc : List Bool) : MicrocodeEmbedding.Frame (Fin 2) :=
  ⟨fun p => (bank [] acc p).denote,positions origin acc⟩

theorem loop_state (m : ℕ) (origin : Fin 2 → ℤ) (pc : Microcode.DecrementFamily.Label)
    (fuel acc : List Bool) :
    NativeCountedLoop.state counterBinding.ports (Label.counter (m:=m)) (frame origin)
      (fun _ => origin 0) pc fuel acc=(cfg (.counter pc) fuel acc origin).denote := by
  unfold NativeCountedLoop.state MicrocodeEmbedding.embed NativeCounter.cfg
    NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← counterBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> simp [counterBinding,FinitePortBinding.values,bank,positions]

abbrev Trace (m : ℕ) (bit : Bool) :=
  OperationalTrace.Trace (NativeMicrocode.step (program m bit)) (NativeMicrocode.Active (program m bit))

noncomputable def nativeEncoding (m : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 2) (Label.counter (m:=m) 0)
noncomputable def nativeMachine (m : ℕ) (bit : Bool) := NativeMicrocode.machine (nativeEncoding m) (program m bit)

end TransposeFollowup.CountedFill


/-! The complete constant-size body, including both transfers, writes the
bits and advances the real output head. No counter value enters control. -/
namespace TransposeFollowup.CountedFill
open FixedTapeCompiler
open CopyMachine (Tape Sym symbols)
set_option autoImplicit false

theorem emit_step (m : ℕ) (bit : Bool) (i : Fin (m+1)) (hi : i.val < m)
    (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    NativeZipper.step (program m bit) (cfg (.emit i) fuel acc origin)=
      cfg (.emit ⟨i.val+1,by omega⟩) fuel (acc++[bit]) origin := by
  simp only [NativeZipper.step,Microcode.step,program,hi,dite_eq_left,cfg]
  congr 2
  · funext p;fin_cases p
    · simp [bank,Microcode.single,Microcode.Action.apply]
    · simp [bank,Microcode.single,Microcode.Action.apply,NativeSealBack.openWord,
        symbols,List.reverse_append,Tape.write,Tape.moveRight,Tape.read]
  · funext p;fin_cases p <;>
      simp [positions,Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift,Nat.cast_add,add_assoc]

theorem emit_run (m : ℕ) (bit : Bool) (i : Fin (m+1)) (fuel acc : List Bool)
    (origin : Fin 2 → ℤ) :
    NativeZipper.run (program m bit) (m - i.val+1) (cfg (.emit i) fuel acc origin)=
      cfg (.counter 0) fuel (acc++List.replicate (m - i.val) bit) origin := by
  generalize he : m - i.val=d
  induction d generalizing i acc with
  | zero =>
    have hi : i.val=m := by omega
    simp [hi,NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg]
  | succ d ih =>
    have hi : i.val < m := by omega
    rw [show d+1+1=1+(d+1) by omega,NativeZipper.run_add]
    change NativeZipper.run (program m bit) (d+1)
      (NativeZipper.step (program m bit) (cfg (.emit i) fuel acc origin))=_
    rw [emit_step m bit i hi]
    have hd : m-(i.val+1)=d := by omega
    rw [ih ⟨i.val+1,by omega⟩ (acc++[bit]) hd]
    simp [List.replicate_succ,List.append_assoc]

theorem body_run (m : ℕ) (bit : Bool) (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    NativeZipper.run (program m bit) (m+2) (cfg (.counter 11) fuel acc origin)=
      cfg (.counter 0) fuel (acc++List.replicate m bit) origin := by
  rw [show m+2=1+(m+1) by omega,NativeZipper.run_add]
  change NativeZipper.run (program m bit) (m+1)
    (NativeZipper.step (program m bit) (cfg (.counter 11) fuel acc origin))=_
  have h : NativeZipper.step (program m bit) (cfg (.counter 11) fuel acc origin)=
      cfg (.emit 0) fuel acc origin := by rfl
  rw [h]
  simpa only [Fin.val_zero,Nat.sub_zero] using emit_run m bit 0 fuel acc origin

theorem body_trace (m : ℕ) (bit : Bool) (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    ∃ t ≤ m+2,Trace m bit t (cfg (.counter 11) fuel acc origin).denote
      (cfg (.counter 0) fuel (acc++List.replicate m bit) origin).denote :=
  NativeZipper.trace_of_run (program m bit) (body_run m bit fuel acc origin)

end TransposeFollowup.CountedFill


/-! An unconditional native trace for the counted fill. The fixed repetition
factor is part of the finite program; the unbounded count is read from tape. -/
namespace TransposeFollowup.CountedFill
open FixedTapeCompiler
set_option autoImplicit false

def update (m : ℕ) (bit : Bool) (_ : List Bool) (acc : List Bool) : List Bool :=
  acc++List.replicate m bit

theorem resultState_word (m : ℕ) (bit : Bool) (n : ℕ) (fuel acc : List Bool) :
    NativeCountedLoop.resultState (update m bit) n fuel acc=acc++List.replicate (n*m) bit := by
  induction n generalizing fuel acc with
  | zero => simp [NativeCountedLoop.resultState]
  | succ n ih =>
    simp only [NativeCountedLoop.resultState,ih,update,Nat.succ_mul]
    rw [List.append_assoc,← List.replicate_add]
    simp [Nat.add_comm]

theorem fill_trace (m : ℕ) (bit : Bool) (fuel acc : List Bool) (origin : Fin 2 → ℤ) :
    ∃ t ≤ Counter.value fuel*(m+2)+8*(Counter.value fuel+1)+4*fuel.length,
      Trace m bit t (cfg (.counter 0) fuel acc origin).denote
        (cfg (.counter 12) (List.replicate fuel.length true)
          (acc++List.replicate (Counter.value fuel*m) bit) origin).denote := by
  obtain ⟨t,ht,htr⟩:=NativeCountedLoop.counted_trace counterBinding.ports
    (Label.counter (m:=m)) (program m bit) (frame origin) (fun _ => origin 0)
    (update m bit) fuel.length (m+2) (counter_code m bit)
    (fun xs _ s => by simpa only [loop_state,update] using body_trace m bit xs s origin)
    (Counter.value fuel) fuel acc rfl rfl
  have hcost:=NativeCounter.native_sequence_budget (Counter.value fuel+1) fuel
  exact ⟨t,by omega,by simpa only [loop_state,resultState_word,
    NativeCountedLoop.terminal_word (Counter.value fuel) fuel rfl] using htr⟩

theorem native_fill (m : ℕ) (bit : Bool) (fuel acc : List Bool) (origin : Fin 2 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ Counter.value fuel*(m+2)+8*(Counter.value fuel+1)+4*fuel.length,
      Transpose.stepN (nativeMachine m bit) input t
        ((cfg (.counter 0) fuel acc origin).denote.denote (nativeEncoding m) (program m bit) inputPos outRev)=
        some ((cfg (.counter 12) (List.replicate fuel.length true)
          (acc++List.replicate (Counter.value fuel*m) bit) origin).denote.denote
            (nativeEncoding m) (program m bit) inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=fill_trace m bit fuel acc origin
  exact ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding m) (program m bit) input inputPos outRev htr⟩

end TransposeFollowup.CountedFill


/-! A fixed three-tape clock builder. Its source is a marked binary radius;
the counter and clock tapes start blank. Three distinct passes produce the
three contiguous runs; they are not interleaved seven-symbol blocks. -/
namespace TransposeFollowup.ClockBuilder
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Phase | lead | middle | tail deriving DecidableEq

instance : Fintype Phase where
  elems := {.lead,.middle,.tail}
  complete := by intro p;cases p <;> simp

def width : Phase → ℕ | .lead => 1 | .middle => 4 | .tail => 2
def bit : Phase → Bool | .middle => true | _ => false

def singleBinding (p : Fin 3) : FinitePortBinding (Fin 1) (Fin 3) where
  ports := ⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun q => if q=p then some 0 else none
  decode_spec := by
    intro q t
    change (if q=p then some 0 else none)=some t ↔ p=q
    fin_cases t
    by_cases h : q=p
    · subst q;simp
    · simp [h,Ne.symm h]

def copyBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports := ⟨![0,1],by decide +kernel⟩
  decode := fun p => if p=0 then some 0 else if p=1 then some 1 else none
  decode_spec := by intro p t;fin_cases p <;> fin_cases t <;> decide

def fillBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports := ⟨![1,2],by decide +kernel⟩
  decode := fun p => if p=1 then some 0 else if p=2 then some 1 else none
  decode_spec := by intro p t;fin_cases p <;> fin_cases t <;> decide

inductive Label
  | init (pc : NativeBuffer.Label)
  | copy (phase : Phase) (pc : NativeMappedCopy.Label)
  | fill (phase : Phase) (pc : CountedFill.Label (width phase))
  | erase (phase : Phase) (pc : NativeErase.Label)
  | seal (pc : NativeSealBack.Label)
  deriving DecidableEq,Fintype

def after : Phase → Label
  | .lead => .copy .middle (.init (.erase 0))
  | .middle => .copy .tail (.init (.erase 0))
  | .tail => .seal .seal

def program : Microcode.Program (Fin 3) Label
  | .init .done => .jump (.copy .lead (.init (.erase 0)))
  | .init pc => (singleBinding 2).instruction Label.init (NativeBuffer.program pc)
  | .copy p (.seal .done) => .jump (.fill p (.counter 0))
  | .copy p pc => copyBinding.instruction (Label.copy p) (NativeMappedCopy.program id pc)
  | .fill p (.counter pc) => if pc=12 then .jump (.erase p 2)
      else fillBinding.instruction (Label.fill p) (CountedFill.program (width p) (bit p) (.counter pc))
  | .fill p pc => fillBinding.instruction (Label.fill p) (CountedFill.program (width p) (bit p) pc)
  | .erase p pc => if pc=0 then .jump (after p)
      else (singleBinding 1).instruction (Label.erase p) (NativeErase.program pc)
  | .seal pc => (singleBinding 2).instruction Label.seal (NativeSealBack.program pc)

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program (.init pc)=MicrocodeEmbedding.instruction (singleBinding 2).ports Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem copy_code (p : Phase) (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy p pc)=MicrocodeEmbedding.instruction copyBinding.ports (Label.copy p) (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem fill_code (p : Phase) (pc : CountedFill.Label (width p))
    (hh : CountedFill.program (width p) (bit p) pc≠.halt) (_ : CountedFill.program (width p) (bit p) pc≠.reject) :
    program (.fill p pc)=MicrocodeEmbedding.instruction fillBinding.ports (Label.fill p)
      (CountedFill.program (width p) (bit p) pc) := by
  have hp : pc≠.counter 12 := by intro h;subst pc;exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem erase_code (p : Phase) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program (.erase p pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports (Label.erase p) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem seal_code (pc : NativeSealBack.Label) :
    program (.seal pc)=MicrocodeEmbedding.instruction (singleBinding 2).ports Label.seal (NativeSealBack.program pc) :=
  (singleBinding 2).instruction_eq _ _

def bank (source fuel output : Tape Bool) (p : Fin 3) : Tape Bool :=
  if p=0 then source else if p=1 then fuel else output

def cfg (pc : Label) (source fuel output : Tape Bool) (pos : Fin 3 → ℤ) : NativeMicrocode.Config (Fin 3) Label :=
  ⟨⟨pc,fun p => (bank source fuel output p).denote⟩,pos⟩

def frame (source fuel output : Tape Bool) (pos : Fin 3 → ℤ) : MicrocodeEmbedding.Frame (Fin 3) :=
  ⟨fun p => (bank source fuel output p).denote,pos⟩

def positions (origin : Fin 3 → ℤ) (acc : List Bool) (p : Fin 3) : ℤ :=
  origin p+if p=2 then (acc.length : ℤ) else 0

def start : Label := .init (.erase 0)
noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 3) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

end TransposeFollowup.ClockBuilder


/-! Physical copying, filling, erasing, initialization and sealing in the
same three-tape caller. Every helper preserves all untouched tapes. -/
namespace TransposeFollowup.ClockBuilder
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem embed_init (pc : NativeBuffer.Label) (source fuel output : Tape Bool)
    (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 2).ports Label.init
      (NativeBuffer.cfg pc output (fun _ => pos 2)).denote (frame source fuel output pos)=
      cfg (.init pc) source fuel output pos := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame cfg
  simp only [← (singleBinding 2).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_copy (phase : Phase) (pc : NativeMappedCopy.Label) (source fuel output : Tape Bool)
    (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports (Label.copy phase)
      (NativeMappedCopy.cfg pc source fuel (fun p => pos (copyBinding.ports p))) (frame source fuel output pos)=
      cfg (.copy phase pc) source fuel output pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg frame cfg
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_fill (phase : Phase) (pc : CountedFill.Label (width phase))
    (source : Tape Bool) (fuel acc : List Bool) (origin : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed fillBinding.ports (Label.fill phase)
      (CountedFill.cfg pc fuel acc (fun p => origin (fillBinding.ports p))).denote
      (frame source ⟨[],[]⟩ ⟨[],[]⟩ origin)=
      cfg (.fill phase pc) source (Counter.marked fuel) (NativeSealBack.openWord acc) (positions origin acc) := by
  unfold MicrocodeEmbedding.embed CountedFill.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [← fillBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> simp [fillBinding,FinitePortBinding.values,
    CountedFill.bank,CountedFill.positions,positions,bank]

theorem embed_erase (phase : Phase) (pc : NativeErase.Label) (source fuel output : Tape Bool)
    (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports (Label.erase phase)
      (NativeErase.cfg pc fuel (fun _ => pos 1)).denote (frame source fuel output pos)=
      cfg (.erase phase pc) source fuel output pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame cfg
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_seal (pc : NativeSealBack.Label) (source fuel output : Tape Bool)
    (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding 2).ports Label.seal
      (NativeSealBack.cfg pc output (fun _ => z)).denote (frame source fuel output pos)=
      cfg (.seal pc) source fuel output (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame cfg
  simp only [← (singleBinding 2).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem jump_trace (pc next : Label) (source fuel output : Tape Bool) (pos : Fin 3 → ℤ)
    (h : program pc=.jump next) :
    Trace 1 (cfg pc source fuel output pos) (cfg next source fuel output pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem init_call (source fuel : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2,Trace t (cfg start source fuel ⟨[],[]⟩ pos)
      (cfg (.init .done) source fuel (NativeSealBack.openWord []) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeBuffer.initialize_trace (fun _ => pos 2)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 2).ports Label.init
    NativeBuffer.program program (frame source fuel ⟨[],[]⟩ pos) init_code htr
  -- The output frame is overwritten by the embedded port.
  have e0:=embed_init (.erase 0) source fuel ⟨[],[]⟩ pos
  have e1 : MicrocodeEmbedding.embed (singleBinding 2).ports Label.init
      (NativeBuffer.cfg .done BinaryCarry.preparedOutput (fun _ => pos 2)).denote
      (frame source fuel ⟨[],[]⟩ pos)=cfg (.init .done) source fuel (NativeSealBack.openWord []) pos := by
    unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [← (singleBinding 2).values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [e0,e1,start] using he⟩

theorem copy_call (phase : Phase) (xs : List Bool) (output : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 6*xs.length+14,Trace t
      (cfg (.copy phase (.init (.erase 0))) (Counter.marked xs) ⟨[],[]⟩ output pos)
      (cfg (.copy phase (.seal .done)) (Counter.marked xs) (Counter.marked xs) output pos) := by
  obtain ⟨t,ht,htr⟩:=NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed copyBinding.ports (Label.copy phase)
    (NativeMappedCopy.program id) program (frame (Counter.marked xs) ⟨[],[]⟩ output pos) (copy_code phase) htr
  have e1 : MicrocodeEmbedding.embed copyBinding.ports (Label.copy phase)
      (NativeMappedCopy.cfg (.seal .done) (Counter.marked xs) (Counter.marked xs)
        (fun p => pos (copyBinding.ports p))) (frame (Counter.marked xs) ⟨[],[]⟩ output pos)=
      cfg (.copy phase (.seal .done)) (Counter.marked xs) (Counter.marked xs) output pos := by
    unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg frame cfg
    simp only [← copyBinding.values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [List.map_id,embed_copy,e1] using he⟩

theorem fill_call (phase : Phase) (source : Tape Bool) (fuel acc : List Bool) (origin : Fin 3 → ℤ) :
    ∃ t ≤ Counter.value fuel*(width phase+2)+8*(Counter.value fuel+1)+4*fuel.length,
      Trace t (cfg (.fill phase (.counter 0)) source (Counter.marked fuel)
          (NativeSealBack.openWord acc) (positions origin acc))
        (cfg (.fill phase (.counter 12)) source (Counter.marked (List.replicate fuel.length true))
          (NativeSealBack.openWord (acc++List.replicate (Counter.value fuel*width phase) (bit phase)))
          (positions origin (acc++List.replicate (Counter.value fuel*width phase) (bit phase)))) := by
  obtain ⟨t,ht,htr⟩:=CountedFill.fill_trace (width phase) (bit phase) fuel acc
    (fun p => origin (fillBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed fillBinding.ports (Label.fill phase)
    (CountedFill.program (width phase) (bit phase)) program (frame source ⟨[],[]⟩ ⟨[],[]⟩ origin)
    (fill_code phase) htr
  exact ⟨t,ht,by simpa only [embed_fill] using he⟩

theorem erase_call (phase : Phase) (source output : Tape Bool) (xs : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace t (cfg (.erase phase 2) source (Counter.marked xs) output pos)
      (cfg (.erase phase 0) source ⟨[],[]⟩ output pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace xs (fun _ => pos 1)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 1).ports (Label.erase phase)
    NativeErase.program program (frame source (Counter.marked xs) output pos) (erase_code phase) htr
  have e1 : MicrocodeEmbedding.embed (singleBinding 1).ports (Label.erase phase)
      (NativeErase.cfg 0 ⟨[],[]⟩ (fun _ => pos 1)).denote (frame source (Counter.marked xs) output pos)=
      cfg (.erase phase 0) source ⟨[],[]⟩ output pos := by
    unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [← (singleBinding 1).values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_erase,e1] using he⟩

theorem seal_call (source fuel : Tape Bool) (xs : List Bool) (origin : Fin 3 → ℤ) :
    ∃ t ≤ 2*xs.length+5,Trace t
      (cfg (.seal .seal) source fuel (NativeSealBack.openWord xs) (positions origin xs))
      (cfg (.seal .done) source fuel (Counter.marked xs) origin) := by
  obtain ⟨t,ht,htr⟩:=NativeSealBack.seal_trace xs (fun _ => positions origin xs 2)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 2).ports Label.seal
    NativeSealBack.program program (frame source fuel (NativeSealBack.openWord xs) (positions origin xs))
    (fun pc _ _ => seal_code pc) htr
  have e1 : MicrocodeEmbedding.embed (singleBinding 2).ports Label.seal
      (NativeSealBack.cfg .done (Counter.marked xs) (fun _ => positions origin xs 2-xs.length)).denote
      (frame source fuel (NativeSealBack.openWord xs) (positions origin xs))=
      cfg (.seal .done) source fuel (Counter.marked xs) origin := by
    unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [← (singleBinding 2).values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> simp [singleBinding,FinitePortBinding.values,bank,positions]
  exact ⟨t,ht,by simpa only [embed_seal,Function.update_eq_self,e1] using he⟩

end TransposeFollowup.ClockBuilder


/-! The whole physical clock builder, including all copies, destructive
counters, cleanup, markers and return of every head to its starting position. -/
namespace TransposeFollowup.ClockBuilder
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

def phaseWord (phase : Phase) (R : ℕ) (acc : List Bool) : List Bool :=
  acc++List.replicate (R*width phase) (bit phase)

theorem phase_trace (phase : Phase) (xs acc : List Bool) (origin : Fin 3 → ℤ) :
    ∃ t ≤ 14*xs.length+29+Counter.value xs*(width phase+10),
      Trace t (cfg (.copy phase (.init (.erase 0))) (Counter.marked xs) ⟨[],[]⟩
          (NativeSealBack.openWord acc) (positions origin acc))
        (cfg (after phase) (Counter.marked xs) ⟨[],[]⟩
          (NativeSealBack.openWord (phaseWord phase (Counter.value xs) acc))
          (positions origin (phaseWord phase (Counter.value xs) acc))) := by
  obtain ⟨a,ha,ta⟩:=copy_call phase xs (NativeSealBack.openWord acc) (positions origin acc)
  have j1:=jump_trace (.copy phase (.seal .done)) (.fill phase (.counter 0)) (Counter.marked xs)
    (Counter.marked xs) (NativeSealBack.openWord acc) (positions origin acc) rfl
  obtain ⟨b,hb,tb⟩:=fill_call phase (Counter.marked xs) xs acc origin
  let out:=phaseWord phase (Counter.value xs) acc
  have j2:=jump_trace (.fill phase (.counter 12)) (.erase phase 2) (Counter.marked xs)
    (Counter.marked (List.replicate xs.length true)) (NativeSealBack.openWord out) (positions origin out) rfl
  obtain ⟨d,hd,td⟩:=erase_call phase (Counter.marked xs) (NativeSealBack.openWord out)
    (List.replicate xs.length true) (positions origin out)
  have j3:=jump_trace (.erase phase 0) (after phase) (Counter.marked xs) ⟨[],[]⟩
    (NativeSealBack.openWord out) (positions origin out) rfl
  refine ⟨a+(1+(b+(1+(d+1)))),?_,NativeCountedLoop.trace_trans ta (NativeCountedLoop.trace_trans j1
    (NativeCountedLoop.trace_trans tb (NativeCountedLoop.trace_trans j2 (NativeCountedLoop.trace_trans td j3))))⟩
  simp only [List.length_replicate] at hd
  simp only [Nat.mul_succ] at hb ⊢
  omega

theorem phases_word (R : ℕ) :
    phaseWord .tail R (phaseWord .middle R (phaseWord .lead R []))=SevenPhaseClock.word R := by
  simp [phaseWord,width,bit,SevenPhaseClock.word,Nat.mul_comm]

theorem clock_trace (xs : List Bool) (origin : Fin 3 → ℤ) :
    ∃ t ≤ 51*Counter.value xs+42*xs.length+95,
      Trace t (cfg start (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ origin)
        (cfg (.seal .done) (Counter.marked xs) ⟨[],[]⟩ (Counter.marked (SevenPhaseClock.word (Counter.value xs))) origin) := by
  let R:=Counter.value xs
  let a1:=phaseWord .lead R []
  let a2:=phaseWord .middle R a1
  obtain ⟨a,ha,ta⟩:=init_call (Counter.marked xs) ⟨[],[]⟩ origin
  have j:=jump_trace (.init .done) (.copy .lead (.init (.erase 0))) (Counter.marked xs) ⟨[],[]⟩
    (NativeSealBack.openWord []) origin rfl
  obtain ⟨b,hb,tb⟩:=phase_trace .lead xs [] origin
  have hp : positions origin []=origin := by funext p;simp [positions]
  rw [hp] at tb
  obtain ⟨c,hc,tc⟩:=phase_trace .middle xs a1 origin
  obtain ⟨d,hd,td⟩:=phase_trace .tail xs a2 origin
  have hw : phaseWord .tail (Counter.value xs) a2=SevenPhaseClock.word (Counter.value xs):=phases_word _
  rw [hw] at td
  obtain ⟨e,he,te⟩:=seal_call (Counter.marked xs) ⟨[],[]⟩ (SevenPhaseClock.word (Counter.value xs)) origin
  refine ⟨a+(1+(b+(c+(d+e)))),?_,NativeCountedLoop.trace_trans ta (NativeCountedLoop.trace_trans j
    (NativeCountedLoop.trace_trans tb (NativeCountedLoop.trace_trans tc (NativeCountedLoop.trace_trans td te))))⟩
  simp only [width] at hb hc hd
  rw [SevenPhaseClock.word_length] at he
  omega

theorem native_clock (xs : List Bool) (origin : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 51*Counter.value xs+42*xs.length+95,
      Transpose.stepN nativeMachine input t
        ((cfg start (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ origin).denote nativeEncoding program inputPos outRev)=
        some ((cfg (.seal .done) (Counter.marked xs) ⟨[],[]⟩
          (Counter.marked (SevenPhaseClock.word (Counter.value xs))) origin).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input ((cfg (.seal .done) (Counter.marked xs) ⟨[],[]⟩
          (Counter.marked (SevenPhaseClock.word (Counter.value xs))) origin).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩:=clock_trace xs origin
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=161 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=161
  decide +kernel

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 3 ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (origin : Fin 3 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 51*Counter.value xs+42*xs.length+95,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ origin)
          outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg (.seal .done) (Counter.marked xs) ⟨[],[]⟩
          (Counter.marked (SevenPhaseClock.word (Counter.value xs))) origin) outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=clock_trace xs origin
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.ClockBuilder


/-! Exact words and sufficient width for the paid radius builder. The
entry-bit word is multiplication fuel, so its width need not equal that of N. -/
namespace TransposeFollowup.RadiusBuilder
open FixedTapeCompiler
set_option autoImplicit false

def padding (K : ℕ) : ℕ:=K.size+4
def width (K : ℕ) (xs : List Bool) : ℕ:=2*xs.length+padding K
def bitWord (xs : List Bool) : List Bool:=MeasuredWord.result (Transpose.entryBits (Counter.value xs))
def factor (K : ℕ) (xs : List Bool) : List Bool:=PaddedWord.word (padding K) id xs
def product (K : ℕ) (xs : List Bool) : List Bool:=DimensionScale.output (bitWord xs) (factor K xs)
def numerator (K : ℕ) (xs : List Bool) : List Bool:=
  RepeatedAdd.repeatWord (ArithmeticSeed.one (width K xs)) 2 (product K xs)
def quotient (K : ℕ) (xs : List Bool) : List Bool:=(NativeDivideThree.divide (numerator K xs) 0).1
def result (K : ℕ) (xs : List Bool) : List Bool:=
  RepeatedAdd.repeatWord (quotient K xs) K (ArithmeticSeed.zeros (width K xs))

theorem width_positive (K : ℕ) (xs : List Bool) : 0<width K xs := by unfold width padding;omega

theorem factor_length (K : ℕ) (xs : List Bool) : (factor K xs).length=width K xs :=
  PaddedWord.word_length _ _ _
theorem factor_value (K : ℕ) (xs : List Bool) : Counter.value (factor K xs)=Counter.value xs :=
  PaddedWord.identity_value _ _
theorem bitWord_length (xs : List Bool) : (bitWord xs).length=Transpose.entryBits (Counter.value xs) :=
  MeasuredWord.result_length _
theorem bitWord_value (xs : List Bool) : Counter.value (bitWord xs)=Transpose.entryBits (Counter.value xs) :=
  MeasuredWord.result_value _
theorem product_length (K : ℕ) (xs : List Bool) : (product K xs).length=width K xs := by
  rw [product,DimensionScale.output_length,factor_length]
theorem numerator_length (K : ℕ) (xs : List Bool) : (numerator K xs).length=width K xs := by
  unfold numerator
  rw [RepeatedAdd.repeatWord_length _ _ _ (by rw [product_length,ArithmeticSeed.one_length _ (width_positive K xs)]),
    ArithmeticSeed.one_length _ (width_positive K xs)]
theorem quotient_length (K : ℕ) (xs : List Bool) : (quotient K xs).length=width K xs := by
  rw [quotient,NativeDivideThree.divide_length,numerator_length]
theorem result_length (K : ℕ) (xs : List Bool) : (result K xs).length=width K xs := by
  unfold result
  rw [RepeatedAdd.repeatWord_length _ _ _ (by simp [ArithmeticSeed.zeros,quotient_length]),quotient_length]

theorem numerator_small (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value xs*Transpose.entryBits (Counter.value xs)+2 < (2^xs.length)^2 := by
  have hv : Counter.value xs<2^xs.length := by rw [NativeCounter.word_value];exact BinaryCarry.value_lt xs
  have hb:=Transpose.Tape.Impl.entryBits_le_self (show 1 ≤ Counter.value xs by omega)
  have hn : Counter.value xs+1 ≤ 2^xs.length := by omega
  nlinarith

theorem width_power (K : ℕ) (xs : List Bool) :
    2^width K xs=(2^xs.length)^2*2^K.size*16 := by
  rw [show width K xs = xs.length*2+K.size+4 by unfold width padding; omega,
    pow_add,pow_add,pow_mul]
  norm_num

theorem numerator_fit (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value xs*Transpose.entryBits (Counter.value xs)+2<2^width K xs := by
  have hn:=numerator_small xs hx
  have hb : 1 ≤ 2^K.size:=Nat.one_le_pow _ _ (by omega)
  rw [width_power]
  nlinarith [Nat.mul_le_mul_left ((2^xs.length)^2) hb]

theorem product_fit (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (bitWord xs)*Counter.value (factor K xs)<2^(factor K xs).length := by
  rw [bitWord_value,factor_value,factor_length]
  have h:=numerator_fit K xs hx
  nlinarith

theorem product_value (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (product K xs)=Counter.value xs*Transpose.entryBits (Counter.value xs) := by
  rw [product,DimensionScale.output_value_exact _ _ (product_fit K xs hx),bitWord_value,factor_value,Nat.mul_comm]

theorem numerator_value (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (numerator K xs)=Counter.value xs*Transpose.entryBits (Counter.value xs)+2 := by
  have hf : BinaryCompare.value (product K xs)+2*BinaryCompare.value (ArithmeticSeed.one (width K xs))<
      2^(ArithmeticSeed.one (width K xs)).length := by
    simpa only [← NativeCounter.word_value,product_value K xs hx,ArithmeticSeed.one_value,Nat.mul_one,
      ArithmeticSeed.one_length _ (width_positive K xs)] using numerator_fit K xs hx
  have h:=RepeatedAdd.repeatWord_value_exact (ArithmeticSeed.one (width K xs)) 2 (product K xs)
    (by rw [product_length,ArithmeticSeed.one_length _ (width_positive K xs)]) hf
  simpa only [numerator,← NativeCounter.word_value,product_value K xs hx,ArithmeticSeed.one_value,Nat.mul_one] using h

theorem quotient_value (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (quotient K xs)=Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs) := by
  rw [quotient,NativeDivideThree.divide_value,numerator_value K xs hx]
  unfold Transpose.Tape.TSDiagram.blockSize
  congr 1

theorem radius_fit (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    K*Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs)<2^width K xs := by
  have hk:=Nat.lt_size_self K
  have hn:=numerator_small xs hx
  have hq : Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs) ≤
      Counter.value xs*Transpose.entryBits (Counter.value xs)+2 := by
    unfold Transpose.Tape.TSDiagram.blockSize
    have h:=Nat.div_le_self (Counter.value xs*Transpose.entryBits (Counter.value xs)+3-1) 3
    omega
  have h1:=Nat.mul_le_mul_left K (hq.trans (Nat.le_of_lt hn))
  have h2:=Nat.mul_lt_mul_of_pos_right hk (show 0<(2^xs.length)^2 by positivity)
  rw [width_power]
  nlinarith

theorem result_value (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    Counter.value (result K xs)=K*Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs) := by
  have hf : BinaryCompare.value (ArithmeticSeed.zeros (width K xs))+K*BinaryCompare.value (quotient K xs)<
      2^(quotient K xs).length := by
    simpa only [← NativeCounter.word_value,ArithmeticSeed.zeros,PaddedWord.value_zeroes,Nat.zero_add,
      quotient_value K xs hx,quotient_length] using radius_fit K xs hx
  have h:=RepeatedAdd.repeatWord_value_exact (quotient K xs) K (ArithmeticSeed.zeros (width K xs))
    (by simp [ArithmeticSeed.zeros,quotient_length]) hf
  simpa only [result,← NativeCounter.word_value,ArithmeticSeed.zeros,PaddedWord.value_zeroes,Nat.zero_add,
    quotient_value K xs hx] using h

/- The bound is discharged by the composed native trace. Keeping its
growth estimate here separates the arithmetic estimate from execution. -/
def budget (K : ℕ) (xs : List Bool) : ℕ :=
  96*xs.length+17*padding K+62*width K xs+
    Transpose.entryBits (Counter.value xs)*(18*width K xs+57)+K*(18*width K xs+52)+369

def linearConstant (K : ℕ) : ℕ := 682+97*padding K+K*(88+18*padding K)

theorem budget_linear (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs)
    (hl : xs.length ≤ Counter.value xs) :
    budget K xs ≤ linearConstant K*(Counter.value xs*Transpose.entryBits (Counter.value xs)) := by
  let N:=Counter.value xs
  let b:=Transpose.entryBits N
  let P:=N*b
  have hn : 1 ≤ N:=hx
  have hb : 1 ≤ b:=by simp only [b,EntryBits.entryBits_eq];omega
  have hnP : N ≤ P:=by dsimp [P];nlinarith
  have hbP : b ≤ P:=by dsimp [P];nlinarith
  have hP : 1 ≤ P:=by omega
  have hlP : xs.length ≤ P:=hl.trans hnP
  have hlb : xs.length*b ≤ P:=Nat.mul_le_mul_right b hl
  have hm : width K xs ≤ (2+padding K)*P:=by
    unfold width
    have hc:=Nat.mul_le_mul_left (padding K) hP
    nlinarith
  have hbm : b*width K xs ≤ (2+padding K)*P:=by
    unfold width
    have hc:=Nat.mul_le_mul_left (padding K) hbP
    nlinarith
  have h96:=Nat.mul_le_mul_left 96 hlP
  have h17:=Nat.mul_le_mul_left (17*padding K) hP
  have h62:=Nat.mul_le_mul_left 62 hm
  have h18:=Nat.mul_le_mul_left 18 hbm
  have h57:=Nat.mul_le_mul_left 57 hbP
  have hK:=Nat.mul_le_mul_left K (show 18*width K xs+52 ≤ (88+18*padding K)*P by nlinarith)
  have h369:=Nat.mul_le_mul_left 369 hP
  change 96*xs.length+17*padding K+62*width K xs+b*(18*width K xs+57)+K*(18*width K xs+52)+369 ≤ _
  change _ ≤ (682+97*padding K+K*(88+18*padding K))*P
  nlinarith

end TransposeFollowup.RadiusBuilder


/-! Eleven fixed tapes, with no input-dependent data in control. The source
is preserved. Entry bits fuel the product; both fixed multipliers reuse the
same one-bit fuel, unit/zero templates, and prepared scratch. -/
namespace TransposeFollowup.RadiusBuilder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | source | bits | product | counter | number | zero | result | one | fuel | left | right
  deriving DecidableEq
instance : Fintype Port where
  elems:={.source,.bits,.product,.counter,.number,.zero,.result,.one,.fuel,.left,.right}
  complete:=by intro p;cases p <;> simp
abbrev Bank:=Port → Tape Bool

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun q => if q=p then some 0 else none
  decode_spec:=by
    intro q i
    change (if q=p then some 0 else none)=some i ↔ p=q
    fin_cases i
    by_cases h : q=p
    · subst q;simp
    · simp [h,Ne.symm h]

def entryBinding : FinitePortBinding EntryBits.Port Port where
  ports:=⟨![.source,.product,.counter,.bits],by decide +kernel⟩
  decode:=fun p => match p with
    | .source => some 0 | .product => some 1 | .counter => some 2 | .bits => some 3 | _ => none
  decode_spec:=by intro p t;cases p <;> fin_cases t <;> decide +kernel

def seedPort : ArithmeticSeed.Port → Port
  | .source => .source | .number => .number | .zeroA => .zero | .zeroB => .result
  | .one => .one | .fuel => .fuel | .left => .left | .right => .right

def seedBinding : FinitePortBinding ArithmeticSeed.Port Port where
  ports:=⟨seedPort,by intro p q h;cases p <;> cases q <;> simp_all [seedPort]⟩
  decode:=fun p => match p with
    | .source => some .source | .number => some .number | .zero => some .zeroA | .result => some .zeroB
    | .one => some .one | .fuel => some .fuel | .left => some .left | .right => some .right | _ => none
  decode_spec:=by intro p t;cases p <;> cases t <;> decide +kernel

def scalePort : DimensionScale.Port → Port
  | .dimension => .bits | .factor => .number | .zero => .zero
  | .scratch => .left | .fuel => .counter | .out => .product

def scaleBinding : FinitePortBinding DimensionScale.Port Port where
  ports:=⟨scalePort,by intro p q h;cases p <;> cases q <;> simp_all [scalePort]⟩
  decode:=fun p => match p with
    | .bits => some .dimension | .number => some .factor | .zero => some .zero
    | .left => some .scratch | .counter => some .fuel | .product => some .out | _ => none
  decode_spec:=by intro p t;cases p <;> cases t <;> decide +kernel

def multiplyPort (isFinal : Bool) : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => if isFinal then .result else .product
  | .factor => if isFinal then .product else .one | .scratch => .left | .zero => .zero

def multiplyBinding (isFinal : Bool) : FinitePortBinding RepeatedAdd.Port Port where
  ports:=⟨multiplyPort isFinal,by intro p q h;cases isFinal <;> cases p <;> cases q <;> simp_all [multiplyPort]⟩
  decode:=fun p => if p=.fuel then some .fuel else if p=(if isFinal then .result else .product) then some .acc
    else if p=(if isFinal then .product else .one) then some .factor
    else if p=.left then some .scratch else if p=.zero then some .zero else none
  decode_spec:=by intro p t;cases isFinal <;> cases p <;> cases t <;> decide +kernel

def erasePorts : Fin 6 ↪ Port:=⟨![.bits,.product,.number,.zero,.one,.fuel],by decide +kernel⟩
def identityBinding : FinitePortBinding Port Port where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p t;simp [eq_comm]

inductive Label (K : ℕ)
  | entry (pc : EntryBits.Label)
  | seed (pc : ArithmeticSeed.Label (padding K))
  | scale (pc : DimensionScale.Label)
  | add (pc : FixedMultiple.Label 2)
  | divide (pc : NativeDivideThree.Label)
  | multiply (pc : FixedMultiple.Label K)
  | erase (pc : NativeBatchErase.Label 6)
  | clear (right : Bool) (pc : NativeUnprepare.Label)
  | done
  deriving DecidableEq,Fintype

def start (K : ℕ) : Label K:=.entry EntryBits.start

def program (K : ℕ) : Microcode.Program Port (Label K)
  | .entry .done => .jump (.seed (.pad false (.init (.erase 0))))
  | .entry pc => entryBinding.instruction Label.entry (EntryBits.program pc)
  | .seed .done => .jump (.scale DimensionScale.start)
  | .seed pc => seedBinding.instruction Label.seed (ArithmeticSeed.program (padding K) pc)
  | .scale .done => .jump (.add (FixedMultiple.start 2))
  | .scale pc => scaleBinding.instruction Label.scale (DimensionScale.program pc)
  | .add .done => .jump (.divide .scan)
  | .add pc => (multiplyBinding false).instruction Label.add (FixedMultiple.program 2 pc)
  | .divide (.done _) => .jump (.multiply (FixedMultiple.start K))
  | .divide pc => (singleBinding .product).instruction Label.divide (NativeDivideThree.program pc)
  | .multiply .done => .jump (.erase (NativeBatchErase.entry 6 0))
  | .multiply pc => (multiplyBinding true).instruction Label.multiply (FixedMultiple.program K pc)
  | .erase .done => .jump (.clear false 0)
  | .erase pc => identityBinding.instruction Label.erase (NativeBatchErase.program erasePorts pc)
  | .clear r pc => if pc=2 then .jump (if r then .done else .clear true 0)
      else (singleBinding (if r then .right else .left)).instruction (Label.clear r) (NativeUnprepare.program pc)
  | .done => .halt

theorem entry_code (K : ℕ) (pc : EntryBits.Label) (hh : EntryBits.program pc≠.halt)
    (_ : EntryBits.program pc≠.reject) :
    program K (.entry pc)=MicrocodeEmbedding.instruction entryBinding.ports Label.entry (EntryBits.program pc) := by
  cases pc <;> simp_all [program,EntryBits.program,FinitePortBinding.instruction_eq]

theorem seed_code (K : ℕ) (pc : ArithmeticSeed.Label (padding K)) (hh : ArithmeticSeed.program (padding K) pc≠.halt)
    (_ : ArithmeticSeed.program (padding K) pc≠.reject) :
    program K (.seed pc)=MicrocodeEmbedding.instruction seedBinding.ports Label.seed (ArithmeticSeed.program (padding K) pc) := by
  cases pc <;> simp_all [program,ArithmeticSeed.program,FinitePortBinding.instruction_eq]

theorem scale_code (K : ℕ) (pc : DimensionScale.Label) (hh : DimensionScale.program pc≠.halt)
    (_ : DimensionScale.program pc≠.reject) :
    program K (.scale pc)=MicrocodeEmbedding.instruction scaleBinding.ports Label.scale (DimensionScale.program pc) := by
  cases pc <;> simp_all [program,DimensionScale.program,FinitePortBinding.instruction_eq]

theorem add_code (K : ℕ) (pc : FixedMultiple.Label 2) (hh : FixedMultiple.program 2 pc≠.halt)
    (_ : FixedMultiple.program 2 pc≠.reject) :
    program K (.add pc)=MicrocodeEmbedding.instruction (multiplyBinding false).ports Label.add (FixedMultiple.program 2 pc) := by
  cases pc <;> simp_all [program,FixedMultiple.program,FinitePortBinding.instruction_eq]

theorem divide_code (K : ℕ) (pc : NativeDivideThree.Label) (hh : NativeDivideThree.program pc≠.halt)
    (_ : NativeDivideThree.program pc≠.reject) :
    program K (.divide pc)=MicrocodeEmbedding.instruction (singleBinding .product).ports Label.divide (NativeDivideThree.program pc) := by
  cases pc <;> simp_all [program,NativeDivideThree.program,FinitePortBinding.instruction_eq]

theorem multiply_code (K : ℕ) (pc : FixedMultiple.Label K) (hh : FixedMultiple.program K pc≠.halt)
    (_ : FixedMultiple.program K pc≠.reject) :
    program K (.multiply pc)=MicrocodeEmbedding.instruction (multiplyBinding true).ports Label.multiply (FixedMultiple.program K pc) := by
  cases pc <;> simp_all [program,FixedMultiple.program,FinitePortBinding.instruction_eq]

theorem erase_code (K : ℕ) (pc : NativeBatchErase.Label 6) (hh : NativeBatchErase.program erasePorts pc≠.halt)
    (_ : NativeBatchErase.program erasePorts pc≠.reject) :
    program K (.erase pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.erase (NativeBatchErase.program erasePorts pc) := by
  cases pc <;> simp_all [program,NativeBatchErase.program,FinitePortBinding.instruction_eq]

theorem clear_code (K : ℕ) (r : Bool) (pc : NativeUnprepare.Label)
    (hh : NativeUnprepare.program pc≠.halt) (_ : NativeUnprepare.program pc≠.reject) :
    program K (.clear r pc)=MicrocodeEmbedding.instruction (singleBinding (if r then .right else .left)).ports
      (Label.clear r) (NativeUnprepare.program pc) := by
  have hp : pc≠2:=by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg {K : ℕ} (pc : Label K) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label K):=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port:=⟨fun p => (s p).denote,pos⟩
abbrev Trace (K : ℕ):=OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K))
noncomputable def nativeEncoding (K : ℕ):=NativeMicrocode.initialEncoding (T:=Port) (start K)
noncomputable def nativeMachine (K : ℕ):=NativeMicrocode.machine (nativeEncoding K) (program K)

end TransposeFollowup.RadiusBuilder


/-! Exact boundary banks, including every blank and prepared marker. -/
namespace TransposeFollowup.RadiusBuilder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def initial (xs : List Bool) : Bank:=fun p => if p=.source then Counter.marked xs else ⟨[],[]⟩
def measured (xs : List Bool) : Bank:=Function.update (initial xs) .bits (Counter.marked (bitWord xs))

def stage (K : ℕ) (xs : List Bool) (work : Tape Bool) (answer : List Bool) : Bank
  | .source => Counter.marked xs | .bits => Counter.marked (bitWord xs)
  | .product => work | .counter => ⟨[],[]⟩ | .number => Counter.marked (factor K xs)
  | .zero => Counter.marked (ArithmeticSeed.zeros (width K xs))
  | .result => Counter.marked answer | .one => Counter.marked (ArithmeticSeed.one (width K xs))
  | .fuel => Counter.marked [true] | .left | .right => BinaryCarry.preparedOutput

def seeded (K : ℕ) (xs : List Bool) : Bank:=stage K xs ⟨[],[]⟩ (ArithmeticSeed.zeros (width K xs))
def scaled (K : ℕ) (xs : List Bool) : Bank:=stage K xs (Counter.marked (product K xs)) (ArithmeticSeed.zeros (width K xs))
def added (K : ℕ) (xs : List Bool) : Bank:=stage K xs (Counter.marked (numerator K xs)) (ArithmeticSeed.zeros (width K xs))
def divided (K : ℕ) (xs : List Bool) : Bank:=stage K xs (Counter.marked (quotient K xs)) (ArithmeticSeed.zeros (width K xs))
def multiplied (K : ℕ) (xs : List Bool) : Bank:=stage K xs (Counter.marked (quotient K xs)) (result K xs)

def clean (K : ℕ) (xs : List Bool) : Bank
  | .source => Counter.marked xs | .result => Counter.marked (result K xs)
  | .left | .right => BinaryCarry.preparedOutput | _ => ⟨[],[]⟩
def halfClean (K : ℕ) (xs : List Bool) : Bank:=Function.update (clean K xs) .left ⟨[],[]⟩
def final (K : ℕ) (xs : List Bool) : Bank
  | .source => Counter.marked xs | .result => Counter.marked (result K xs) | _ => ⟨[],[]⟩

def eraseWords (K : ℕ) (xs : List Bool) : Fin 6 → List Bool:=
  ![bitWord xs,quotient K xs,factor K xs,ArithmeticSeed.zeros (width K xs),ArithmeticSeed.one (width K xs),[true]]

theorem erase_words (K : ℕ) (xs : List Bool) (j : Fin 6) :
    multiplied K xs (erasePorts j)=Counter.marked (eraseWords K xs j) := by
  fin_cases j <;> rfl

theorem erase_final (K : ℕ) (xs : List Bool) :
    NativeBatchErase.stage erasePorts (multiplied K xs) 6=clean K xs := by
  funext p
  cases p
  all_goals simp [NativeBatchErase.stage,erasePorts,Fin.exists_fin_succ,multiplied,stage,clean]

theorem erase_budget (K : ℕ) (xs : List Bool) :
    (∑ j : Fin 6,(4*(eraseWords K xs j).length+5))=
      4*Transpose.entryBits (Counter.value xs)+16*width K xs+34 := by
  simp only [Fin.sum_univ_succ,eraseWords,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,bitWord_length,quotient_length,factor_length,ArithmeticSeed.zeros,
    List.length_replicate,ArithmeticSeed.one_length _ (width_positive K xs),List.length_cons,List.length_nil]
  omega

end TransposeFollowup.RadiusBuilder


/-! Framed native calls for all stages of the radius calculation. -/
namespace TransposeFollowup.RadiusBuilder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_bank {U J : Type*} (K : ℕ) (binding : FinitePortBinding U Port)
    (labels : J → Label K) (pc : J) (inner : U → Tape Bool) (outer : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed binding.ports labels
      (⟨⟨pc,fun p => (inner p).denote⟩,fun p => pos (binding.ports p)⟩ : NativeMicrocode.Config U J)
      (frame outer pos)=cfg (labels pc) (binding.values inner outer) pos := by
  exact binding.embed_bank_project _ _ _ _ _

theorem jump_trace (K : ℕ) (pc next : Label K) (s : Bank) (pos : Port → ℤ)
    (h : program K pc=.jump next) : Trace K 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem entry_call (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ 50*xs.length+87,Trace K t (cfg (start K) (initial xs) pos)
      (cfg (.entry .done) (measured xs) pos) := by
  obtain ⟨t,ht,htr⟩:=EntryBits.complete_trace xs hx (fun p => pos (entryBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed entryBinding.ports Label.entry EntryBits.program
    (program K) (frame (initial xs) pos) (entry_code K) htr
  have hi : entryBinding.values (EntryBits.initial xs) (initial xs)=initial xs:=by
    funext p;cases p <;> rfl
  have hf : entryBinding.values (EntryBits.final xs) (initial xs)=measured xs:=by
    funext p;cases p <;> rfl
  exact ⟨t,ht,by simpa only [EntryBits.cfg,embed_bank,hi,hf,start] using he⟩

theorem seed_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 46*xs.length+17*padding K+81,Trace K t
      (cfg (.seed (.pad false (.init (.erase 0)))) (measured xs) pos)
      (cfg (.seed .done) (seeded K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=ArithmeticSeed.seed_trace (padding K) xs (width_positive K xs)
    (fun p => pos (seedBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed seedBinding.ports Label.seed (ArithmeticSeed.program (padding K))
    (program K) (frame (measured xs) pos) (seed_code K) htr
  have hi : seedBinding.values (ArithmeticSeed.initial xs).tapes (measured xs)=measured xs:=by
    funext p;cases p <;> rfl
  have hf : seedBinding.values (ArithmeticSeed.ready (padding K) xs).tapes (measured xs)=seeded K xs:=by
    funext p;cases p <;> rfl
  exact ⟨t,ht,by simpa only [ArithmeticSeed.cfg,embed_bank,hi,hf] using he⟩

theorem scale_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ Transpose.entryBits (Counter.value xs)*(18*width K xs+39)+
        14*Transpose.entryBits (Counter.value xs)+6*width K xs+44,
      Trace K t (cfg (.scale DimensionScale.start) (seeded K xs) pos)
        (cfg (.scale .done) (scaled K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=DimensionScale.complete_trace (bitWord xs) (factor K xs)
    (fun p => pos (scaleBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed scaleBinding.ports Label.scale DimensionScale.program
    (program K) (frame (seeded K xs) pos) (scale_code K) htr
  have hi : scaleBinding.values (DimensionScale.initial (bitWord xs) (factor K xs)).tapes (seeded K xs)=seeded K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,scaleBinding,DimensionScale.initial,DimensionScale.Bank.tapes,
      seeded,stage,factor_length]
  have hf : scaleBinding.values (DimensionScale.final (bitWord xs) (factor K xs)).tapes (seeded K xs)=scaled K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,scaleBinding,DimensionScale.final,DimensionScale.initial,
      DimensionScale.Bank.tapes,seeded,scaled,stage,product,factor_length]
  refine ⟨t,?_,by simpa only [DimensionScale.cfg,embed_bank,hi,hf] using he⟩
  simpa only [DimensionScale.budget_expansion,bitWord_value,bitWord_length,factor_length] using ht

theorem add_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 36*width K xs+105,Trace K t (cfg (.add (FixedMultiple.start 2)) (scaled K xs) pos)
      (cfg (.add .done) (added K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=FixedMultiple.multiple_trace 2 (product K xs) (ArithmeticSeed.one (width K xs))
    (by rw [product_length,ArithmeticSeed.one_length _ (width_positive K xs)])
    (fun p => pos ((multiplyBinding false).ports p))
  have he:=MicrocodeEmbedding.trace_embed (multiplyBinding false).ports Label.add (FixedMultiple.program 2)
    (program K) (frame (scaled K xs) pos) (add_code K) htr
  have hi : (multiplyBinding false).values (RepeatedAdd.ready [true] (product K xs) (ArithmeticSeed.one (width K xs))).tapes
      (scaled K xs)=scaled K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,multiplyBinding,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
      scaled,stage,ArithmeticSeed.one_length _ (width_positive K xs),ArithmeticSeed.zeros] <;> rfl
  have hf : (multiplyBinding false).values
      (RepeatedAdd.ready [true] (numerator K xs) (ArithmeticSeed.one (width K xs))).tapes (scaled K xs)=added K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,multiplyBinding,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
      scaled,added,stage,ArithmeticSeed.one_length _ (width_positive K xs),ArithmeticSeed.zeros] <;> rfl
  unfold numerator at hf
  refine ⟨t,?_,by simpa only [FixedMultiple.cfg,embed_bank,hi,hf] using he⟩
  simp only [FixedMultiple.budget,ArithmeticSeed.one_length _ (width_positive K xs)] at ht
  omega

theorem divide_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*width K xs+4,Trace K t (cfg (.divide .scan) (added K xs) pos)
      (cfg (.divide (.done (NativeDivideThree.divide (numerator K xs) 0).2)) (divided K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeDivideThree.complete_trace (numerator K xs) (fun p => pos ((singleBinding .product).ports p))
  have he:=MicrocodeEmbedding.trace_embed (singleBinding .product).ports Label.divide NativeDivideThree.program
    (program K) (frame (added K xs) pos) (divide_code K) htr
  have hi : (singleBinding .product).values (fun _ => Counter.marked (numerator K xs)) (added K xs)=added K xs:=by
    funext p;cases p <;> rfl
  have hf : (singleBinding .product).values (fun _ => Counter.marked (quotient K xs)) (added K xs)=divided K xs:=by
    funext p;cases p <;> rfl
  refine ⟨t,by simpa only [numerator_length] using ht,?_⟩
  unfold quotient at hf
  simpa only [NativeDivideThree.cfg,NativeZipper.Config.denote,Microcode.Config.denote,embed_bank,hi,hf] using he

theorem multiply_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ K*(18*width K xs+52)+1,Trace K t
      (cfg (.multiply (FixedMultiple.start K)) (divided K xs) pos)
      (cfg (.multiply .done) (multiplied K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=FixedMultiple.multiple_trace K (ArithmeticSeed.zeros (width K xs)) (quotient K xs)
    (by simp [ArithmeticSeed.zeros,quotient_length]) (fun p => pos ((multiplyBinding true).ports p))
  have he:=MicrocodeEmbedding.trace_embed (multiplyBinding true).ports Label.multiply (FixedMultiple.program K)
    (program K) (frame (divided K xs) pos) (multiply_code K) htr
  have hi : (multiplyBinding true).values (RepeatedAdd.ready [true] (ArithmeticSeed.zeros (width K xs)) (quotient K xs)).tapes
      (divided K xs)=divided K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,multiplyBinding,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
      divided,stage,quotient_length,ArithmeticSeed.zeros] <;> rfl
  have hf : (multiplyBinding true).values (RepeatedAdd.ready [true] (result K xs) (quotient K xs)).tapes
      (divided K xs)=multiplied K xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,multiplyBinding,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
      divided,multiplied,stage,quotient_length,ArithmeticSeed.zeros] <;> rfl
  unfold result at hf
  exact ⟨t,by simpa only [FixedMultiple.budget,quotient_length] using ht,
    by simpa only [FixedMultiple.cfg,embed_bank,hi,hf] using he⟩

theorem erase_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*Transpose.entryBits (Counter.value xs)+16*width K xs+34,Trace K t
      (cfg (.erase (NativeBatchErase.entry 6 0)) (multiplied K xs) pos)
      (cfg (.erase .done) (clean K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeBatchErase.complete_trace erasePorts (eraseWords K xs) (multiplied K xs) (erase_words K xs) pos
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports Label.erase (NativeBatchErase.program erasePorts)
    (program K) (frame (multiplied K xs) pos) (erase_code K) htr
  have hi : identityBinding.values (multiplied K xs) (multiplied K xs)=multiplied K xs:=rfl
  have hf : identityBinding.values (clean K xs) (multiplied K xs)=clean K xs:=rfl
  change OperationalTrace.Trace _ _ t
    (MicrocodeEmbedding.embed identityBinding.ports Label.erase
      ⟨⟨NativeBatchErase.entry 6 0,fun p => (multiplied K xs p).denote⟩,fun p => pos (identityBinding.ports p)⟩
      (frame (multiplied K xs) pos))
    (MicrocodeEmbedding.embed identityBinding.ports Label.erase
      ⟨⟨NativeBatchErase.Label.done,fun p => (NativeBatchErase.stage erasePorts (multiplied K xs) 6 p).denote⟩,
        fun p => pos (identityBinding.ports p)⟩ (frame (multiplied K xs) pos)) at he
  exact ⟨t,by simpa only [erase_budget] using ht,
    by simpa only [NativeBatchErase.cfg,embed_bank,erase_final,hi,hf] using he⟩

theorem clear_call (K : ℕ) (r : Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s (if r then .right else .left)=BinaryCarry.preparedOutput) :
    ∃ t ≤ 2,Trace K t (cfg (.clear r 0) s pos)
      (cfg (.clear r 2) (Function.update s (if r then .right else .left) ⟨[],[]⟩) pos) := by
  let port : Port:=if r then .right else .left
  obtain ⟨t,ht,htr⟩:=NativeUnprepare.complete_trace (fun p => pos ((singleBinding port).ports p))
  have he:=MicrocodeEmbedding.trace_embed (singleBinding port).ports (Label.clear r) NativeUnprepare.program
    (program K) (frame s pos) (clear_code K r) htr
  have hi : (singleBinding port).values (fun _ => BinaryCarry.preparedOutput) s=s:=by
    funext p;by_cases h : p=port
    · subst p;simpa [FinitePortBinding.values,singleBinding] using hs.symm
    · simp [FinitePortBinding.values,singleBinding,h]
  have hf : (singleBinding port).values (fun _ => (⟨[],[]⟩ : Tape Bool)) s=Function.update s port ⟨[],[]⟩:=by
    funext p;by_cases h : p=port <;> simp [FinitePortBinding.values,singleBinding,Function.update,h]
  exact ⟨t,ht,by simpa only [NativeUnprepare.cfg,NativeZipper.Config.denote,Microcode.Config.denote,embed_bank,hi,hf] using he⟩

end TransposeFollowup.RadiusBuilder


/-! Complete paid radius computation from a retained dimension word and
blank auxiliary tapes. All transfers, markers and erasures are charged. -/
namespace TransposeFollowup.RadiusBuilder
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem complete_trace (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ budget K xs,Trace K t (cfg (start K) (initial xs) pos) (cfg .done (final K xs) pos) := by
  obtain ⟨a,ha,ta⟩:=entry_call K xs hx pos
  have ja:=jump_trace K (.entry .done) (.seed (.pad false (.init (.erase 0)))) (measured xs) pos rfl
  obtain ⟨b,hb,tb⟩:=seed_call K xs pos
  have jb:=jump_trace K (.seed .done) (.scale DimensionScale.start) (seeded K xs) pos rfl
  obtain ⟨c,hc,tc⟩:=scale_call K xs pos
  have jc:=jump_trace K (.scale .done) (.add (FixedMultiple.start 2)) (scaled K xs) pos rfl
  obtain ⟨d,hd,td⟩:=add_call K xs pos
  have jd:=jump_trace K (.add .done) (.divide .scan) (added K xs) pos rfl
  obtain ⟨e,he,te⟩:=divide_call K xs pos
  have je:=jump_trace K (.divide (.done (NativeDivideThree.divide (numerator K xs) 0).2))
    (.multiply (FixedMultiple.start K)) (divided K xs) pos rfl
  obtain ⟨f,hf,tf⟩:=multiply_call K xs pos
  have jf:=jump_trace K (.multiply .done) (.erase (NativeBatchErase.entry 6 0)) (multiplied K xs) pos rfl
  obtain ⟨g,hg,tg⟩:=erase_call K xs pos
  have jg:=jump_trace K (.erase .done) (.clear false 0) (clean K xs) pos rfl
  obtain ⟨h,hh,th⟩:=clear_call K false (clean K xs) pos rfl
  change Trace K h (cfg (.clear false 0) (clean K xs) pos) (cfg (.clear false 2) (halfClean K xs) pos) at th
  have jh:=jump_trace K (.clear false 2) (.clear true 0) (halfClean K xs) pos rfl
  obtain ⟨i,hi,ti⟩:=clear_call K true (halfClean K xs) pos rfl
  have hend : Function.update (halfClean K xs) .right ⟨[],[]⟩=final K xs:=by
    funext p;cases p <;> rfl
  rw [show (if true then Port.right else Port.left)=Port.right from rfl,hend] at ti
  have ji:=jump_trace K (.clear true 2) .done (final K xs) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb (trace_trans tc (trace_trans jc (trace_trans td (trace_trans jd (trace_trans te (trace_trans je (trace_trans tf (trace_trans jf (trace_trans tg (trace_trans jg (trace_trans th (trace_trans jh (trace_trans ti (ji)))))))))))))))))⟩
  unfold budget
  nlinarith

theorem native_radius (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K xs,
      Transpose.stepN (nativeMachine K) input t
        ((cfg (start K) (initial xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=
        some ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace K xs hx pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding K) (program K) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding K) (program K) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_radius_linear (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs)
    (hl : xs.length ≤ Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ linearConstant K*(Counter.value xs*Transpose.entryBits (Counter.value xs)),
      Transpose.stepN (nativeMachine K) input t
        ((cfg (start K) (initial xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=
        some ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=none := by
  obtain ⟨t,ht,hstep,hhalt⟩:=native_radius K xs hx pos input inputPos outRev
  exact ⟨t,ht.trans (budget_linear K xs hx hl),hstep,hhalt⟩

theorem fixed_resources (K : ℕ) : (nativeMachine K).k=11 ∧ (nativeMachine K).g+1=5 ∧
    (nativeEncoding K).label (start K)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Port=11
  decide +kernel

theorem output_contract (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    (result K xs).length=width K xs ∧
    Counter.value (result K xs)=K*Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs) ∧
    final K xs .source=Counter.marked xs ∧ final K xs .result=Counter.marked (result K xs) ∧
    ∀ p,p≠.source → p≠.result → final K xs p=⟨[],[]⟩ := by
  refine ⟨result_length K xs,result_value K xs hx,rfl,rfl,?_⟩
  intro p hs hr
  cases p <;> simp_all [final]

theorem native_call {U J : Type*} {k q : ℕ} (K : ℕ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label K → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program K pc≠.halt → program K pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program K pc))
    (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start K) (initial xs) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final K xs) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace K xs hx pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program K) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RadiusBuilder


/-! Radius and clock contracts for one paid setup from a marked dimension.
The radius is erased after its clock has been built. -/
namespace TransposeFollowup.RadiusClock
open FixedTapeCompiler
set_option autoImplicit false

def radius (K : ℕ) (xs : List Bool) : ℕ :=
  K*Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs)
def word (K : ℕ) (xs : List Bool) : List Bool := SevenPhaseClock.word (radius K xs)
def budget (K : ℕ) (xs : List Bool) : ℕ :=
  RadiusBuilder.budget K xs+51*radius K xs+46*RadiusBuilder.width K xs+102
def linearConstant (K : ℕ) : ℕ :=
  876+143*RadiusBuilder.padding K+K*(139+18*RadiusBuilder.padding K)

theorem radius_le (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) :
    radius K xs ≤ K*(Counter.value xs*Transpose.entryBits (Counter.value xs)) := by
  have hb : 1 ≤ Transpose.entryBits (Counter.value xs) := by
    rw [EntryBits.entryBits_eq];omega
  have hp : 1 ≤ Counter.value xs*Transpose.entryBits (Counter.value xs) := by nlinarith
  have h : Transpose.Tape.TSDiagram.blockSize 3 (Counter.value xs) ≤
      Counter.value xs*Transpose.entryBits (Counter.value xs) := by
    unfold Transpose.Tape.TSDiagram.blockSize
    omega
  exact Nat.mul_le_mul_left K h

theorem budget_linear (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs)
    (hl : xs.length ≤ Counter.value xs) :
    budget K xs ≤ linearConstant K*(Counter.value xs*Transpose.entryBits (Counter.value xs)) := by
  let P:=Counter.value xs*Transpose.entryBits (Counter.value xs)
  have hb : 1 ≤ Transpose.entryBits (Counter.value xs) := by rw [EntryBits.entryBits_eq];omega
  have hnP : Counter.value xs ≤ P := by dsimp [P];nlinarith
  have hP : 1 ≤ P := by omega
  have hlP : xs.length ≤ P := hl.trans hnP
  have hm : RadiusBuilder.width K xs ≤ (2+RadiusBuilder.padding K)*P := by
    unfold RadiusBuilder.width
    have h:=Nat.mul_le_mul_left (RadiusBuilder.padding K) hP
    nlinarith
  have h0:=RadiusBuilder.budget_linear K xs hx hl
  have h1:=Nat.mul_le_mul_left 51 (radius_le K xs hx)
  have h2:=Nat.mul_le_mul_left 46 hm
  have h3:=Nat.mul_le_mul_left 102 hP
  unfold budget linearConstant RadiusBuilder.linearConstant at *
  dsimp [P] at *
  nlinarith

theorem word_length (K : ℕ) (xs : List Bool) : (word K xs).length=7*radius K xs :=
  SevenPhaseClock.word_length _

end TransposeFollowup.RadiusClock


/-! One fixed caller for radius calculation, physical clock generation,
and radius erasure. Only the original dimension and clock remain. -/
namespace TransposeFollowup.RadiusClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
abbrev Port:=RadiusBuilder.Port ⊕ Unit
abbrev Bank:=Port → Tape Bool

def radiusBinding : FinitePortBinding RadiusBuilder.Port Port where
  ports:=Function.Embedding.inl
  decode | .inl p => some p | .inr _ => none
  decode_spec:=by intro p t;cases p <;> simp [eq_comm]

def clockBinding : FinitePortBinding (Fin 3) Port where
  ports:=⟨![.inl .result,.inl .counter,.inr ()],by decide +kernel⟩
  decode | .inl .result => some 0 | .inl .counter => some 1 | .inr _ => some 2 | _ => none
  decode_spec:=by
    intro p t
    cases p with
    | inl p => cases p <;> fin_cases t <;> decide +kernel
    | inr p => cases p;fin_cases t <;> decide +kernel

def eraseBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => .inl .result,fun _ _ _ => Subsingleton.elim _ _⟩
  decode | .inl .result => some 0 | _ => none
  decode_spec:=by
    intro p t
    fin_cases t
    cases p with
    | inl p => cases p <;> decide +kernel
    | inr p => cases p;decide +kernel

inductive Label (K : ℕ)
  | radius (pc : RadiusBuilder.Label K)
  | clock (pc : ClockBuilder.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start (K : ℕ) : Label K:=.radius (RadiusBuilder.start K)
def program (K : ℕ) : Microcode.Program Port (Label K)
  | .radius .done => .jump (.clock ClockBuilder.start)
  | .radius pc => radiusBinding.instruction Label.radius (RadiusBuilder.program K pc)
  | .clock (.seal .done) => .jump (.erase 2)
  | .clock pc => clockBinding.instruction Label.clock (ClockBuilder.program pc)
  | .erase pc => if pc=0 then .jump .done else eraseBinding.instruction Label.erase (NativeErase.program pc)
  | .done => .halt

theorem radius_code (K : ℕ) (pc : RadiusBuilder.Label K)
    (hh : RadiusBuilder.program K pc≠.halt) (_ : RadiusBuilder.program K pc≠.reject) :
    program K (.radius pc)=MicrocodeEmbedding.instruction radiusBinding.ports Label.radius (RadiusBuilder.program K pc) := by
  cases pc <;> first | exact False.elim (hh rfl) | exact radiusBinding.instruction_eq _ _

theorem clock_code (K : ℕ) (pc : ClockBuilder.Label)
    (hh : ClockBuilder.program pc≠.halt) (_ : ClockBuilder.program pc≠.reject) :
    program K (.clock pc)=MicrocodeEmbedding.instruction clockBinding.ports Label.clock (ClockBuilder.program pc) := by
  have hp : pc≠.seal .done:=by intro h;subst pc;exact hh rfl
  cases pc with
  | «seal» pc => cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]
  | _ => exact clockBinding.instruction_eq _ _

theorem erase_code (K : ℕ) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program K (.erase pc)=MicrocodeEmbedding.instruction eraseBinding.ports Label.erase (NativeErase.program pc) := by
  have hp : pc≠0:=by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def initial (xs : List Bool) : Bank:=Sum.elim (RadiusBuilder.initial xs) (fun _ => ⟨[],[]⟩)
def radial (K : ℕ) (xs : List Bool) : Bank:=Sum.elim (RadiusBuilder.final K xs) (fun _ => ⟨[],[]⟩)
def clocked (K : ℕ) (xs : List Bool) : Bank:=
  Sum.elim (RadiusBuilder.final K xs) (fun _ => Counter.marked (word K xs))
def final (K : ℕ) (xs : List Bool) : Bank:=
  Sum.elim (RadiusBuilder.initial xs) (fun _ => Counter.marked (word K xs))

def cfg {K : ℕ} (pc : Label K) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label K):=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port:=⟨fun p => (s p).denote,pos⟩
abbrev Trace (K : ℕ):=OperationalTrace.Trace (NativeMicrocode.step (program K)) (NativeMicrocode.Active (program K))
noncomputable def nativeEncoding (K : ℕ):=NativeMicrocode.initialEncoding (T:=Port) (start K)
noncomputable def nativeMachine (K : ℕ):=NativeMicrocode.machine (nativeEncoding K) (program K)

end TransposeFollowup.RadiusClock


/-! Reuse of the already proved native routines with exact tape frames. -/
namespace TransposeFollowup.RadiusClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_radius (K : ℕ) (pc : RadiusBuilder.Label K) (s : RadiusBuilder.Bank)
    (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed radiusBinding.ports Label.radius
      (RadiusBuilder.cfg pc s (fun p => pos (radiusBinding.ports p))) (frame base pos)=
      cfg (.radius pc) (radiusBinding.values s base) pos := by
  exact radiusBinding.embed_bank_project _ _ _ _ _

theorem embed_clock (K : ℕ) (pc : ClockBuilder.Label) (source fuel output : Tape Bool)
    (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed clockBinding.ports (Label.clock (K:=K))
      (ClockBuilder.cfg pc source fuel output (fun p => pos (clockBinding.ports p))) (frame base pos)=
      cfg (.clock pc) (clockBinding.values (ClockBuilder.bank source fuel output) base) pos := by
  exact clockBinding.embed_bank_project _ _ _ _ _

theorem embed_erase (K : ℕ) (pc : NativeErase.Label) (w : Tape Bool)
    (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed eraseBinding.ports (Label.erase (K:=K))
      (NativeErase.cfg pc w (fun p => pos (eraseBinding.ports p))).denote (frame base pos)=
      cfg (.erase pc) (Function.update base (.inl .result) w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame cfg
  simp only [← eraseBinding.values_eq_extend]
  congr 2
  all_goals
    funext p
    cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p;rfl

theorem jump_trace (K : ℕ) (pc next : Label K) (s : Bank) (pos : Port → ℤ)
    (h : program K pc=.jump next) : Trace K 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem radius_call (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ RadiusBuilder.budget K xs,Trace K t (cfg (start K) (initial xs) pos)
      (cfg (.radius .done) (radial K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=RadiusBuilder.complete_trace K xs hx (fun p => pos (radiusBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed radiusBinding.ports Label.radius (RadiusBuilder.program K)
    (program K) (frame (initial xs) pos) (radius_code K) htr
  have hi : radiusBinding.values (RadiusBuilder.initial xs) (initial xs)=initial xs := by
    funext p;cases p <;> rfl
  have hf : radiusBinding.values (RadiusBuilder.final K xs) (initial xs)=radial K xs := by
    funext p;cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_radius,hi,hf,start] using he⟩

theorem clock_call (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ 51*radius K xs+42*RadiusBuilder.width K xs+95,Trace K t
      (cfg (.clock ClockBuilder.start) (radial K xs) pos)
      (cfg (.clock (.seal .done)) (clocked K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=ClockBuilder.clock_trace (RadiusBuilder.result K xs) (fun p => pos (clockBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed clockBinding.ports (Label.clock (K:=K)) ClockBuilder.program
    (program K) (frame (radial K xs) pos) (clock_code K) htr
  have hi : clockBinding.values (ClockBuilder.bank (Counter.marked (RadiusBuilder.result K xs)) ⟨[],[]⟩ ⟨[],[]⟩)
      (radial K xs)=radial K xs := by
    funext p
    cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p;rfl
  have hf : clockBinding.values (ClockBuilder.bank (Counter.marked (RadiusBuilder.result K xs)) ⟨[],[]⟩
      (Counter.marked (word K xs))) (radial K xs)=clocked K xs := by
    funext p
    cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p;rfl
  have hv : Counter.value (RadiusBuilder.result K xs)=radius K xs:=RadiusBuilder.result_value K xs hx
  exact ⟨t,by simpa only [hv,RadiusBuilder.result_length] using ht,
    by simpa only [embed_clock,hv,← word.eq_def,hi,hf] using he⟩

theorem erase_call (K : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*RadiusBuilder.width K xs+4,Trace K t
      (cfg (.erase 2) (clocked K xs) pos) (cfg (.erase 0) (final K xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace (RadiusBuilder.result K xs) (fun p => pos (eraseBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed eraseBinding.ports (Label.erase (K:=K)) NativeErase.program
    (program K) (frame (clocked K xs) pos) (erase_code K) htr
  have hi : Function.update (clocked K xs) (.inl .result) (Counter.marked (RadiusBuilder.result K xs))=clocked K xs :=
    Function.update_eq_self _ _
  have hf : Function.update (clocked K xs) (.inl .result) ⟨[],[]⟩=final K xs := by
    funext p
    cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p;rfl
  exact ⟨t,by simpa only [RadiusBuilder.result_length] using ht,
    by simpa only [embed_erase,hi,hf] using he⟩

end TransposeFollowup.RadiusClock


/-! Complete clock setup from the retained positive dimension. All other
work tapes start blank; only the dimension and physical clock survive. -/
namespace TransposeFollowup.RadiusClock
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem complete_trace (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ budget K xs,Trace K t (cfg (start K) (initial xs) pos) (cfg .done (final K xs) pos) := by
  obtain ⟨a,ha,ta⟩:=radius_call K xs hx pos
  have ja:=jump_trace K (.radius .done) (.clock ClockBuilder.start) (radial K xs) pos rfl
  obtain ⟨b,hb,tb⟩:=clock_call K xs hx pos
  have jb:=jump_trace K (.clock (.seal .done)) (.erase 2) (clocked K xs) pos rfl
  obtain ⟨c,hc,tc⟩:=erase_call K xs pos
  have jc:=jump_trace K (.erase 0) .done (final K xs) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb (trace_trans tc jc))))⟩
  unfold budget
  omega

theorem native_clock (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K xs,
      Transpose.stepN (nativeMachine K) input t
        ((cfg (start K) (initial xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=
        some ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace K xs hx pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding K) (program K) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding K) (program K) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_clock_linear (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs)
    (hl : xs.length ≤ Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ linearConstant K*(Counter.value xs*Transpose.entryBits (Counter.value xs)),
      Transpose.stepN (nativeMachine K) input t
        ((cfg (start K) (initial xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=
        some ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev) ∧
      Transpose.step (nativeMachine K) input
        ((cfg .done (final K xs) pos).denote (nativeEncoding K) (program K) inputPos outRev)=none := by
  obtain ⟨t,ht,hstep,hhalt⟩:=native_clock K xs hx pos input inputPos outRev
  exact ⟨t,ht.trans (budget_linear K xs hx hl),hstep,hhalt⟩

theorem fixed_resources (K : ℕ) : (nativeMachine K).k=12 ∧ (nativeMachine K).g+1=5 ∧
    (nativeEncoding K).label (start K)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Port=12
  decide +kernel

theorem output_contract (K : ℕ) (xs : List Bool) :
    final K xs (.inl .source)=Counter.marked xs ∧
    final K xs (.inr ())=Counter.marked (word K xs) ∧
    (word K xs).length=7*radius K xs ∧
    ∀ p,p≠.inl .source → p≠.inr () → final K xs p=⟨[],[]⟩ := by
  refine ⟨rfl,rfl,word_length K xs,?_⟩
  intro p hs hc
  cases p with
  | inl p => cases p <;> simp_all [final,RadiusBuilder.initial]
  | inr p => cases p;exact False.elim (hc rfl)

theorem native_call {U J : Type*} {k q : ℕ} (K : ℕ)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label K → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program K pc≠.halt → program K pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program K pc))
    (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget K xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start K) (initial xs) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final K xs) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace K xs hx pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program K) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RadiusClock
