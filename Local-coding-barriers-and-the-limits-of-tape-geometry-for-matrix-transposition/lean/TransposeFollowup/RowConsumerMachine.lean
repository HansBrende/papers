import TransposeFollowup.InPlaceAdd
import TransposeFollowup.NativeClosedStream
import TransposeFollowup.NativeMappedCopy

/-! Eight physical tapes suffice for a reusable row consumer. Every read,
call transfer, append, index increment, rewind and cleanup is an actual
instruction. Record storage is distinct from the reusable row workspace. -/
namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | stream | index | rowIndex | unit | zero | fuel | scratch | output
  deriving DecidableEq

instance : Fintype Port where
  elems := {.stream,.index,.rowIndex,.unit,.zero,.fuel,.scratch,.output}
  complete := by intro p; cases p <;> simp

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => p, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun t => if t=p then some 0 else none
  decode_spec := by
    intro t j; fin_cases j
    change (if t=p then some (0 : Fin 1) else none)=some 0 ↔ p=t
    by_cases h : t=p
    · subst t; simp
    · simp [h,Ne.symm h]

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.zero,.index], by decide +kernel⟩
  decode := fun t => match t with | .zero => some 0 | .index => some 1 | _ => none
  decode_spec := by intro t j; cases t <;> fin_cases j <;> decide +kernel

def appendBinding (target : Bool) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![if target then .index else .rowIndex,.output], by cases target <;> decide +kernel⟩
  decode := fun t => if t=.output then some 1
    else if t=(if target then .index else .rowIndex) then some 0 else none
  decode_spec := by intro t j; cases target <;> cases t <;> fin_cases j <;> decide +kernel

def addPort : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .index | .factor => .unit | .scratch => .scratch | .zero => .zero

def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort, by intro a b h; cases a <;> cases b <;> simp_all [addPort]⟩
  decode := fun t => match t with
    | .fuel => some .fuel | .index => some .acc | .unit => some .factor
    | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec := by intro t j; cases t <;> cases j <;> decide +kernel

inductive Label
  | rewind (pc : NativeSealBack.Label)
  | copy (pc : NativeMappedCopy.Label)
  | scan
  | append (target : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | increment (pc : RepeatedAdd.Label)
  | advance
  | erase (counter : Bool) (pc : NativeErase.Label)
  | done | reject
  deriving DecidableEq, Fintype

def start : Label := .rewind .back

def program : Microcode.Program Port Label
  | .rewind pc => if pc=.done then .jump (.copy (.init (.erase 0)))
      else (singleBinding .stream).instruction Label.rewind (NativeSealBack.program pc)
  | .copy pc => if pc=.seal .done then .jump .scan
      else copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .scan => .read .stream (fun s => match s with
      | .data true => .append false 0
      | .data false => .increment (.counter 0)
      | .stop => .erase false 4 | _ => .reject)
  | .append target pc => if pc=7 then
      .jump (if target then .increment (.counter 0) else .append true 0)
      else (appendBinding target).instruction (Label.append target) (Microcode.MappedAppendFamily.program id pc)
  | .increment pc => if pc=.counter 12 then .jump .advance
      else addBinding.instruction Label.increment (RepeatedAdd.program pc)
  | .advance => .act (Microcode.single .stream ⟨none,.right⟩) .scan
  | .erase counter pc => if pc=0 then .jump (if counter then .done else .erase true 2)
      else (singleBinding (if counter then .index else .stream)).instruction (Label.erase counter) (NativeErase.program pc)
  | .done => .halt
  | .reject => .reject

theorem rewind_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt)
    (_ : NativeSealBack.program pc≠.reject) :
    program (.rewind pc)=MicrocodeEmbedding.instruction (singleBinding .stream).ports
      Label.rewind (NativeSealBack.program pc) := by
  have h : pc≠.done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports
      Label.copy (NativeMappedCopy.program id pc) := by
  have h : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem append_code (b : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt)
    (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program (.append b pc)=MicrocodeEmbedding.instruction (appendBinding b).ports
      (Label.append b) (Microcode.MappedAppendFamily.program id pc) := by
  have h : pc≠7 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem increment_code (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt)
    (_ : RepeatedAdd.program pc≠.reject) :
    program (.increment pc)=MicrocodeEmbedding.instruction addBinding.ports
      Label.increment (RepeatedAdd.program pc) := by
  have h : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem erase_code (b : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program (.erase b pc)=MicrocodeEmbedding.instruction (singleBinding (if b then .index else .stream)).ports
      (Label.erase b) (NativeErase.program pc) := by
  have h : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

structure Work where
  stream : Tape Bool
  index : Tape Bool
  pre : List (Sym Bool)

def bank (row unit : List Bool) (s : Work) : Port → Tape Bool
  | .stream => s.stream | .index => s.index | .rowIndex => Counter.marked row
  | .unit => Counter.marked unit | .zero => Counter.marked (List.replicate unit.length false)
  | .fuel => Counter.marked [true] | .scratch => BinaryCarry.preparedOutput
  | .output => ⟨s.pre,[]⟩

def cfg (pc : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (bank row unit s p).denote⟩,pos⟩

def zipperCfg (pc : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc,bank row unit s⟩,pos⟩

def frame (row unit : List Bool) (s : Work) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (bank row unit s p).denote,pos⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) start
noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=8 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=165 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=8
    decide +kernel
  · change Fintype.card Label-1+1=165
    decide +kernel

end TransposeFollowup.RowConsumer
