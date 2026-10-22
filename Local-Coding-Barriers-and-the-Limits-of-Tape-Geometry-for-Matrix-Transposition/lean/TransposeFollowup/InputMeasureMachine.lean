import TransposeFollowup.NativeIOEmbedding
import TransposeFollowup.RawInputCopy
import TransposeFollowup.MeasuredScan

/-! One actual original-input length controller. The three work tapes hold
payload,tally,and measured length. All five call transfers and tally cleanup
are paid. The result has the original payload's width; canonical trimming
is a subsequent physical operation. -/
namespace TransposeFollowup.InputMeasure
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
abbrev Port := Fin 3
abbrev Bank := Port → Tape Bool

def singleBinding (t : Port) : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => t,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun q => if q=t then some 0 else none
  decode_spec:=by
    intro q i
    change (if q=t then some (0:Fin 1) else none)=some i ↔ t=q
    fin_cases i
    simp [eq_comm]

def copyPorts (finish : Bool) : Fin 2 → Port := if finish then ![1,2] else ![0,1]
def copyBinding (finish : Bool) : FinitePortBinding (Fin 2) Port where
  ports:=⟨copyPorts finish,by cases finish <;> decide +kernel⟩
  decode:=fun t => if t=copyPorts finish 0 then some 0 else if t=copyPorts finish 1 then some 1 else none
  decode_spec:=by intro t q;cases finish <;> fin_cases t <;> fin_cases q <;> decide +kernel

def mapFor (finish : Bool) : Bool → Bool := if finish then Bool.not else fun _ => true

inductive Label
  | load (pc : RawInputCopy.Label)
  | copy (finish : Bool) (pc : NativeMappedCopy.Label)
  | scan (pc : MeasuredScan.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .load RawInputCopy.start

def program : NativeIO.Program Port Label
  | .load .done => .work (.jump (.copy false (.init (.erase 0))))
  | .load pc => NativeIOEmbedding.boundInstruction (singleBinding 0) Label.load (RawInputCopy.program pc)
  | .copy finish pc => if pc=.seal .done then
      .work (.jump (if finish then .erase 2 else .scan .read))
      else .work ((copyBinding finish).instruction (Label.copy finish) (NativeMappedCopy.program (mapFor finish) pc))
  | .scan .done => .work (.jump (.copy true (.init (.erase 0))))
  | .scan pc => .work ((copyBinding false).instruction Label.scan (MeasuredScan.program pc))
  | .erase pc => if pc=0 then .work (.jump .done)
      else .work ((singleBinding 1).instruction Label.erase (NativeErase.program pc))
  | .done => .work .halt

theorem load_code (pc : RawInputCopy.Label) (hh : RawInputCopy.program pc≠.work .halt) (_ : RawInputCopy.program pc≠.work .reject) :
    program (.load pc)=NativeIOEmbedding.instruction (singleBinding 0).ports Label.load (RawInputCopy.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem copy_code (finish : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program (mapFor finish) pc≠.halt) (_ : NativeMappedCopy.program (mapFor finish) pc≠.reject) :
    NativeIO.workProgram program (.copy finish pc)=MicrocodeEmbedding.instruction (copyBinding finish).ports
      (Label.copy finish) (NativeMappedCopy.program (mapFor finish) pc) := by
  have hp : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  simp only [NativeIO.workProgram,program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem scan_code (pc : MeasuredScan.Label) (hh : MeasuredScan.program pc≠.halt) (_ : MeasuredScan.program pc≠.reject) :
    NativeIO.workProgram program (.scan pc)=MicrocodeEmbedding.instruction (copyBinding false).ports Label.scan (MeasuredScan.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    NativeIO.workProgram program (.erase pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports Label.erase (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [NativeIO.workProgram,program,hp,ite_false,FinitePortBinding.instruction_eq]

def workCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (inputPos : ℤ) (outRev : List Bool) : NativeIO.Config Port Label :=
  ⟨workCfg pc s pos,inputPos,outRev⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩

def initial : Bank := fun _ => ⟨[],[]⟩
def bank (source tally result : Tape Bool) : Bank := ![source,tally,result]
def loaded (xs : List Bool) := bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩
def seeded (xs : List Bool) := bank (Counter.marked xs) (Counter.marked (List.replicate xs.length true)) ⟨[],[]⟩
def counted (xs : List Bool) := bank (Counter.marked xs) (Counter.marked (MeasuredWord.counted xs.length)) ⟨[],[]⟩
def copied (xs : List Bool) := bank (Counter.marked xs) (Counter.marked (MeasuredWord.counted xs.length))
  (Counter.marked (MeasuredWord.result xs.length))
def final (xs : List Bool) := bank (Counter.marked xs) ⟨[],[]⟩ (Counter.marked (MeasuredWord.result xs.length))

abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

end TransposeFollowup.InputMeasure
