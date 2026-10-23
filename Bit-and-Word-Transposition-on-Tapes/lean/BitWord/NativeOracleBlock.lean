import BitWord.NativeOracleResetFrame
import BitWord.NativeBoundedCopy
import TransposeFollowup.NativeErase
import TransposeFollowup.NativeMappedAppend

/-! Literal one-block caller: prepare isolated input/capture, load a clocked
block, run and reset the arbitrary oracle, append its output, erase both buffers. -/
namespace BitWord.NativeOracleBlock
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

abbrev Pool (M : Transpose.TM) := NativeOracleReset.Port M
abbrev Port (M : Transpose.TM) := Pool M ⊕ Fin 3

def source (M : Transpose.TM) : Port M := .inr 0
def target (M : Transpose.TM) : Port M := .inr 1
def clock (M : Transpose.TM) : Port M := .inr 2
def input (M : Transpose.TM) : Port M := .inl (NativeOracleReset.inputPort M)
def capture (M : Transpose.TM) : Port M := .inl (NativeOracleReset.capturePort M)

def poolBinding (M : Transpose.TM) : FinitePortBinding (Pool M) (Port M) where
  ports := ⟨Sum.inl,Sum.inl_injective⟩
  decode := fun p => match p with | .inl i => some i | .inr _ => none
  decode_spec := by intro p i; cases p <;> simp [eq_comm]

def loadBinding (M : Transpose.TM) : FinitePortBinding (Fin 3) (Port M) where
  ports := ⟨![source M,input M,clock M],by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all [source,input,clock]⟩
  decode := fun p => if p=source M then some 0 else if p=input M then some 1 else
    if p=clock M then some 2 else none
  decode_spec := by
    intro p i; fin_cases i <;>
      by_cases hs : p=source M <;> by_cases hi : p=input M <;> by_cases hc : p=clock M <;>
      simp_all [source,input,clock,eq_comm]

def oneBinding (M : Transpose.TM) (p : Port M) := NativeBankCalls.singleBinding p
def appendBinding (M : Transpose.TM) := NativeBankCalls.pairBinding (capture M) (target M)
  (by simp [capture,target])

inductive Label (M : Transpose.TM)
  | initInput (pc : NativeBuffer.Label)
  | initCapture (pc : NativeBuffer.Label)
  | load (pc : NativeBoundedCopy.Label)
  | oracle (pc : NativeOracleReset.Label M)
  | seal (pc : NativeSealBack.Label)
  | append (pc : Microcode.MappedAppendFamily.Label)
  | eraseCapture (pc : NativeErase.Label)
  | eraseInput (pc : NativeErase.Label)
  | done
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _

def start (M : Transpose.TM) : Label M := .initInput (.erase 0)

def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .initInput .done => .jump (.initCapture (.erase 0))
  | .initInput pc => (oneBinding M (input M)).instruction Label.initInput (NativeBuffer.program pc)
  | .initCapture .done => .jump (.load .scan)
  | .initCapture pc => (oneBinding M (capture M)).instruction Label.initCapture (NativeBuffer.program pc)
  | .load .done => .jump (.oracle none)
  | .load pc => (loadBinding M).instruction Label.load (NativeBoundedCopy.program pc)
  | .oracle pc => if pc=NativeOracleReset.terminal M then .jump (.seal .seal)
      else (poolBinding M).instruction Label.oracle (NativeOracleReset.program M pc)
  | .seal .done => .jump (.append 0)
  | .seal pc => (oneBinding M (capture M)).instruction Label.seal (NativeSealBack.program pc)
  | .append pc => if pc=7 then .jump (.eraseCapture 2)
      else (appendBinding M).instruction Label.append (Microcode.MappedAppendFamily.program id pc)
  | .eraseCapture pc => if pc=0 then .jump (.eraseInput 2)
      else (oneBinding M (capture M)).instruction Label.eraseCapture (NativeErase.program pc)
  | .eraseInput pc => if pc=0 then .jump .done
      else (oneBinding M (input M)).instruction Label.eraseInput (NativeErase.program pc)
  | .done => .halt

theorem initInput_code (M : Transpose.TM) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program M (.initInput pc)=MicrocodeEmbedding.instruction (oneBinding M (input M)).ports
      Label.initInput (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem initCapture_code (M : Transpose.TM) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program M (.initCapture pc)=MicrocodeEmbedding.instruction (oneBinding M (capture M)).ports
      Label.initCapture (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem load_code (M : Transpose.TM) (pc : NativeBoundedCopy.Label)
    (hh : NativeBoundedCopy.program pc≠.halt) (_ : NativeBoundedCopy.program pc≠.reject) :
    program M (.load pc)=MicrocodeEmbedding.instruction (loadBinding M).ports
      Label.load (NativeBoundedCopy.program pc) := by
  cases pc <;> simp_all [program,NativeBoundedCopy.program,FinitePortBinding.instruction_eq]
theorem oracle_code (M : Transpose.TM) (pc : NativeOracleReset.Label M)
    (hh : NativeOracleReset.program M pc≠.halt) (_ : NativeOracleReset.program M pc≠.reject) :
    program M (.oracle pc)=MicrocodeEmbedding.instruction (poolBinding M).ports
      Label.oracle (NativeOracleReset.program M pc) := by
  have hn : pc≠NativeOracleReset.terminal M := by
    intro h; subst pc
    simp [NativeOracleReset.program,NativeOracleReset.terminal,NativeLoggedInit.label,
      NativeLoggedInit.program,NativeLogged.program,MicrocodeEmbedding.instruction] at hh
  simp [program,hn,FinitePortBinding.instruction_eq]
theorem seal_code (M : Transpose.TM) (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    program M (.seal pc)=MicrocodeEmbedding.instruction (oneBinding M (capture M)).ports
      Label.seal (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]
theorem append_code (M : Transpose.TM) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt)
    (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program M (.append pc)=MicrocodeEmbedding.instruction (appendBinding M).ports
      Label.append (Microcode.MappedAppendFamily.program id pc) := by
  have hn : pc≠7 := by intro h; subst pc; exact hh rfl
  simp [program,hn,FinitePortBinding.instruction_eq]
theorem eraseCapture_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseCapture pc)=MicrocodeEmbedding.instruction (oneBinding M (capture M)).ports
      Label.eraseCapture (NativeErase.program pc) := by
  have hn : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hn,FinitePortBinding.instruction_eq]
theorem eraseInput_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseInput pc)=MicrocodeEmbedding.instruction (oneBinding M (input M)).ports
      Label.eraseInput (NativeErase.program pc) := by
  have hn : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hn,FinitePortBinding.instruction_eq]

abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T := Port M) (L := Label M)

end
end BitWord.NativeOracleBlock
