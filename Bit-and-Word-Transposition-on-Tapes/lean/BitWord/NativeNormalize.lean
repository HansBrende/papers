import BitWord.NativeSquareRun
import BitWord.NativeResize
import BitWord.NativeBindingCalls
import TransposeFollowup.NativeMappedCopy
import BitWord.SquareLayout

/-! Fixed native pre/post conversion between a raw matrix bank and its square,
entry-padded bank. Every ruler is an explicit retained tape. -/
namespace BitWord.NativeNormalize
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls
set_option autoImplicit false
abbrev Port := Fin 9
abbrev Bank := Port → Tape Bool

def resizePorts (expand : Bool) : Fin 4 → Port := if expand then ![0,1,3,4] else ![1,2,3,4]
def resizeBinding (expand : Bool) : FinitePortBinding (Fin 4) Port where
  ports := ⟨resizePorts expand,by cases expand <;> decide +kernel⟩
  decode := fun p => if p=resizePorts expand 0 then some 0 else if p=resizePorts expand 1 then some 1
    else if p=3 then some 2 else if p=4 then some 3 else none
  decode_spec := by intro p i; cases expand <;> fin_cases p <;> fin_cases i <;> decide +kernel

def squarePorts (expand : Bool) : Fin 6 → Port := if expand then ![1,2,7,8,5,6] else ![0,1,7,8,5,6]
def squareBinding (expand : Bool) : FinitePortBinding (Fin 6) Port where
  ports := ⟨squarePorts expand,by cases expand <;> decide +kernel⟩
  decode := fun p => if p=squarePorts expand 0 then some 0 else if p=squarePorts expand 1 then some 1
    else if p=7 then some 2 else if p=8 then some 3 else if p=5 then some 4 else if p=6 then some 5 else none
  decode_spec := by intro p i; cases expand <;> fin_cases p <;> fin_cases i <;> decide +kernel

def copyBinding := pairBinding (2:Port) 0 (by decide)

@[simp] theorem resizeBinding_ports (expand : Bool) (i : Fin 4) :
    (resizeBinding expand).ports i=resizePorts expand i := rfl
@[simp] theorem squareBinding_ports (expand : Bool) (i : Fin 6) :
    (squareBinding expand).ports i=squarePorts expand i := rfl
@[simp] theorem copyBinding_ports (i : Fin 2) : copyBinding.ports i=(![2,0] : Fin 2 → Port) i := rfl

inductive Label
  | resize (pc : NativeResize.Label)
  | square (pc : NativeSquare.Label)
  | erase (i : Fin 3) (pc : NativeErase.Label)
  | copy (pc : NativeMappedCopy.Label)
  | done
  deriving DecidableEq,Fintype

def start (expand : Bool) : Label := if expand then .resize NativeResize.start else .square NativeSquare.start

def program (expand : Bool) : Microcode.Program Port Label
  | .resize .done => .jump (if expand then .square NativeSquare.start else .erase 0 2)
  | .resize pc => (resizeBinding expand).instruction Label.resize (NativeResize.program expand pc)
  | .square .done => .jump (if expand then .erase 0 2 else .resize NativeResize.start)
  | .square pc => (squareBinding expand).instruction Label.square (NativeSquare.program expand pc)
  | .erase i pc => if pc=0 then .jump (if i=0 then .copy (.init (.erase 0)) else if i=1 then .erase 2 2 else .done)
      else (singleBinding ⟨i.val,by omega⟩).instruction (Label.erase i) (NativeErase.program pc)
  | .copy (.seal .done) => .jump (.erase 1 2)
  | .copy pc => copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .done => .halt

abbrev cfg := workCfg (T:=Port) (L:=Label)
abbrev Trace (expand : Bool) := OperationalTrace.Trace (NativeMicrocode.step (program expand)) (NativeMicrocode.Active (program expand))

def bank (src tmp₁ tmp₂ : Tape Bool) (d D h B : ℕ) : Bank :=
  ![src,tmp₁,tmp₂,NativeResizeScan.markedRuler h,NativeResizeScan.markedRuler B,
    NativeResizeScan.markedRuler d,NativeResizeScan.markedRuler D,
    NativeResizeScan.markedRuler (d*B),NativeResizeScan.markedRuler (D*B)]

theorem resize_code (expand : Bool) (pc : NativeResize.Label)
    (hh : NativeResize.program expand pc ≠ .halt) (_ : NativeResize.program expand pc ≠ .reject) :
    program expand (.resize pc)=MicrocodeEmbedding.instruction (resizeBinding expand).ports Label.resize
      (NativeResize.program expand pc) := by
  cases pc <;> simp_all [program,NativeResize.program,FinitePortBinding.instruction_eq]

theorem square_code (expand : Bool) (pc : NativeSquare.Label)
    (hh : NativeSquare.program expand pc ≠ .halt) (_ : NativeSquare.program expand pc ≠ .reject) :
    program expand (.square pc)=MicrocodeEmbedding.instruction (squareBinding expand).ports Label.square
      (NativeSquare.program expand pc) := by
  cases pc <;> simp_all [program,NativeSquare.program,FinitePortBinding.instruction_eq]

theorem erase_code (expand : Bool) (i : Fin 3) : NativeTapeCalls.Code (program expand)
    (⟨i.val,by omega⟩ : Port) (Label.erase i) NativeErase.program := by
  intro pc hh _
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem copy_code (expand : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc ≠ .halt) (hr : NativeMappedCopy.program id pc ≠ .reject) :
    program expand (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy
      (NativeMappedCopy.program id pc) := by
  cases pc <;> try { exact copyBinding.instruction_eq _ _ }
  rename_i pc; cases pc <;> simp_all [program,NativeMappedCopy.program,NativeSealBack.program,
    FinitePortBinding.instruction_eq,MicrocodeEmbedding.instruction]

theorem jump (expand : Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program expand pc=.jump next) : Trace expand 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end BitWord.NativeNormalize
