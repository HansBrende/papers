import TransposeFollowup.RadiusClockRun
import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.PortBindingFrame

/-! A fixed four-tape power-of-two ruler controller. The exponent is a
little-endian marked binary word; no power or unary ruler is supplied. -/
namespace BitWord.NativePowerTwo
open TransposeFollowup FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | source | fuel | power | result
  deriving DecidableEq
instance : Fintype Port where
  elems := {.source,.fuel,.power,.result}
  complete := by intro p; cases p <;> simp
abbrev Bank := Port → Tape Bool

def single (p : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => p, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun t => if t=p then some 0 else none
  decode_spec := by intro t i; fin_cases i; change (if t=p then some (0 : Fin 1) else none)=some 0 ↔ p=t; simp [eq_comm]

def pair (a b : Port) (h : a ≠ b) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![a,b], by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all⟩
  decode := fun t => if t=a then some 0 else if t=b then some 1 else none
  decode_spec := by
    intro t i
    change (if t=a then some (0 : Fin 2) else if t=b then some 1 else none)=some i ↔ ![a,b] i=t
    fin_cases i <;> by_cases ha : t=a <;> by_cases hb : t=b <;> simp_all [eq_comm]

def copyBinding := pair .source .fuel (by decide)
def fuelPort (second : Bool) : Port := if second then .power else .fuel
def outputPort (second : Bool) : Port := if second then .result else .power
def fillBinding (second : Bool) := pair (fuelPort second) (outputPort second)
  (by cases second <;> decide)

inductive Label
  | copy (pc : NativeMappedCopy.Label)
  | init (second : Bool) (pc : NativeBuffer.Label)
  | fill (second : Bool) (pc : CountedFill.Label 1)
  | append
  | seal (second : Bool) (pc : NativeSealBack.Label)
  | erase (second : Bool) (pc : NativeErase.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .copy (.init (.erase 0))
def program : Microcode.Program Port Label
  | .copy (.seal .done) => .jump (.init false (.erase 0))
  | .copy pc => copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .init s .done => .jump (.fill s (.counter 0))
  | .init s pc => (single (outputPort s)).instruction (Label.init s) (NativeBuffer.program pc)
  | .fill s (.counter pc) => if pc=12 then .jump (if s then .seal true .seal else .append)
      else (fillBinding s).instruction (Label.fill s) (CountedFill.program 1 s (.counter pc))
  | .fill s pc => (fillBinding s).instruction (Label.fill s) (CountedFill.program 1 s pc)
  | .append => .act (Microcode.single .power ⟨some (.data true),.right⟩) (.seal false .seal)
  | .seal false .done => .jump (.init true (.erase 0))
  | .seal true .done => .jump (.erase false 2)
  | .seal s pc => (single (outputPort s)).instruction (Label.seal s) (NativeSealBack.program pc)
  | .erase s pc => if pc=0 then .jump (if s then .done else .erase true 2)
      else (single (fuelPort s)).instruction (Label.erase s) (NativeErase.program pc)
  | .done => .halt

def cfg (pc : Label) (bank : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (bank p).denote⟩,pos⟩
def frame (bank : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (bank p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

def powerWord (e : ℕ) := List.replicate e false ++ [true]
def ruler (xs : List Bool) := List.replicate (2^Counter.value xs) true

theorem powerWord_value (e : ℕ) : Counter.value (powerWord e)=2^e := by
  induction e with
  | zero => rfl
  | succ e ih => simpa [powerWord,List.replicate_succ,Counter.value,pow_succ,Nat.mul_comm] using ih

@[simp] theorem powerWord_length (e : ℕ) : (powerWord e).length=e+1 := by simp [powerWord]

def initial (xs : List Bool) : Bank := fun p => if p=.source then Counter.marked xs else ⟨[],[]⟩
def final (xs : List Bool) : Bank := Function.update (initial xs) .result (Counter.marked (ruler xs))

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc ≠ .halt)
    (_ : NativeMappedCopy.program id pc ≠ .reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy
      (NativeMappedCopy.program id pc) := by
  cases pc with
  | init pc => simp [program,FinitePortBinding.instruction_eq]
  | append pc => simp [program,FinitePortBinding.instruction_eq]
  | «seal» pc => cases pc <;> simp_all [program,NativeMappedCopy.program,NativeSealBack.program,
      FinitePortBinding.instruction_eq,NativeMappedCopy.targetBinding,MicrocodeEmbedding.instruction]

theorem init_code (s : Bool) (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc ≠ .halt)
    (_ : NativeBuffer.program pc ≠ .reject) :
    program (.init s pc)=MicrocodeEmbedding.instruction (single (outputPort s)).ports
      (Label.init s) (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem fill_code (s : Bool) (pc : CountedFill.Label 1) (hh : CountedFill.program 1 s pc ≠ .halt)
    (_ : CountedFill.program 1 s pc ≠ .reject) :
    program (.fill s pc)=MicrocodeEmbedding.instruction (fillBinding s).ports
      (Label.fill s) (CountedFill.program 1 s pc) := by
  have hp : pc ≠ .counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem seal_code (s : Bool) (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc ≠ .halt)
    (_ : NativeSealBack.program pc ≠ .reject) :
    program (.seal s pc)=MicrocodeEmbedding.instruction (single (outputPort s)).ports
      (Label.seal s) (NativeSealBack.program pc) := by
  cases s <;> cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code (s : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc ≠ .halt)
    (_ : NativeErase.program pc ≠ .reject) :
    program (.erase s pc)=MicrocodeEmbedding.instruction (single (fuelPort s)).ports
      (Label.erase s) (NativeErase.program pc) := by
  have hp : pc ≠ 0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

end BitWord.NativePowerTwo
