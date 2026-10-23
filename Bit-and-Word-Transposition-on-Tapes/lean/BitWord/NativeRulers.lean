import BitWord.NativeUnary
import BitWord.NativePowerTwoRun
import BitWord.NativeBindingCalls
import TransposeFollowup.NativeExpanderShearTagBank

/-! Build all physical width and row-count rulers from three binary words.
The only multiplication of lengths is a paid repetition of a unary clock. -/
namespace BitWord.NativeRulers
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames NativeCountedLoop

inductive Port
  | dimension | hword | wword | d | h | D | B | dB | DB | fuelA | fuelB | powD | powB
  deriving DecidableEq
instance : Fintype Port where
  elems := {.dimension,.hword,.wword,.d,.h,.D,.B,.dB,.DB,.fuelA,.fuelB,.powD,.powB}
  complete := by intro p; cases p <;> simp
abbrev Bank := Port → Tape Bool

def unarySource (second : Bool) : Port := if second then .hword else .dimension
def unaryTarget (second : Bool) : Port := if second then .h else .d
def powerSource (second : Bool) : Port := if second then .wword else .hword
def powerTarget (second : Bool) : Port := if second then .powB else .powD
def rulerTarget (second : Bool) : Port := if second then .B else .D

def unaryPorts (second : Bool) : Fin 3 → Port := ![unarySource second,.fuelA,unaryTarget second]
def unaryBinding (second : Bool) : FinitePortBinding (Fin 3) Port where
  ports := ⟨unaryPorts second,by cases second <;> decide +kernel⟩
  decode := fun p => if p=unarySource second then some 0 else if p=.fuelA then some 1
    else if p=unaryTarget second then some 2 else none
  decode_spec := by intro p i; cases second <;> cases p <;> fin_cases i <;> decide +kernel

def powerPorts (second : Bool) : NativePowerTwo.Port → Port
  | .source => powerSource second | .fuel => .fuelA | .power => .fuelB | .result => powerTarget second

def powerBinding (second : Bool) : FinitePortBinding NativePowerTwo.Port Port where
  ports := ⟨powerPorts second,by cases second <;> decide +kernel⟩
  decode := fun p => if p=powerSource second then some .source else if p=.fuelA then some .fuel
    else if p=.fuelB then some .power else if p=powerTarget second then some .result else none
  decode_spec := by intro p i; cases second <;> cases p <;> cases i <;> decide +kernel

def mapBinding (second : Bool) := pairBinding (powerTarget second) (rulerTarget second)
  (by cases second <;> decide)
def productSource (second : Bool) : Port := if second then .D else .d
def productTarget (second : Bool) : Port := if second then .DB else .dB

def productPorts (second : Bool) : Fin 3 → Port := ![productSource second,.B,productTarget second]
def productBinding (second : Bool) : FinitePortBinding (Fin 3) Port where
  ports := ⟨productPorts second,by cases second <;> decide +kernel⟩
  decode := fun p => if p=productSource second then some 0 else if p=.B then some 1
    else if p=productTarget second then some 2 else none
  decode_spec := by intro p i; cases second <;> cases p <;> fin_cases i <;> decide +kernel

inductive Label
  | unary (second : Bool) (pc : NativeUnary.Label)
  | power (second : Bool) (pc : NativePowerTwo.Label)
  | map (second : Bool) (pc : NativeMappedCopy.Label)
  | product (second : Bool) (pc : NativeExpanderShearTagPage.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .unary false NativeUnary.start
def program : Microcode.Program Port Label
  | .unary s .done => .jump (if s then .power false NativePowerTwo.start else .unary true NativeUnary.start)
  | .unary s pc => (unaryBinding s).instruction (Label.unary s) (NativeUnary.program pc)
  | .power s .done => .jump (.map s (.init (.erase 0)))
  | .power s pc => (powerBinding s).instruction (Label.power s) (NativePowerTwo.program pc)
  | .map s (.seal .done) => .jump (if s then .product false NativeExpanderShearTagPage.start else .power true NativePowerTwo.start)
  | .map s pc => (mapBinding s).instruction (Label.map s) (NativeMappedCopy.program (fun _ => false) pc)
  | .product s .done => .jump (if s then .done else .product true NativeExpanderShearTagPage.start)
  | .product s pc => (productBinding s).instruction (Label.product s) (NativeExpanderShearTagPage.program pc)
  | .done => .halt

abbrev cfg := workCfg (T:=Port) (L:=Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

def birth : Port → ℕ
  | .d => 1 | .h => 2 | .powD => 3 | .D => 4 | .powB => 5 | .B => 6 | .dB => 7 | .DB => 8 | _ => 0

def contents (xs hs ws : List Bool) : Bank
  | .dimension => Counter.marked xs | .hword => Counter.marked hs | .wword => Counter.marked ws
  | .d => Counter.marked (List.replicate (Counter.value xs) false)
  | .h => Counter.marked (List.replicate (Counter.value hs) false)
  | .D => Counter.marked (List.replicate (2^Counter.value hs) false)
  | .B => Counter.marked (List.replicate (2^Counter.value ws) false)
  | .dB => Counter.marked (List.replicate (Counter.value xs*2^Counter.value ws) false)
  | .DB => Counter.marked (List.replicate (2^Counter.value hs*2^Counter.value ws) false)
  | .powD => Counter.marked (NativePowerTwo.ruler hs)
  | .powB => Counter.marked (NativePowerTwo.ruler ws)
  | _ => ⟨[],[]⟩

def stage (xs hs ws : List Bool) (k : ℕ) : Bank :=
  fun p => if birth p≤k then contents xs hs ws p else ⟨[],[]⟩
def initial (xs hs ws : List Bool) := stage xs hs ws 0
def final (xs hs ws : List Bool) := stage xs hs ws 8

theorem unary_code (s : Bool) (pc : NativeUnary.Label) (hh : NativeUnary.program pc≠.halt)
    (_ : NativeUnary.program pc≠.reject) :
    program (.unary s pc)=MicrocodeEmbedding.instruction (unaryBinding s).ports (Label.unary s) (NativeUnary.program pc) := by
  cases pc <;> simp_all [program,NativeUnary.program,FinitePortBinding.instruction_eq]

theorem power_code (s : Bool) (pc : NativePowerTwo.Label) (hh : NativePowerTwo.program pc≠.halt)
    (_ : NativePowerTwo.program pc≠.reject) :
    program (.power s pc)=MicrocodeEmbedding.instruction (powerBinding s).ports (Label.power s) (NativePowerTwo.program pc) := by
  cases pc <;> simp_all [program,NativePowerTwo.program,FinitePortBinding.instruction_eq]

theorem map_code (s : Bool) (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program (fun _ => false) pc≠.halt)
    (_ : NativeMappedCopy.program (fun _ => false) pc≠.reject) :
    program (.map s pc)=MicrocodeEmbedding.instruction (mapBinding s).ports (Label.map s)
      (NativeMappedCopy.program (fun _ => false) pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem product_code (s : Bool) (pc : NativeExpanderShearTagPage.Label)
    (hh : NativeExpanderShearTagPage.program pc≠.halt) (_ : NativeExpanderShearTagPage.program pc≠.reject) :
    program (.product s pc)=MicrocodeEmbedding.instruction (productBinding s).ports (Label.product s)
      (NativeExpanderShearTagPage.program pc) := by
  cases pc <;> simp_all [program,NativeExpanderShearTagPage.program,FinitePortBinding.instruction_eq]

end BitWord.NativeRulers
