import BitWord.NativeOracleInPlace
import BitWord.NativeDoubleWord
import BitWord.NativePowerTwoRun
import BitWord.NativeBindingCalls

/-! A suffix caller receives only a marked binary parameter k. It constructs
its unary block ruler, executes the real oracle batch, and clears all new scratch. -/
namespace BitWord.NativeSuffixPowered
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls
set_option autoImplicit false
noncomputable section
abbrev DataPort (M : Transpose.TM) := NativeOracleInPlace.Port M
abbrev Port (M : Transpose.TM) := DataPort M ⊕ Fin 4
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool

def parameter (M : Transpose.TM) : Port M := .inr 0
def exponent (M : Transpose.TM) : Port M := .inr 1
def fuel (M : Transpose.TM) : Port M := .inr 2
def power (M : Transpose.TM) : Port M := .inr 3
def ruler (M : Transpose.TM) : Port M := .inl (NativeOracleBlock.clock M)
def doubleBinding (M : Transpose.TM) := pairBinding (parameter M) (exponent M) (by simp [parameter,exponent])
def dataBinding (M : Transpose.TM) : FinitePortBinding (DataPort M) (Port M) where
  ports := ⟨Sum.inl,Sum.inl_injective⟩
  decode := fun p => match p with | .inl i => some i | .inr _ => none
  decode_spec := by intro p i; cases p <;> simp [eq_comm]
def powerPorts (M : Transpose.TM) : NativePowerTwo.Port → Port M
  | .source => exponent M | .fuel => fuel M | .power => power M | .result => ruler M

def powerBinding (M : Transpose.TM) : FinitePortBinding NativePowerTwo.Port (Port M) where
  ports := ⟨powerPorts M,by intro p q h; cases p <;> cases q <;>
    simp_all [powerPorts,exponent,fuel,power,ruler]⟩
  decode := fun p => if p=exponent M then some .source else if p=fuel M then some .fuel else
    if p=power M then some .power else if p=ruler M then some .result else none
  decode_spec := by
    intro p i
    change (if p=exponent M then some .source else if p=fuel M then some .fuel else
      if p=power M then some .power else if p=ruler M then some .result else none)=some i ↔
        powerPorts M i=p
    cases i <;>
      by_cases he : p=exponent M <;> by_cases hf : p=fuel M <;>
      by_cases hp : p=power M <;> by_cases hr : p=ruler M <;>
      simp_all [powerPorts,exponent,fuel,power,ruler,eq_comm]

inductive Label (M : Transpose.TM)
  | double (pc : NativeDoubleWord.Label)
  | power (pc : NativePowerTwo.Label)
  | suffix (pc : NativeOracleInPlace.Label M)
  | eraseRuler (pc : NativeErase.Label)
  | eraseExponent (pc : NativeErase.Label)
  | done
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _
def start (M : Transpose.TM) : Label M := .double NativeDoubleWord.start

def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .double .done => .jump (.power NativePowerTwo.start)
  | .double pc => (doubleBinding M).instruction Label.double (NativeDoubleWord.program pc)
  | .power .done => .jump (.suffix (NativeOracleInPlace.start M))
  | .power pc => (powerBinding M).instruction Label.power (NativePowerTwo.program pc)
  | .suffix .done => .jump (.eraseRuler 2)
  | .suffix pc => (dataBinding M).instruction Label.suffix (NativeOracleInPlace.program M pc)
  | .eraseRuler pc => if pc=0 then .jump (.eraseExponent 2) else
      (singleBinding (ruler M)).instruction Label.eraseRuler (NativeErase.program pc)
  | .eraseExponent pc => if pc=0 then .jump .done else
      (singleBinding (exponent M)).instruction Label.eraseExponent (NativeErase.program pc)
  | .done => .halt
abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T:=Port M) (L:=Label M)

theorem double_code (M : Transpose.TM) (pc : NativeDoubleWord.Label)
    (hh : NativeDoubleWord.program pc≠.halt) (_ : NativeDoubleWord.program pc≠.reject) :
    program M (.double pc)=MicrocodeEmbedding.instruction (doubleBinding M).ports
      Label.double (NativeDoubleWord.program pc) := by
  cases pc <;> simp_all [program,NativeDoubleWord.program,FinitePortBinding.instruction_eq]
theorem power_code (M : Transpose.TM) (pc : NativePowerTwo.Label)
    (hh : NativePowerTwo.program pc≠.halt) (_ : NativePowerTwo.program pc≠.reject) :
    program M (.power pc)=MicrocodeEmbedding.instruction (powerBinding M).ports
      Label.power (NativePowerTwo.program pc) := by
  cases pc <;> simp_all [program,NativePowerTwo.program,FinitePortBinding.instruction_eq]
theorem suffix_code (M : Transpose.TM) (pc : NativeOracleInPlace.Label M)
    (hh : NativeOracleInPlace.program M pc≠.halt) (_ : NativeOracleInPlace.program M pc≠.reject) :
    program M (.suffix pc)=MicrocodeEmbedding.instruction (dataBinding M).ports
      Label.suffix (NativeOracleInPlace.program M pc) := by
  cases pc <;> simp_all [program,NativeOracleInPlace.program,FinitePortBinding.instruction_eq]
theorem eraseRuler_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseRuler pc)=MicrocodeEmbedding.instruction (singleBinding (ruler M)).ports
      Label.eraseRuler (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]
theorem eraseExponent_code (M : Transpose.TM) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program M (.eraseExponent pc)=MicrocodeEmbedding.instruction (singleBinding (exponent M)).ports
      Label.eraseExponent (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def layout {A : Type*} (M : Transpose.TM) (inner : DataPort M → A) (outer : Fin 4 → A) : Port M → A :=
  Sum.elim inner outer
@[simp] theorem layout_update_inl {A : Type*} (M : Transpose.TM)
    (inner : DataPort M → A) (outer : Fin 4 → A) (p : DataPort M) (v : A) :
    Function.update (layout M inner outer) (.inl p) v=layout M (Function.update inner p v) outer := by
  funext t; cases t <;> simp [layout]
@[simp] theorem layout_update_inr {A : Type*} (M : Transpose.TM)
    (inner : DataPort M → A) (outer : Fin 4 → A) (p : Fin 4) (v : A) :
    Function.update (layout M inner outer) (.inr p) v=layout M inner (Function.update outer p v) := by
  funext t; cases t <;> simp [layout]
@[simp] theorem update_four_one {A : Type*} (a b c d v : A) :
    Function.update ![a,b,c,d] (1:Fin 4) v=![a,v,c,d] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_four_two {A : Type*} (a b c d v : A) :
    Function.update ![a,b,c,d] (2:Fin 4) v=![a,b,v,d] := by funext i; fin_cases i <;> rfl
@[simp] theorem update_four_three {A : Type*} (a b c d v : A) :
    Function.update ![a,b,c,d] (3:Fin 4) v=![a,b,c,v] := by funext i; fin_cases i <;> rfl
@[simp] theorem data_values {A : Type*} (M : Transpose.TM) (a inner : DataPort M → A) (outer : Fin 4 → A) :
    (dataBinding M).values a (layout M inner outer)=layout M a outer := by funext p; cases p <;> rfl

def innerBank (M : Transpose.TM) (main clock : Tape Bool) : DataPort M → Tape Bool :=
  NativeOracleBlock.layout M ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩ ![main,⟨[],[]⟩,clock]
def bank (M : Transpose.TM) (main clock param exp : Tape Bool) : Bank M :=
  layout M (innerBank M main clock) ![param,exp,⟨[],[]⟩,⟨[],[]⟩]
def positions (M : Transpose.TM) (sp tp kp pp : ℤ) : Port M → ℤ :=
  layout M (NativeOracleBlock.blockPos M sp tp kp) ![pp,0,0,0]

@[simp] theorem inner_update_clock (M : Transpose.TM) (main clk c : Tape Bool) :
    Function.update (innerBank M main clk) (NativeOracleBlock.clock M) c=innerBank M main c := by
  funext p
  cases p with
  | inl p => cases p with
    | data p => cases p <;> simp [innerBank,NativeOracleBlock.layout,NativeOracleBlock.clock]
    | log r => simp [innerBank,NativeOracleBlock.layout,NativeOracleBlock.clock]
  | inr p => fin_cases p <;> simp [innerBank,NativeOracleBlock.layout,NativeOracleBlock.clock]

@[simp] theorem power_values {A : Type*} (M : Transpose.TM) (a : NativePowerTwo.Port → A) (s : Port M → A) :
    (powerBinding M).values a s = Function.update (Function.update (Function.update (Function.update s
      (exponent M) (a .source)) (fuel M) (a .fuel)) (power M) (a .power)) (ruler M) (a .result) := by
  funext p
  by_cases he : p=exponent M <;> by_cases hf : p=fuel M <;>
    by_cases hp : p=power M <;> by_cases hr : p=ruler M <;>
    simp_all [powerBinding,FinitePortBinding.values,exponent,fuel,power,ruler]

end
end BitWord.NativeSuffixPowered
