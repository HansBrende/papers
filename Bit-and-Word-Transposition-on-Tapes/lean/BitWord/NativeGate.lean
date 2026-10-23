import BitWord.NativeSuffixPoweredRun
import BitWord.NativeSplitRun
import BitWord.NativeUnsplitRun
import BitWord.NativeOpcode
import BitWord.AddressParity

/-! A fixed two-bit dispatcher chooses an actual suffix, stable split,
inverse stable split, or idle action. Its control does not contain a dimension. -/
namespace BitWord.NativeGate
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls
set_option autoImplicit false
noncomputable section
abbrev Port (M : Transpose.TM) := NativeSuffixPowered.Port M ⊕ Fin 4
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool
def main (M : Transpose.TM) : Port M := .inl (.inl (NativeOracleBlock.source M))
def opcode (M : Transpose.TM) : Port M := .inr 0
def firstHalf (M : Transpose.TM) : Port M := .inr 1
def secondHalf (M : Transpose.TM) : Port M := .inr 2
def halfRuler (M : Transpose.TM) : Port M := .inr 3
def suffixBinding (M : Transpose.TM) : FinitePortBinding (NativeSuffixPowered.Port M) (Port M) where
  ports := ⟨Sum.inl,Sum.inl_injective⟩
  decode := fun p => match p with | .inl i => some i | .inr _ => none
  decode_spec := by intro p i; cases p <;> simp [eq_comm]
def splitPorts (M : Transpose.TM) : Fin 3 → Port M := ![main M,firstHalf M,secondHalf M]
def splitBinding (M : Transpose.TM) : FinitePortBinding (Fin 3) (Port M) where
  ports := ⟨splitPorts M,by intro i j h; fin_cases i <;> fin_cases j <;>
    simp_all [splitPorts,main,firstHalf,secondHalf]⟩
  decode := fun p => if p=main M then some 0 else if p=firstHalf M then some 1 else
    if p=secondHalf M then some 2 else none
  decode_spec := by
    intro p i
    change (if p=main M then some 0 else if p=firstHalf M then some 1 else
      if p=secondHalf M then some 2 else none)=some i ↔ splitPorts M i=p
    fin_cases i <;> by_cases hm : p=main M <;> by_cases ha : p=firstHalf M <;>
      by_cases hb : p=secondHalf M <;> simp_all [splitPorts,main,firstHalf,secondHalf,eq_comm]
def leftPorts (M : Transpose.TM) : Fin 4 → Port M := ![main M,firstHalf M,secondHalf M,halfRuler M]
def leftBinding (M : Transpose.TM) : FinitePortBinding (Fin 4) (Port M) where
  ports := ⟨leftPorts M,by intro i j h; fin_cases i <;> fin_cases j <;>
    simp_all [leftPorts,main,firstHalf,secondHalf,halfRuler]⟩
  decode := fun p => if p=main M then some 0 else if p=firstHalf M then some 1 else
    if p=secondHalf M then some 2 else if p=halfRuler M then some 3 else none
  decode_spec := by
    intro p i
    change (if p=main M then some 0 else if p=firstHalf M then some 1 else
      if p=secondHalf M then some 2 else if p=halfRuler M then some 3 else none)=some i ↔ leftPorts M i=p
    fin_cases i <;> by_cases hm : p=main M <;> by_cases ha : p=firstHalf M <;>
      by_cases hb : p=secondHalf M <;> by_cases hr : p=halfRuler M <;>
      simp_all [leftPorts,main,firstHalf,secondHalf,halfRuler,eq_comm]
inductive Label (M : Transpose.TM)
  | read (pc : NativeOpcode.Label)
  | suffix (pc : NativeSuffixPowered.Label M)
  | split (pc : NativeSplit.Label)
  | merge (pc : NativeUnsplit.Label)
  | done
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _
def start (M : Transpose.TM) : Label M := .read NativeOpcode.start
def selected (M : Transpose.TM) : Bool → Bool → Label M
  | false,false => .done | true,false => .split NativeSplit.start
  | false,true => .merge NativeUnsplit.start | true,true => .suffix (NativeSuffixPowered.start M)
def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .read (.done a b) => .jump (selected M a b)
  | .read pc => (singleBinding (opcode M)).instruction Label.read (NativeOpcode.program pc)
  | .suffix .done => .jump .done
  | .suffix pc => (suffixBinding M).instruction Label.suffix (NativeSuffixPowered.program M pc)
  | .split .done => .jump .done
  | .split pc => (splitBinding M).instruction Label.split (NativeSplit.program pc)
  | .merge .done => .jump .done
  | .merge pc => (leftBinding M).instruction Label.merge (NativeUnsplit.program pc)
  | .done => .halt
abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T:=Port M) (L:=Label M)

theorem read_code (M : Transpose.TM) (pc : NativeOpcode.Label)
    (hh : NativeOpcode.program pc≠.halt) (_ : NativeOpcode.program pc≠.reject) :
    program M (.read pc)=MicrocodeEmbedding.instruction (singleBinding (opcode M)).ports Label.read
      (NativeOpcode.program pc) := by
  cases pc <;> simp_all [program,NativeOpcode.program,FinitePortBinding.instruction_eq]
theorem suffix_code (M : Transpose.TM) (pc : NativeSuffixPowered.Label M)
    (hh : NativeSuffixPowered.program M pc≠.halt) (_ : NativeSuffixPowered.program M pc≠.reject) :
    program M (.suffix pc)=MicrocodeEmbedding.instruction (suffixBinding M).ports Label.suffix
      (NativeSuffixPowered.program M pc) := by
  cases pc <;> simp_all [program,NativeSuffixPowered.program,FinitePortBinding.instruction_eq]
theorem split_code (M : Transpose.TM) (pc : NativeSplit.Label)
    (hh : NativeSplit.program pc≠.halt) (_ : NativeSplit.program pc≠.reject) :
    program M (.split pc)=MicrocodeEmbedding.instruction (splitBinding M).ports Label.split
      (NativeSplit.program pc) := by
  cases pc <;> simp_all [program,NativeSplit.program,FinitePortBinding.instruction_eq]
theorem merge_code (M : Transpose.TM) (pc : NativeUnsplit.Label)
    (hh : NativeUnsplit.program pc≠.halt) (_ : NativeUnsplit.program pc≠.reject) :
    program M (.merge pc)=MicrocodeEmbedding.instruction (leftBinding M).ports Label.merge
      (NativeUnsplit.program pc) := by
  cases pc <;> simp_all [program,NativeUnsplit.program,FinitePortBinding.instruction_eq]

def bank (M : Transpose.TM) (raw param code fs : List Bool) : Bank M := Sum.elim
  (NativeSuffixPowered.bank M (Counter.marked raw) ⟨[],[]⟩ (Counter.marked param) ⟨[],[]⟩)
  ![Counter.marked code,⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs]
def positions (M : Transpose.TM) (sp tp kp pp : ℤ) (extra : Fin 4 → ℤ) : Port M → ℤ :=
  Sum.elim (NativeSuffixPowered.positions M sp tp kp pp) extra
@[simp] theorem suffix_values {A : Type*} (M : Transpose.TM)
    (v old : NativeSuffixPowered.Port M → A) (ext : Fin 4 → A) :
    (suffixBinding M).values v (Sum.elim old ext)=Sum.elim v ext := by
  funext i; cases i <;> rfl
@[simp] theorem bank_main (M : Transpose.TM) (raw param code fs : List Bool) :
    bank M raw param code fs (main M)=Counter.marked raw := rfl
@[simp] theorem bank_opcode (M : Transpose.TM) (raw param code fs : List Bool) :
    bank M raw param code fs (opcode M)=Counter.marked code := rfl
@[simp] theorem split_values (M : Transpose.TM) (raw out param code fs : List Bool) :
    (splitBinding M).values ![Counter.marked out,⟨[],[]⟩,⟨[],[]⟩] (bank M raw param code fs)=
      bank M out param code fs := by
  funext i
  by_cases hm : i=main M
  · subst i; simp [FinitePortBinding.values,splitBinding,splitPorts,main,firstHalf,secondHalf,bank,NativeSuffixPowered.bank,NativeSuffixPowered.layout,NativeSuffixPowered.innerBank,NativeOracleBlock.layout,NativeOracleBlock.source]
  by_cases ha : i=firstHalf M
  · subst i; simp [FinitePortBinding.values,splitBinding,splitPorts,main,firstHalf,secondHalf,bank]
  by_cases hb : i=secondHalf M
  · subst i; simp [FinitePortBinding.values,splitBinding,splitPorts,main,firstHalf,secondHalf,bank]
  simp only [FinitePortBinding.values,splitBinding,hm,ha,hb,ite_false]
  cases i with
  | inr i => rfl
  | inl i => cases i with
    | inr i => rfl
    | inl i => cases i with
      | inl i => cases i with
        | data i => cases i <;> rfl
        | log i => rfl
      | inr i => fin_cases i <;> simp_all [main,NativeOracleBlock.source,bank,NativeSuffixPowered.bank,
          NativeSuffixPowered.layout,NativeSuffixPowered.innerBank,NativeOracleBlock.layout]
@[simp] theorem left_values (M : Transpose.TM) (raw out param code fs : List Bool) :
    (leftBinding M).values ![Counter.marked out,⟨[],[]⟩,⟨[],[]⟩,Counter.marked fs]
      (bank M raw param code fs)=bank M out param code fs := by
  funext i
  by_cases hm : i=main M
  · subst i; simp [FinitePortBinding.values,leftBinding,leftPorts,main,firstHalf,secondHalf,halfRuler,bank,NativeSuffixPowered.bank,NativeSuffixPowered.layout,NativeSuffixPowered.innerBank,NativeOracleBlock.layout,NativeOracleBlock.source]
  by_cases ha : i=firstHalf M
  · subst i; simp [FinitePortBinding.values,leftBinding,leftPorts,main,firstHalf,secondHalf,halfRuler,bank]
  by_cases hb : i=secondHalf M
  · subst i; simp [FinitePortBinding.values,leftBinding,leftPorts,main,firstHalf,secondHalf,halfRuler,bank]
  by_cases hr : i=halfRuler M
  · subst i; simp [FinitePortBinding.values,leftBinding,leftPorts,main,firstHalf,secondHalf,halfRuler,bank]
  simp only [FinitePortBinding.values,leftBinding,hm,ha,hb,hr,ite_false]
  have hs := congrFun (split_values M raw out param code fs) i
  simpa only [FinitePortBinding.values,splitBinding,hm,ha,hb,ite_false] using hs
end
end BitWord.NativeGate
