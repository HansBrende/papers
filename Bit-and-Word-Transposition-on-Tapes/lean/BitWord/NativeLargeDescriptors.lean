import BitWord.NativeCanonicalParameterRun
import BitWord.NativeSmallDescriptors

/-! Fixed thirteen-slot emission for the large canonical gate word. -/
namespace BitWord.NativeLargeDescriptors
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
set_option autoImplicit false

inductive Port
  | work (p : NativeCanonicalParameters.Port)
  | opcode (i : Fin 13)
  | parameter (i : Fin 13)
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def workBinding : FinitePortBinding NativeCanonicalParameters.Port Port where
  ports := ⟨Port.work,fun _ _ h => Port.work.inj h⟩
  decode := fun p => match p with | .work t => some t | _ => none
  decode_spec := by
    intro p q
    change (match p with | .work t => some t | _ => none)=some q ↔ Port.work q=p
    cases p <;> simp [eq_comm]

def literalBinding : FinitePortBinding (Fin 13) Port where
  ports := ⟨Port.opcode,fun _ _ h => Port.opcode.inj h⟩
  decode := fun p => match p with | .opcode i => some i | _ => none
  decode_spec := by
    intro p q
    change (match p with | .opcode i => some i | _ => none)=some q ↔ Port.opcode q=p
    cases p <;> simp [eq_comm]

def source : Fin 13 → NativeCanonicalParameters.Port :=
  ![.total,.diff,.double,.diff,.total,.h,.total,.diff,.double,.diff,.total,.u,.u]
def mapBit (i : Fin 13) : Bool → Bool := if i.val<11 then id else fun _ => false
def literal (_ : Unit) (i : Fin 13) : List Bool := if i.val<11 then [true,true] else [false,false]
def copyBinding (i : Fin 13) := pairBinding (Port.work (source i)) (Port.parameter i) (by intro h; cases h)

inductive Label
  | arithmetic (pc : NativeCanonicalParameters.Label)
  | literal (pc : NativeLiteralBank.Label Unit 2)
  | copy (i : Fin 13) (pc : NativeMappedCopy.Label)
  | done
  deriving DecidableEq, Fintype

def entry (k : ℕ) : Label := if hk : k<13 then .copy ⟨k,hk⟩ (.init (.erase 0)) else .done
def start : Label := .arithmetic NativeCanonicalParameters.start

def program : Microcode.Program Port Label
  | .arithmetic .done => .jump (.literal (.start ()))
  | .arithmetic pc => workBinding.instruction Label.arithmetic (NativeCanonicalParameters.program pc)
  | .literal (.done _) => .jump (entry 0)
  | .literal pc => literalBinding.instruction Label.literal (NativeLiteralBank.program 2 literal pc)
  | .copy i (.seal .done) => .jump (entry (i.val+1))
  | .copy i pc => (copyBinding i).instruction (Label.copy i) (NativeMappedCopy.program (mapBit i) pc)
  | .done => .halt

abbrev cfg := workCfg (T:=Port) (L:=Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

def initial (h : ℕ) : Bank
  | .work p => NativeCanonicalParameters.initial h p
  | _ => ⟨[],[]⟩
def sourceWord (h : ℕ) : NativeCanonicalParameters.Port → List Bool
  | .h => hword h | .u => uword h | .double => W h | .total => N h | .diff => R h | _ => []
def parameterWord (h : ℕ) (i : Fin 13) := (sourceWord h (source i)).map (mapBit i)
def stage (h k : ℕ) : Bank
  | .work p => NativeCanonicalParameters.final h p
  | .opcode i => Counter.marked (literal () i)
  | .parameter i => if i.val<k then Counter.marked (parameterWord h i) else ⟨[],[]⟩
def final (h : ℕ) := stage h 13

theorem arithmetic_code (pc : NativeCanonicalParameters.Label)
    (hh : NativeCanonicalParameters.program pc ≠ .halt)
    (_ : NativeCanonicalParameters.program pc ≠ .reject) :
    program (.arithmetic pc)=MicrocodeEmbedding.instruction workBinding.ports Label.arithmetic
      (NativeCanonicalParameters.program pc) := by
  cases pc <;> simp_all [program,NativeCanonicalParameters.program,FinitePortBinding.instruction_eq]

theorem literal_code (pc : NativeLiteralBank.Label Unit 2)
    (hh : NativeLiteralBank.program 2 literal pc ≠ .halt)
    (_ : NativeLiteralBank.program 2 literal pc ≠ .reject) :
    program (.literal pc)=MicrocodeEmbedding.instruction literalBinding.ports Label.literal
      (NativeLiteralBank.program 2 literal pc) := by
  cases pc <;> simp_all [program,NativeLiteralBank.program,FinitePortBinding.instruction_eq]

theorem copy_code (i : Fin 13) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program (mapBit i) pc ≠ .halt)
    (hr : NativeMappedCopy.program (mapBit i) pc ≠ .reject) :
    program (.copy i pc)=MicrocodeEmbedding.instruction (copyBinding i).ports (Label.copy i)
      (NativeMappedCopy.program (mapBit i) pc) := by
  cases pc <;> try { exact (copyBinding i).instruction_eq _ _ }
  rename_i pc; cases pc <;> simp_all [program,NativeMappedCopy.program,NativeSealBack.program,
    FinitePortBinding.instruction_eq,MicrocodeEmbedding.instruction]

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem source_marked (h k : ℕ) (i : Fin 13) :
    stage h k (.work (source i))=Counter.marked (sourceWord h (source i)) := by
  fin_cases i <;> rfl

theorem sourceWord_length (h : ℕ) (i : Fin 13) : (sourceWord h (source i)).length ≤ width h := by
  fin_cases i <;> simp [source,sourceWord,width] <;> omega

theorem parameterWord_length (h : ℕ) (i : Fin 13) : (parameterWord h i).length ≤ width h := by
  simpa only [parameterWord,List.length_map] using sourceWord_length h i

theorem stage_step (h : ℕ) (j : Fin 13) :
    Function.update (stage h j.val) (.parameter j) (Counter.marked (parameterWord h j))=stage h (j.val+1) := by
  funext p; cases p with
  | work p => simp [stage]
  | opcode i => simp [stage]
  | parameter i =>
    by_cases hi : i=j
    · subst i; simp [stage]
    · have hv : i.val≠j.val := by intro h; exact hi (Fin.ext h)
      simp [stage,hi,show (i.val<j.val+1) ↔ (i.val<j.val) by omega]

end BitWord.NativeLargeDescriptors
