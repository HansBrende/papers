import BitWord.NativeLargeDescriptors
import BitWord.NativeSmallClassifier

/-! The uniform size branch is chosen by a paid bounded scan of the measured
entry-width word. Both branches use the same physical descriptor tapes. -/
namespace BitWord.NativeCanonicalGenerator
open FixedTapeCompiler CopyMachine TransposeFollowup NativeExpanderShearFrames
open NativeBankCalls CanonicalMetadata
set_option autoImplicit false

abbrev Port := NativeLargeDescriptors.Port
abbrev Bank := Port → Tape Bool

def smallPort : NativeSmallDescriptors.Port → Port
  | .u => .work .u | .w => .work .double | .n => .work .total | .r => .work .diff
  | .opcode i => .opcode i | .parameter i => .parameter i

def smallBinding : FinitePortBinding NativeSmallDescriptors.Port Port where
  ports := ⟨smallPort,by intro a b h; cases a <;> cases b <;> simp_all [smallPort]⟩
  decode := fun p => match p with
    | .work .u => some .u | .work .double => some .w
    | .work .total => some .n | .work .diff => some .r
    | .opcode i => some (.opcode i) | .parameter i => some (.parameter i)
    | _ => none
  decode_spec := by
    intro p q
    change (match p with
      | .work .u => some .u | .work .double => some .w
      | .work .total => some .n | .work .diff => some .r
      | .opcode i => some (.opcode i) | .parameter i => some (.parameter i)
      | _ => none)=some q ↔ smallPort q=p
    cases p with
    | work p => cases p <;> cases q <;> simp [smallPort]
    | opcode i => cases q <;> simp [smallPort,eq_comm]
    | parameter i => cases q <;> simp [smallPort,eq_comm]

def classifierBinding := singleBinding (NativeLargeDescriptors.Port.work .h)
def largeBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p q; simp [eq_comm]

inductive Label
  | classifier (pc : NativeSmallClassifier.Label)
  | small (pc : NativeSmallDescriptors.Label)
  | large (pc : NativeLargeDescriptors.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .classifier (.scan 0)
def branch (a : Fin 33) : Label := if ha : a.val < 32 then .small (.start ⟨a.val,ha⟩)
  else .large NativeLargeDescriptors.start

def program : Microcode.Program Port Label
  | .classifier (.done a) => .jump (branch a)
  | .classifier pc => classifierBinding.instruction Label.classifier (NativeSmallClassifier.program pc)
  | .small (.done _) => .jump .done
  | .small pc => smallBinding.instruction Label.small (NativeSmallDescriptors.program pc)
  | .large .done => .jump .done
  | .large pc => largeBinding.instruction Label.large (NativeLargeDescriptors.program pc)
  | .done => .halt

abbrev cfg := workCfg (T := Port) (L := Label)
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
abbrev initial := NativeLargeDescriptors.initial

def smallFinal (h : Fin 32) := smallBinding.values (NativeSmallDescriptors.final h) (initial h)
def final (h : ℕ) : Bank := if hh : h < 32 then smallFinal ⟨h,hh⟩ else NativeLargeDescriptors.final h

def fieldWord (h : ℕ) (p : NativeSmallDescriptors.Port) : List Bool :=
  if hh : h < 32 then NativeSmallDescriptors.word ⟨h,hh⟩ p else match p with
    | .u => uword h | .w => W h | .n => N h | .r => R h
    | .opcode i => NativeLargeDescriptors.literal () i
    | .parameter i => NativeLargeDescriptors.parameterWord h i

theorem classifier_code (pc : NativeSmallClassifier.Label)
    (hh : NativeSmallClassifier.program pc ≠ .halt)
    (_ : NativeSmallClassifier.program pc ≠ .reject) :
    program (.classifier pc)=MicrocodeEmbedding.instruction classifierBinding.ports Label.classifier
      (NativeSmallClassifier.program pc) := by
  cases pc <;> simp_all [program,NativeSmallClassifier.program,FinitePortBinding.instruction_eq]

theorem small_code (pc : NativeSmallDescriptors.Label)
    (hh : NativeSmallDescriptors.program pc ≠ .halt)
    (_ : NativeSmallDescriptors.program pc ≠ .reject) :
    program (.small pc)=MicrocodeEmbedding.instruction smallBinding.ports Label.small
      (NativeSmallDescriptors.program pc) := by
  cases pc <;> simp_all [program,NativeSmallDescriptors.program,NativeLiteralBank.program,
    FinitePortBinding.instruction_eq]

theorem large_code (pc : NativeLargeDescriptors.Label)
    (hh : NativeLargeDescriptors.program pc ≠ .halt)
    (_ : NativeLargeDescriptors.program pc ≠ .reject) :
    program (.large pc)=MicrocodeEmbedding.instruction largeBinding.ports Label.large
      (NativeLargeDescriptors.program pc) := by
  cases pc <;> simp_all [program,NativeLargeDescriptors.program,FinitePortBinding.instruction_eq]

theorem jump (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem final_fields (h : ℕ) (p : NativeSmallDescriptors.Port) :
    final h (smallPort p)=Counter.marked (fieldWord h p) := by
  by_cases hh : h < 32
  · simp [final,fieldWord,hh,smallFinal,smallBinding,smallPort,FinitePortBinding.values,
      NativeSmallDescriptors.final]
    cases p <;> rfl
  · cases p <;> simp [final,fieldWord,hh,smallPort,NativeLargeDescriptors.final,
      NativeLargeDescriptors.stage,NativeCanonicalParameters.final]

theorem final_h (h : ℕ) : final h (.work .h)=Counter.marked (hword h) := by
  by_cases hh : h < 32 <;> simp [final,hh,smallFinal,smallBinding,FinitePortBinding.values,
    initial,NativeLargeDescriptors.initial,NativeCanonicalParameters.initial,
    NativeLargeDescriptors.final,NativeLargeDescriptors.stage,NativeCanonicalParameters.final]

end BitWord.NativeCanonicalGenerator
