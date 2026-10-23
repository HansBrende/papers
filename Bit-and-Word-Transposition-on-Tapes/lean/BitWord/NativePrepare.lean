import BitWord.NativeBootstrap
import BitWord.NativeCanonicalGeneratorRun
import BitWord.CanonicalBounds

/-! Complete raw-input setup: recover shape, generate the fixed gate recipe,
and construct every physical normalization ruler. -/
namespace BitWord.NativePrepare
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeExpanderShearFrames NativeCountedLoop

inductive Port
  | bootstrap (p : NativeBootstrap.Port)
  | generator (p : NativeCanonicalGenerator.Port)
  | rulers (p : NativeRulers.Port)
  deriving DecidableEq,Fintype
abbrev Bank := Port → Tape Bool

def bootstrapBinding : FinitePortBinding NativeBootstrap.Port Port where
  ports := ⟨Port.bootstrap,by intro p q h; cases h; rfl⟩
  decode := fun p => match p with | .bootstrap q => some q | _ => none
  decode_spec := by
    intro p q
    change (match p with | .bootstrap r => some r | _ => none)=some q ↔ Port.bootstrap q=p
    cases p <;> simp [eq_comm]

def generatorPort (p : NativeCanonicalGenerator.Port) : Port :=
  if p=.work .h then .bootstrap .hword else .generator p

def generatorBinding : FinitePortBinding NativeCanonicalGenerator.Port Port where
  ports := ⟨generatorPort,by
    intro p q h
    by_cases hp : p=.work .h <;> by_cases hq : q=.work .h <;> simp_all [generatorPort]⟩
  decode := fun p => match p with
    | .bootstrap .hword => some (.work .h)
    | .generator q => if q=.work .h then none else some q
    | _ => none
  decode_spec := by
    intro p q
    change (match p with
      | .bootstrap .hword => some (.work .h)
      | .generator r => if r=.work .h then none else some r
      | _ => none)=some q ↔ generatorPort q=p
    by_cases hq : q=.work .h
    · subst q; cases p with
      | bootstrap p => cases p <;> simp [generatorPort]
      | generator p => by_cases hp : p=.work .h <;> simp_all [generatorPort]
      | rulers p => simp [generatorPort]
    · cases p with
      | bootstrap p => cases p <;> simp_all [generatorPort,Ne.symm hq]
      | generator p => by_cases hp : p=.work .h <;> simp_all [generatorPort,eq_comm]
      | rulers p => simp [generatorPort,hq]

def rulerPort : NativeRulers.Port → Port
  | .dimension => .bootstrap NativeBootstrap.dimension
  | .hword => .bootstrap .hword
  | .wword => .generator (.work .double)
  | p => .rulers p

def rulersBinding : FinitePortBinding NativeRulers.Port Port where
  ports := ⟨rulerPort,by intro p q h; cases p <;> cases q <;> simp_all [rulerPort,NativeBootstrap.dimension]⟩
  decode := fun p => match p with
    | .bootstrap (.raw (.loader (.work .candidate))) => some .dimension
    | .bootstrap .hword => some .hword
    | .generator (.work .double) => some .wword
    | .rulers q => match q with | .dimension | .hword | .wword => none | _ => some q
    | _ => none
  decode_spec := by
    intro p q
    change _ = some q ↔ rulerPort q=p
    cases q <;> cases p with
    | bootstrap p => cases p with
      | raw p => cases p with
        | payload => decide +kernel
        | loader p => cases p with
          | work p => cases p <;> decide +kernel
          | source => decide +kernel
          | extra => decide +kernel
      | scratchA => decide +kernel
      | scratchB => decide +kernel
      | hword => decide +kernel
    | generator p => cases p with
      | work p => cases p <;> decide +kernel
      | opcode i => simp [rulerPort,NativeBootstrap.dimension]
      | parameter i => simp [rulerPort,NativeBootstrap.dimension]
    | rulers p => cases p <;> decide +kernel

inductive Label
  | bootstrap (pc : NativeBootstrap.Label)
  | generator (pc : NativeCanonicalGenerator.Label)
  | rulers (pc : NativeRulers.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .bootstrap NativeBootstrap.start
def program : NativeIO.Program Port Label
  | .bootstrap .done => .work (.jump (.generator NativeCanonicalGenerator.start))
  | .bootstrap pc => NativeIOEmbedding.boundInstruction bootstrapBinding Label.bootstrap (NativeBootstrap.program pc)
  | .generator .done => .work (.jump (.rulers NativeRulers.start))
  | .generator pc => .work (generatorBinding.instruction Label.generator (NativeCanonicalGenerator.program pc))
  | .rulers .done => .work (.jump .done)
  | .rulers pc => .work (rulersBinding.instruction Label.rulers (NativeRulers.program pc))
  | .done => .work .halt

def initial : Bank := fun _ => ⟨[],[]⟩
def h (xs : List Bool) := Transpose.entryBits (Counter.value xs)
def hword (xs : List Bool) := MeasuredWord.result (h xs)
def wword (xs : List Bool) := NativeCanonicalGenerator.fieldWord (h xs) .w

def loaded (w xs : List Bool) : Bank := bootstrapBinding.values (NativeBootstrap.final w xs) initial
def generated (w xs : List Bool) : Bank := generatorBinding.values (NativeCanonicalGenerator.final (h xs)) (loaded w xs)
def final (w xs : List Bool) : Bank :=
  rulersBinding.values (NativeRulers.final xs (hword xs) (wword xs)) (generated w xs)

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (out : List Bool) : NativeIO.Config Port Label :=
  NativeExpanderShearFrames.cfg pc s pos ip out
abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem bootstrap_code (pc : NativeBootstrap.Label) (hh : NativeBootstrap.program pc≠.work .halt)
    (_ : NativeBootstrap.program pc≠.work .reject) :
    program (.bootstrap pc)=NativeIOEmbedding.instruction bootstrapBinding.ports Label.bootstrap (NativeBootstrap.program pc) := by
  cases pc <;> simp_all [program,NativeBootstrap.program,NativeIOEmbedding.bound_instruction_eq]

theorem generator_code (pc : NativeCanonicalGenerator.Label) (hh : NativeCanonicalGenerator.program pc≠.halt)
    (_ : NativeCanonicalGenerator.program pc≠.reject) :
    NativeIO.workProgram program (.generator pc)=MicrocodeEmbedding.instruction generatorBinding.ports Label.generator
      (NativeCanonicalGenerator.program pc) := by
  cases pc <;> simp_all [program,NativeIO.workProgram,NativeCanonicalGenerator.program,FinitePortBinding.instruction_eq]

theorem rulers_code (pc : NativeRulers.Label) (hh : NativeRulers.program pc≠.halt)
    (_ : NativeRulers.program pc≠.reject) :
    NativeIO.workProgram program (.rulers pc)=MicrocodeEmbedding.instruction rulersBinding.ports Label.rulers
      (NativeRulers.program pc) := by
  cases pc <;> simp_all [program,NativeIO.workProgram,NativeRulers.program,FinitePortBinding.instruction_eq]

theorem generator_initial (w xs : List Bool) :
    (fun p => loaded w xs (generatorPort p))=NativeCanonicalGenerator.initial (h xs) := by
  funext p
  cases p with
  | work p => cases p <;> rfl
  | opcode i => rfl
  | parameter i => rfl

theorem rulers_initial (w xs : List Bool) :
    (fun p => generated w xs (rulerPort p))=NativeRulers.initial xs (hword xs) (wword xs) := by
  funext p
  cases p with
  | hword =>
    change NativeCanonicalGenerator.final (h xs) (.work .h)=Counter.marked (hword xs)
    exact NativeCanonicalGenerator.final_h _
  | wword =>
    change NativeCanonicalGenerator.final (h xs) (.work .double)=Counter.marked (wword xs)
    exact NativeCanonicalGenerator.final_fields _ .w
  | dimension => rfl
  | d => rfl
  | h => rfl
  | D => rfl
  | B => rfl
  | dB => rfl
  | DB => rfl
  | fuelA => rfl
  | fuelB => rfl
  | powD => rfl
  | powB => rfl

end BitWord.NativePrepare
