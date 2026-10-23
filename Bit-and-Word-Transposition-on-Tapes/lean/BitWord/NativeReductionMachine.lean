import BitWord.NativePrepareFields
import BitWord.NativeNormalizeRun
import BitWord.NativeStages
import BitWord.NativeHalfRuler
import BitWord.NativeFixedBinding
import TransposeFollowup.NativeMatchingXorOutput

/-! The single fixed native controller for the bit-to-word reduction. Every
subroutine shares only declared physical tapes; no runtime descriptor is copied
or installed in finite control for free. Trace assembly is in the next module. -/
namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
open NativeBankCalls
set_option autoImplicit false
noncomputable section

inductive Port (M : Transpose.TM)
  | prepare (p : NativePrepare.Port)
  | data (p : NativeStages.DataPort M)
  | normalize (p : Fin 2)
  | half (p : Fin 3)
  deriving Fintype
instance (M : Transpose.TM) : DecidableEq (Port M) := Classical.decEq _
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool

def main (M : Transpose.TM) : Port M := .prepare NativePrepare.mainPort

def prepareBinding (M : Transpose.TM) : FinitePortBinding NativePrepare.Port (Port M) :=
  fixedBinding ⟨Port.prepare,by intro p q h; exact Port.prepare.inj h⟩

def dataPort (M : Transpose.TM) (p : NativeStages.DataPort M) : Port M :=
  if p=NativeGate.main M then main M else .data p

def stagesPort (M : Transpose.TM) : NativeStages.Port M → Port M
  | .inl p => dataPort M p
  | .inr (false,i) => .prepare (NativePrepare.generatorPort (.parameter i))
  | .inr (true,i) => .prepare (NativePrepare.generatorPort (.opcode i))

theorem dataPort_injective (M : Transpose.TM) : Function.Injective (dataPort M) := by
  intro p q h
  by_cases hp : p=NativeGate.main M <;> by_cases hq : q=NativeGate.main M <;>
    simp_all [dataPort,main]

theorem stagesPort_injective (M : Transpose.TM) : Function.Injective (stagesPort M) := by
  intro p q h
  cases p with
  | inl p =>
    cases q with
    | inl q => exact congrArg Sum.inl (dataPort_injective M h)
    | inr q =>
      rcases q with ⟨b,j⟩
      cases b <;> by_cases hp : p=NativeGate.main M <;>
        simp_all [stagesPort,dataPort,main,NativePrepare.mainPort,NativePrepare.generatorPort,
          NativeBootstrap.payload]
  | inr p =>
    rcases p with ⟨b,i⟩
    cases q with
    | inl q =>
      cases b <;> by_cases hq : q=NativeGate.main M <;>
        simp_all [stagesPort,dataPort,main,NativePrepare.mainPort,NativePrepare.generatorPort,
          NativeBootstrap.payload]
    | inr q =>
      rcases q with ⟨c,j⟩
      cases b <;> cases c <;> simp_all [stagesPort,NativePrepare.generatorPort]

def stagesBinding (M : Transpose.TM) : FinitePortBinding (NativeStages.Port M) (Port M) :=
  fixedBinding ⟨stagesPort M,stagesPort_injective M⟩

def normalizePorts (M : Transpose.TM) : Fin 9 → Port M :=
  ![main M,.normalize 0,.normalize 1,
    .prepare (NativePrepare.rulerPort .h),.prepare (NativePrepare.rulerPort .B),
    .prepare (NativePrepare.rulerPort .d),.prepare (NativePrepare.rulerPort .D),
    .prepare (NativePrepare.rulerPort .dB),.prepare (NativePrepare.rulerPort .DB)]

def normalizeBinding (M : Transpose.TM) : FinitePortBinding NativeNormalize.Port (Port M) :=
  fixedBinding ⟨normalizePorts M,by
    intro p q h
    fin_cases p <;> fin_cases q <;>
      simp_all [normalizePorts,main,NativePrepare.rulerPort,NativePrepare.mainPort]⟩

def halfPort (M : Transpose.TM) : NativeHalfRuler.Port → Port M
  | .inr _ => .prepare (NativePrepare.generatorPort (.work .total))
  | .inl .source => .half 0
  | .inl .fuel => .half 1
  | .inl .power => .half 2
  | .inl .result => .data (NativeGate.halfRuler M)

def halfBinding (M : Transpose.TM) : FinitePortBinding NativeHalfRuler.Port (Port M) :=
  fixedBinding ⟨halfPort M,by
    intro p q h
    cases p with
    | inl p => cases q with
      | inl q => cases p <;> cases q <;> simp_all [halfPort]
      | inr q => cases p <;> simp_all [halfPort]
    | inr p => cases q with
      | inl q => cases q <;> simp_all [halfPort]
      | inr q => exact congrArg Sum.inr (Subsingleton.elim p q)⟩

def outputBinding (M : Transpose.TM) : FinitePortBinding (Fin 1) (Port M) := singleBinding (main M)

@[simp] theorem prepareBinding_ports (M : Transpose.TM) (p : NativePrepare.Port) :
    (prepareBinding M).ports p=Port.prepare p := rfl
@[simp] theorem stagesBinding_ports (M : Transpose.TM) (p : NativeStages.Port M) :
    (stagesBinding M).ports p=stagesPort M p := rfl
@[simp] theorem normalizeBinding_ports (M : Transpose.TM) (p : NativeNormalize.Port) :
    (normalizeBinding M).ports p=normalizePorts M p := rfl
@[simp] theorem halfBinding_ports (M : Transpose.TM) (p : NativeHalfRuler.Port) :
    (halfBinding M).ports p=halfPort M p := rfl
@[simp] theorem outputBinding_ports (M : Transpose.TM) (p : Fin 1) :
    (outputBinding M).ports p=main M := rfl

inductive Label (M : Transpose.TM)
  | prepare (pc : NativePrepare.Label)
  | normalize (expand : Bool) (pc : NativeNormalize.Label)
  | half (pc : NativeHalfRuler.Label)
  | stages (pc : NativeStages.Label M)
  | output (pc : NativeMatchingXorOutput.Label)
  | done
  deriving Fintype
instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _

def start (M : Transpose.TM) : Label M := .prepare NativePrepare.start

def program (M : Transpose.TM) : NativeIO.Program (Port M) (Label M)
  | .prepare .done => .work (.jump (.normalize true (NativeNormalize.start true)))
  | .prepare pc => NativeIOEmbedding.boundInstruction (prepareBinding M) Label.prepare (NativePrepare.program pc)
  | .normalize true .done => .work (.jump (.half NativeHalfRuler.start))
  | .normalize false .done => .work (.jump (.output .read))
  | .normalize expand pc => .work ((normalizeBinding M).instruction (Label.normalize expand) (NativeNormalize.program expand pc))
  | .half .done => .work (.jump (.stages (NativeStages.start M)))
  | .half pc => .work ((halfBinding M).instruction Label.half (NativeHalfRuler.program pc))
  | .stages .done => .work (.jump (.normalize false (NativeNormalize.start false)))
  | .stages pc => .work ((stagesBinding M).instruction Label.stages (NativeStages.program M pc))
  | .output .done => .work (.jump .done)
  | .output pc => NativeIOEmbedding.boundInstruction (outputBinding M) Label.output (NativeMatchingXorOutput.program pc)
  | .done => .work .halt

def cfg (M : Transpose.TM) (pc : Label M) (s : Bank M) (pos : Port M → ℤ)
    (ip : ℤ) (out : List Bool) : NativeIO.Config (Port M) (Label M) :=
  NativeExpanderShearFrames.cfg pc s pos ip out
abbrev Trace (M : Transpose.TM) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program M) w) (NativeIO.Active (program M))

theorem prepare_code (M : Transpose.TM) (pc : NativePrepare.Label)
    (hh : NativePrepare.program pc≠.work .halt) (_ : NativePrepare.program pc≠.work .reject) :
    program M (.prepare pc)=NativeIOEmbedding.instruction (prepareBinding M).ports Label.prepare
      (NativePrepare.program pc) := by
  cases pc <;> simp_all [program,NativePrepare.program,NativeIOEmbedding.bound_instruction_eq]

theorem normalize_code (M : Transpose.TM) (expand : Bool) (pc : NativeNormalize.Label)
    (hh : NativeNormalize.program expand pc≠.halt) (_ : NativeNormalize.program expand pc≠.reject) :
    NativeIO.workProgram (program M) (.normalize expand pc)=
      MicrocodeEmbedding.instruction (normalizeBinding M).ports (Label.normalize expand)
        (NativeNormalize.program expand pc) := by
  cases pc <;> cases expand <;>
    simp_all [program,NativeIO.workProgram,NativeNormalize.program,FinitePortBinding.instruction_eq]

theorem half_code (M : Transpose.TM) (pc : NativeHalfRuler.Label)
    (hh : NativeHalfRuler.program pc≠.halt) (_ : NativeHalfRuler.program pc≠.reject) :
    NativeIO.workProgram (program M) (.half pc)=
      MicrocodeEmbedding.instruction (halfBinding M).ports Label.half (NativeHalfRuler.program pc) := by
  cases pc <;> simp_all [program,NativeIO.workProgram,NativeHalfRuler.program,FinitePortBinding.instruction_eq]

theorem stages_code (M : Transpose.TM) (pc : NativeStages.Label M)
    (hh : NativeStages.program M pc≠.halt) (_ : NativeStages.program M pc≠.reject) :
    NativeIO.workProgram (program M) (.stages pc)=
      MicrocodeEmbedding.instruction (stagesBinding M).ports Label.stages (NativeStages.program M pc) := by
  cases pc <;> simp_all [program,NativeIO.workProgram,NativeStages.program,FinitePortBinding.instruction_eq]

theorem output_code (M : Transpose.TM) (pc : NativeMatchingXorOutput.Label)
    (hh : NativeMatchingXorOutput.program pc≠.work .halt)
    (_ : NativeMatchingXorOutput.program pc≠.work .reject) :
    program M (.output pc)=NativeIOEmbedding.instruction (outputBinding M).ports Label.output
      (NativeMatchingXorOutput.program pc) := by
  cases pc <;> simp_all [program,NativeMatchingXorOutput.program,NativeIOEmbedding.bound_instruction_eq]

theorem jump (M : Transpose.TM) (w : List Bool) (pc next : Label M) (s : Bank M)
    (pos : Port M → ℤ) (ip : ℤ) (out : List Bool)
    (hc : program M pc=.work (.jump next)) : Trace M w 1 (cfg M pc s pos ip out) (cfg M next s pos ip out) :=
  NativeIO.jump_trace (program M) w (cfg M pc s pos ip out) next hc

noncomputable def nativeEncoding (M : Transpose.TM) := NativeMicrocode.initialEncoding (T:=Port M) (start M)
noncomputable def nativeMachine (M : Transpose.TM) := NativeIO.machine (nativeEncoding M) (program M)

theorem initial_state_zero (M : Transpose.TM) : (nativeEncoding M).label (start M)=0 :=
  NativeMicrocode.initialEncoding_start _

end
end BitWord.NativeReductionMachine
