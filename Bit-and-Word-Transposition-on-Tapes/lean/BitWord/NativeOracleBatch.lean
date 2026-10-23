import BitWord.NativeOracleBlockRun
import TransposeFollowup.NativeClosedStream

/-! A fixed end-marker-controlled loop around the resettable bit-oracle call.
Block width is a physical unary ruler, not a parameter of the controller. -/
namespace BitWord.NativeOracleBatch
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls
set_option autoImplicit false
noncomputable section
abbrev Port (M : Transpose.TM) := NativeOracleBlock.Port M
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool
abbrev source := NativeOracleBlock.source
abbrev target := NativeOracleBlock.target
abbrev clock := NativeOracleBlock.clock
abbrev blockBank := NativeOracleBlock.blockBank
abbrev blockPos := NativeOracleBlock.blockPos

def allBinding (M : Transpose.TM) : FinitePortBinding (Port M) (Port M) where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]
@[simp] theorem all_values {A : Type*} (M : Transpose.TM) (f g : Port M → A) :
    (allBinding M).values f g=f := rfl

inductive Label (M : Transpose.TM)
  | init (pc : NativeBuffer.Label)
  | check
  | call (pc : NativeOracleBlock.Label M)
  | seal (pc : NativeSealBack.Label)
  | rewind (pc : NativeSealBack.Label)
  | done | reject
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _

def start (M : Transpose.TM) : Label M := .init (.erase 0)
def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .init .done => .jump .check
  | .init pc => (singleBinding (target M)).instruction Label.init (NativeBuffer.program pc)
  | .check => .read (source M) (fun s => match s with
      | .data _ => .call (NativeOracleBlock.start M) | .stop => .seal .seal | _ => .reject)
  | .call .done => .jump .check
  | .call pc => (allBinding M).instruction Label.call (NativeOracleBlock.program M pc)
  | .seal .done => .jump (.rewind .back)
  | .seal pc => (singleBinding (target M)).instruction Label.seal (NativeSealBack.program pc)
  | .rewind .done => .jump .done
  | .rewind pc => (singleBinding (source M)).instruction Label.rewind (NativeSealBack.program pc)
  | .done => .halt | .reject => .reject

abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T := Port M) (L := Label M)

theorem init_code (M : Transpose.TM) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program M (.init pc)=MicrocodeEmbedding.instruction (singleBinding (target M)).ports
      Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem call_code (M : Transpose.TM) (pc : NativeOracleBlock.Label M)
    (hh : NativeOracleBlock.program M pc≠.halt) (_ : NativeOracleBlock.program M pc≠.reject) :
    program M (.call pc)=MicrocodeEmbedding.instruction (allBinding M).ports
      Label.call (NativeOracleBlock.program M pc) := by
  cases pc <;> simp_all [program,NativeOracleBlock.program,FinitePortBinding.instruction_eq]
theorem seal_code (M : Transpose.TM) (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    program M (.seal pc)=MicrocodeEmbedding.instruction (singleBinding (target M)).ports
      Label.seal (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]
theorem rewind_code (M : Transpose.TM) (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    program M (.rewind pc)=MicrocodeEmbedding.instruction (singleBinding (source M)).ports
      Label.rewind (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem jump (M : Transpose.TM) (pc next : Label M) (s : Bank M) (pos : Port M → ℤ)
    (h : program M pc=.jump next) : Trace M 1 (cfg M pc s pos) (cfg M next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem check_call (M : Transpose.TM) (s : Bank M) (pos : Port M → ℤ)
    (sl : List (Sym Bool)) (rest : List Bool) (hs : s (source M)=⟨sl,symbols rest++[.stop]⟩) :
    Trace M 1 (cfg M .check s pos)
      (cfg M (if rest=[] then .seal .seal else .call (NativeOracleBlock.start M)) s pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program,workCfg]
  · have he : NativeMicrocode.step (program M) (cfg M .check s pos)=
        cfg M (if rest=[] then .seal .seal else .call (NativeOracleBlock.start M)) s pos := by
      cases rest <;> simp [NativeMicrocode.step,Microcode.actualStep,cfg,workCfg,program,hs,Tape.read,symbols]
    rw [he]; exact .refl _

theorem block_call (M : Transpose.TM) (xs out fs acc : List Bool)
    (sl sr : List (Sym Bool)) (sp tp kp : ℤ) (T : ℕ)
    (hlen : fs.length=xs.length) (h : Transpose.ComputesWithin M xs out T) :
    ∃ t≤NativeOracleBlock.blockBudget M xs.length out.length T,Trace M t
      (cfg M (.call (NativeOracleBlock.start M))
        (blockBank M ⟨sl,symbols xs++sr⟩ (NativeSealBack.openWord acc) fs) (blockPos M sp tp kp))
      (cfg M (.call .done) (blockBank M ⟨(symbols xs).reverse++sl,sr⟩
        (NativeSealBack.openWord (acc++out)) fs) (blockPos M (sp+xs.length) (tp+out.length) kp)) := by
  obtain ⟨t,ht,htr⟩ := NativeOracleBlock.complete_trace M xs out fs acc sl sr sp tp kp T hlen h
  have hh := MicrocodeEmbedding.trace_embed (allBinding M).ports Label.call (NativeOracleBlock.program M)
    (program M) (frame (fun _ => ⟨[],[]⟩) (fun _ => 0)) (call_code M) htr
  rw [embed_work,embed_work] at hh
  exact ⟨t,ht,by simpa only [all_values] using hh⟩

end
end BitWord.NativeOracleBatch
