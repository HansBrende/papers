import TransposeFollowup.NativeIOCore
import TransposeFollowup.FinitePortBinding

/-! Static port/label wiring for native programs that also use the original
input and output tapes. Reuse the existing work-tape frame theorem; preserve
its exact transition count while propagating input position and output. -/
namespace TransposeFollowup.NativeIOEmbedding
open FixedTapeCompiler
set_option autoImplicit false
variable {T U L J : Type*}

noncomputable def instruction (ports : T ↪ U) (labels : L → J) : NativeIO.Instruction T L → NativeIO.Instruction U J
  | .work i => .work (MicrocodeEmbedding.instruction ports labels i)
  | .readInput next => .readInput (labels ∘ next)
  | .moveInput dir next => .moveInput dir (labels next)
  | .output bit next => .output bit (labels next)

def boundInstruction (b : FinitePortBinding T U) (labels : L → J) : NativeIO.Instruction T L → NativeIO.Instruction U J
  | .work i => .work (b.instruction labels i)
  | .readInput next => .readInput (labels ∘ next)
  | .moveInput dir next => .moveInput dir (labels next)
  | .output bit next => .output bit (labels next)

theorem bound_instruction_eq (b : FinitePortBinding T U) (labels : L → J) (i : NativeIO.Instruction T L) :
    boundInstruction b labels i=instruction b.ports labels i := by
  cases i <;> simp only [boundInstruction,instruction,FinitePortBinding.instruction_eq]

noncomputable def embed (ports : T ↪ U) (labels : L → J) (c : NativeIO.Config T L)
    (frame : MicrocodeEmbedding.Frame U) : NativeIO.Config U J :=
  ⟨MicrocodeEmbedding.embed ports labels c.work frame,c.inputPos,c.outRev⟩

theorem step_embed (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (w : List Bool) (c : NativeIO.Config T L) (frame : MicrocodeEmbedding.Frame U)
    (hc : target (labels c.work.core.pc)=instruction ports labels (source c.work.core.pc)) :
    NativeIO.step target w (embed ports labels c frame)=embed ports labels (NativeIO.step source w c) frame := by
  cases hs : source c.work.core.pc with
  | work i =>
    have hw : NativeIO.workProgram target (labels c.work.core.pc)=
        MicrocodeEmbedding.instruction ports labels (NativeIO.workProgram source c.work.core.pc) := by
      simp only [NativeIO.workProgram,hc,hs,instruction]
    have h := MicrocodeEmbedding.step_embed ports labels (NativeIO.workProgram source) (NativeIO.workProgram target) c.work frame hw
    simp only [NativeIO.step,embed,MicrocodeEmbedding.embed,hc,hs,instruction]
    exact congrArg (fun d => (⟨d,c.inputPos,c.outRev⟩ : NativeIO.Config U J)) h
  | _ => simp only [NativeIO.step,embed,MicrocodeEmbedding.embed,hc,hs,instruction,NativeIO.setLabel,Function.comp_apply]

theorem active_iff (source : NativeIO.Program T L) (c : NativeIO.Config T L) :
    NativeIO.Active source c ↔ source c.work.core.pc≠.work .halt ∧ source c.work.core.pc≠.work .reject := by
  cases hs : source c.work.core.pc <;> simp [NativeIO.Active,hs]

theorem active_embed (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (c : NativeIO.Config T L) (frame : MicrocodeEmbedding.Frame U)
    (hc : target (labels c.work.core.pc)=instruction ports labels (source c.work.core.pc))
    (ha : NativeIO.Active source c) : NativeIO.Active target (embed ports labels c frame) := by
  cases hs : source c.work.core.pc with
  | work i => cases i <;> simp_all [NativeIO.Active,embed,MicrocodeEmbedding.embed,instruction,MicrocodeEmbedding.instruction]
  | _ => simp_all [NativeIO.Active,embed,MicrocodeEmbedding.embed,instruction]

theorem trace_embed (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (frame : MicrocodeEmbedding.Frame U) (w : List Bool)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject → target (labels pc)=instruction ports labels (source pc))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIO.step source w) (NativeIO.Active source) n c d) :
    OperationalTrace.Trace (NativeIO.step target w) (NativeIO.Active target) n
      (embed ports labels c frame) (embed ports labels d frame) := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d ha tr ih =>
    have hh := (active_iff source c).mp ha
    have hcode := hc c.work.core.pc hh.1 hh.2
    refine .cons (active_embed ports labels source target c frame hcode ha) ?_
    rw [step_embed ports labels source target w c frame hcode]
    exact ih

theorem native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (frame : MicrocodeEmbedding.Frame U) (w : List Bool)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject → target (labels pc)=instruction ports labels (source pc))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIO.step source w) (NativeIO.Active source) n c d) :
    Transpose.stepN (NativeIO.machine encoding target) w n ((embed ports labels c frame).denote encoding target)=
      some ((embed ports labels d frame).denote encoding target) :=
  NativeIO.trace_stepN encoding target w (trace_embed ports labels source target frame w hc h)

theorem unused_tape (ports : T ↪ U) (labels : L → J) (c : NativeIO.Config T L)
    (frame : MicrocodeEmbedding.Frame U) (u : U) (h : ¬∃ t,ports t=u) :
    (embed ports labels c frame).work.core.tapes u=frame.tapes u ∧
      (embed ports labels c frame).work.pos u=frame.pos u :=
  MicrocodeEmbedding.unused_tape ports labels c.work frame u h

end TransposeFollowup.NativeIOEmbedding
