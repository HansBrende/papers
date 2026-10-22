import TransposeFollowup.NativeIOFusionCalls
import TransposeFollowup.TracePrefix

/-! Composition of mixed IO programs with selective work-read fusion.
A selected read's successor instruction must be preserved too; return labels
outside those successors remain available for a caller's continuation. -/
namespace TransposeFollowup.NativeIOFusionEmbedding
open FixedTapeCompiler
open MicrocodeEmbedding (Frame)
set_option autoImplicit false
variable {T U L J : Type*}

theorem work_code (ports : T ↪ U) (labels : L → J)
    (source : NativeIO.Program T L) (target : NativeIO.Program U J) (pc : L)
    (hc : target (labels pc)=NativeIOEmbedding.instruction ports labels (source pc)) :
    NativeIO.workProgram target (labels pc)=
      MicrocodeEmbedding.instruction ports labels (NativeIO.workProgram source pc) := by
  cases hs : source pc <;>
    simp only [NativeIO.workProgram,hc,hs,NativeIOEmbedding.instruction,MicrocodeEmbedding.instruction]

theorem step_embed (ports : T ↪ U) (labels : L → J)
    (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (w : List Bool) (c : NativeIO.Config T L) (frame : Frame U)
    (hsel : ts (labels c.work.core.pc)=ss c.work.core.pc)
    (hc : target (labels c.work.core.pc)=NativeIOEmbedding.instruction ports labels (source c.work.core.pc))
    (hr : ss c.work.core.pc=true → ∀ t next,NativeIO.workProgram source c.work.core.pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=
        MicrocodeEmbedding.instruction ports labels (NativeIO.workProgram source (next s))) :
    NativeIOFusion.step target ts w (NativeIOEmbedding.embed ports labels c frame)=
      NativeIOEmbedding.embed ports labels (NativeIOFusion.step source ss w c) frame := by
  cases hs : source c.work.core.pc with
  | work i =>
    have h:=NativeReadFusionEmbedding.step_embed ports labels (NativeIO.workProgram source) (NativeIO.workProgram target)
      ss ts c.work frame hsel (work_code ports labels source target _ hc) hr
    simp only [NativeIOFusion.step,NativeIOEmbedding.embed,MicrocodeEmbedding.embed,hc,hs,NativeIOEmbedding.instruction]
    exact congrArg (fun d => (⟨d,c.inputPos,c.outRev⟩ : NativeIO.Config U J)) h
  | _ =>
    simp only [NativeIOFusion.step,NativeIOEmbedding.embed,MicrocodeEmbedding.embed,hc,hs,NativeIOEmbedding.instruction,
      NativeIO.step,NativeIO.setLabel,Function.comp_apply]

theorem trace_embed (ports : T ↪ U) (labels : L → J)
    (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,NativeIO.workProgram source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=
        MicrocodeEmbedding.instruction ports labels (NativeIO.workProgram source (next s)))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIOFusion.step source ss w) (NativeIOFusion.Active source ss) n c d) :
    OperationalTrace.Trace (NativeIOFusion.step target ts w) (NativeIOFusion.Active target ts) n
      (NativeIOEmbedding.embed ports labels c frame) (NativeIOEmbedding.embed ports labels d frame) := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d ha tr ih =>
    have ha':=(NativeIOFusion.active_iff source ss c).mp ha
    have hh:=(NativeIOEmbedding.active_iff source c).mp ha'
    have hcode:=hc c.work.core.pc hh.1 hh.2
    apply OperationalTrace.Trace.cons
    · apply (NativeIOFusion.active_iff _ _ _).mpr
      exact NativeIOEmbedding.active_embed ports labels source target c frame hcode ha'
    · rw [step_embed ports labels source target ss ts w c frame (hsel _) hcode (hr _)]
      exact ih

theorem run_prefix (ports : T ↪ U) (labels : L → J)
    (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,NativeIO.workProgram source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=
        MicrocodeEmbedding.instruction ports labels (NativeIO.workProgram source (next s)))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIOFusion.step source ss w) (NativeIOFusion.Active source ss) n c d)
    (s : ℕ) (hs : s ≤ n) :
    NativeIOFusion.run target ts w s (NativeIOEmbedding.embed ports labels c frame)=
      NativeIOEmbedding.embed ports labels (NativeIOFusion.run source ss w s c) frame :=
  OperationalTrace.trace_run (trace_embed ports labels source target ss ts frame w hsel hc hr (OperationalTrace.take_trace h s hs))

end TransposeFollowup.NativeIOFusionEmbedding
