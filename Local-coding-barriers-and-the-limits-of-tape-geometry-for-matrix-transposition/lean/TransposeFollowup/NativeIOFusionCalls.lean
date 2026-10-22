import TransposeFollowup.NativeIOFusionRunCore
import TransposeFollowup.NativeReadFusionEmbedding
import TransposeFollowup.NativeIOEmbedding

/-! Two call interfaces into one selected-fusion IO machine: ordinary IO
programs on unselected labels, and fused work programs on selected labels. -/
namespace TransposeFollowup.NativeIOFusionCalls
open FixedTapeCompiler
open MicrocodeEmbedding (Frame)
set_option autoImplicit false
variable {T U L J : Type*}

theorem unselected_trace (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L)
    (target : NativeIO.Program U J) (selected : J → Bool) (frame : Frame U) (w : List Bool)
    (hsel : ∀ pc,selected (labels pc)=false)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (source pc))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIO.step source w) (NativeIO.Active source) n c d) :
    OperationalTrace.Trace (NativeIOFusion.step target selected w) (NativeIOFusion.Active target selected) n
      (NativeIOEmbedding.embed ports labels c frame) (NativeIOEmbedding.embed ports labels d frame) := by
  induction h with
  | refl c => exact .refl _
  | @cons n c d ha tr ih =>
    have hh:=(NativeIOEmbedding.active_iff source c).mp ha
    have hcode:=hc c.work.core.pc hh.1 hh.2
    apply OperationalTrace.Trace.cons
    · apply (NativeIOFusion.active_iff _ _ _).mpr
      exact NativeIOEmbedding.active_embed ports labels source target c frame hcode ha
    · rw [NativeIOFusion.step_unselected _ _ _ _ (hsel c.work.core.pc),
        NativeIOEmbedding.step_embed ports labels source target w c frame hcode]
      exact ih

theorem unselected_native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : NativeIO.Program T L) (target : NativeIO.Program U J)
    (selected : J → Bool) (frame : Frame U) (w : List Bool)
    (hsel : ∀ pc,selected (labels pc)=false)
    (hc : ∀ pc,source pc≠.work .halt → source pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (source pc))
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIO.step source w) (NativeIO.Active source) n c d) :
    Transpose.stepN (NativeIOFusion.machine encoding target selected) w n
      (NativeIOFusion.denote encoding target selected (NativeIOEmbedding.embed ports labels c frame))=
      some (NativeIOFusion.denote encoding target selected (NativeIOEmbedding.embed ports labels d frame)) :=
  NativeIOFusion.trace_stepN encoding target selected w (unselected_trace ports labels source target selected frame w hsel hc h)

theorem work_trace (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=MicrocodeEmbedding.instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d) :
    OperationalTrace.Trace (NativeIOFusion.step target ts w) (NativeIOFusion.Active target ts) n
      ⟨MicrocodeEmbedding.embed ports labels c frame,ip,outRev⟩
      ⟨MicrocodeEmbedding.embed ports labels d frame,ip,outRev⟩ :=
  NativeIOFusion.lift_work_trace target ts w ip outRev
    (NativeReadFusionEmbedding.trace_embed ports labels source (NativeIO.workProgram target) ss ts frame hsel hc hr h)

theorem work_native_call {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=MicrocodeEmbedding.instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d) :
    Transpose.stepN (NativeIOFusion.machine encoding target ts) w n
      (NativeIOFusion.denote encoding target ts ⟨MicrocodeEmbedding.embed ports labels c frame,ip,outRev⟩)=
      some (NativeIOFusion.denote encoding target ts ⟨MicrocodeEmbedding.embed ports labels d frame,ip,outRev⟩) :=
  NativeIOFusion.trace_stepN encoding target ts w (work_trace ports labels source target ss ts frame w ip outRev hsel hc hr h)

end TransposeFollowup.NativeIOFusionCalls
