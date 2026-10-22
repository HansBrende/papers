import TransposeFollowup.NativeIOFusionRun
import TransposeFollowup.NativeIOFusionCalls
import TransposeFollowup.TracePrefix

namespace TransposeFollowup.NativeIOFusionCalls
open FixedTapeCompiler
open MicrocodeEmbedding (Frame)
set_option autoImplicit false
variable {T U L J : Type*}

theorem work_prefix (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=MicrocodeEmbedding.instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d)
    (s : ℕ) (hs : s ≤ n) :
    NativeIOFusion.run target ts w s ⟨MicrocodeEmbedding.embed ports labels c frame,ip,outRev⟩=
      ⟨MicrocodeEmbedding.embed ports labels (NativeReadFusion.run source ss s c) frame,ip,outRev⟩ :=
  OperationalTrace.trace_run
    (work_trace ports labels source target ss ts frame w ip outRev hsel hc hr (OperationalTrace.take_trace h s hs))

theorem work_native_prefix {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : NativeIO.Program U J)
    (ss : L → Bool) (ts : J → Bool) (frame : Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,ts (labels pc)=ss pc)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (source pc))
    (hr : ∀ pc,ss pc=true → ∀ t next,source pc=.read t next → ∀ s,
      NativeIO.workProgram target (labels (next s))=MicrocodeEmbedding.instruction ports labels (source (next s)))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step source ss) (NativeReadFusion.Active source ss) n c d)
    (s : ℕ) (hs : s ≤ n) :
    OperationalTrace.run (Transpose.Tape.Impl.next (NativeIOFusion.machine encoding target ts) w) s
      (NativeIOFusion.denote encoding target ts ⟨MicrocodeEmbedding.embed ports labels c frame,ip,outRev⟩)=
      NativeIOFusion.denote encoding target ts
        ⟨MicrocodeEmbedding.embed ports labels (NativeReadFusion.run source ss s c) frame,ip,outRev⟩ := by
  rw [NativeIOFusion.run_denote,work_prefix ports labels source target ss ts frame w ip outRev hsel hc hr h s hs]

end TransposeFollowup.NativeIOFusionCalls
