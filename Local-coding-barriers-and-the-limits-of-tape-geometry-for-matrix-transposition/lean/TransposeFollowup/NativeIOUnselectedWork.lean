import TransposeFollowup.NativeIOFusionCalls

namespace TransposeFollowup.NativeReadFusion
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

theorem unselected_trace (p : Microcode.Program T L) {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d) :
    OperationalTrace.Trace (step p (fun _ => false)) (Active p (fun _ => false)) n c d := by
  induction h with
  | refl c => exact .refl _
  | cons ha tr ih =>
    apply OperationalTrace.Trace.cons ((active_iff _ _ _).mpr ha)
    rw [step_unselected _ _ _ rfl]
    exact ih

end TransposeFollowup.NativeReadFusion

namespace TransposeFollowup.NativeIOFusionCalls
open FixedTapeCompiler
set_option autoImplicit false
variable {T U L J : Type*}

theorem unselected_work_trace (ports : T ↪ U) (labels : L → J) (source : Microcode.Program T L) (target : NativeIO.Program U J)
    (selected : J → Bool) (frame : MicrocodeEmbedding.Frame U) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (hsel : ∀ pc,selected (labels pc)=false)
    (hc : ∀ pc,source pc≠.halt → source pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (source pc))
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeMicrocode.step source) (NativeMicrocode.Active source) n c d) :
    OperationalTrace.Trace (NativeIOFusion.step target selected w) (NativeIOFusion.Active target selected) n
      ⟨MicrocodeEmbedding.embed ports labels c frame,ip,outRev⟩ ⟨MicrocodeEmbedding.embed ports labels d frame,ip,outRev⟩ :=
  work_trace ports labels source target (fun _ => false) selected frame w ip outRev hsel hc
    (by intro pc h;cases h) (NativeReadFusion.unselected_trace source h)

end TransposeFollowup.NativeIOFusionCalls
