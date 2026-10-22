import TransposeFollowup.FusedPageClockTrajectory
import TransposeFollowup.NativeIOFusionPrefixes

/-! Call the fused clock inside a native IO machine. Every source label
except its final return is preserved; the caller may replace that return.
All prefix positions and all unused caller tapes are retained. -/
namespace TransposeFollowup.FusedPageClockIO
open FixedTapeCompiler
open ReusablePageClock (Port Label program cfg)
set_option autoImplicit false
variable {q : ℕ} {U J : Type*} {k z : ℕ}

theorem read_next_ne_done (ops : Fin q → PageOpcode) (pc : Label) (t : Port q)
    (next : CopyMachine.Sym Bool → Label) (h : program ops pc=.read t next) (s : CopyMachine.Sym Bool) :
    next s≠.inr .done := by
  cases pc with
  | inl pc =>
    cases pc <;> simp [program,PageClock.program,FinitePortBinding.instruction] at h
    rcases h with ⟨rfl,rfl⟩
    simp
  | inr pc =>
    cases pc <;> simp [program,NativeSealBack.program,FinitePortBinding.instruction] at h
    rcases h with ⟨rfl,rfl⟩
    cases s <;> simp

theorem trace_call (ops : Fin q → PageOpcode) (ports : Port q ↪ U) (labels : Label → J)
    (target : NativeIO.Program U J) (selected : J → Bool) (frame : MicrocodeEmbedding.Frame U)
    (hsel : ∀ pc,selected (labels pc)=FusedPageClock.selected pc)
    (hc : ∀ pc,pc≠.inr .done → NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (pos : Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    OperationalTrace.Trace (NativeIOFusion.step target selected w) (NativeIOFusion.Active target selected) (2*xs.length+3)
      ⟨MicrocodeEmbedding.embed ports labels (cfg (.inl .read) (FixedTapeCompiler.Counter.marked xs) pos) frame,ip,outRev⟩
      ⟨MicrocodeEmbedding.embed ports labels
        (cfg (.inr .done) (FixedTapeCompiler.Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) frame,ip,outRev⟩ := by
  apply NativeIOFusionCalls.work_trace ports labels (program ops) target FusedPageClock.selected selected frame w ip outRev hsel
  · intro pc hh _
    apply hc pc
    intro he;subst pc
    exact hh rfl
  · intro pc _ t next h s
    exact hc (next s) (read_next_ne_done ops pc t next h s)
  · exact FusedPageClock.complete_trace ops xs pos

theorem native_call (encoding : NativeMicrocode.Encoding U J k z)
    (ops : Fin q → PageOpcode) (ports : Port q ↪ U) (labels : Label → J)
    (target : NativeIO.Program U J) (selected : J → Bool) (frame : MicrocodeEmbedding.Frame U)
    (hsel : ∀ pc,selected (labels pc)=FusedPageClock.selected pc)
    (hc : ∀ pc,pc≠.inr .done → NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (pos : Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (NativeIOFusion.machine encoding target selected) w (2*xs.length+3)
      (NativeIOFusion.denote encoding target selected
        ⟨MicrocodeEmbedding.embed ports labels (cfg (.inl .read) (FixedTapeCompiler.Counter.marked xs) pos) frame,ip,outRev⟩)=
      some (NativeIOFusion.denote encoding target selected
        ⟨MicrocodeEmbedding.embed ports labels
          (cfg (.inr .done) (FixedTapeCompiler.Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) frame,ip,outRev⟩) :=
  NativeIOFusion.trace_stepN encoding target selected w (trace_call ops ports labels target selected frame hsel hc xs pos w ip outRev)

theorem native_page_trajectory (encoding : NativeMicrocode.Encoding U J k z)
    (ops : Fin q → PageOpcode) (ports : Port q ↪ U) (labels : Label → J)
    (target : NativeIO.Program U J) (selected : J → Bool) (frame : MicrocodeEmbedding.Frame U)
    (hsel : ∀ pc,selected (labels pc)=FusedPageClock.selected pc)
    (hc : ∀ pc,pc≠.inr .done → NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (pos : Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 2*xs.length+3) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (NativeIOFusion.machine encoding target selected) w) s
      (NativeIOFusion.denote encoding target selected
        ⟨MicrocodeEmbedding.embed ports labels (cfg (.inl .read) (FixedTapeCompiler.Counter.marked xs) pos) frame,ip,outRev⟩)).workPos
          (encoding.port (ports (some p)))=pos (some p)+(ops p).direction*((xs.take s).count true) := by
  have ha : ∀ pc,program ops pc≠.halt → program ops pc≠.reject →
      NativeIO.workProgram target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc) := by
    intro pc hh _;apply hc pc;intro he;subst pc;exact hh rfl
  have hr : ∀ pc,FusedPageClock.selected pc=true → ∀ t next,program ops pc=.read t next → ∀ x,
      NativeIO.workProgram target (labels (next x))=MicrocodeEmbedding.instruction ports labels (program ops (next x)) := by
    intro pc _ t next he x;exact hc (next x) (read_next_ne_done ops pc t next he x)
  rw [NativeIOFusionCalls.work_native_prefix encoding ports labels (program ops) target FusedPageClock.selected selected frame
    w ip outRev hsel ha hr (FusedPageClock.complete_trace ops xs pos) s hs]
  simp only [NativeIOFusion.denote,Equiv.symm_apply_apply,MicrocodeEmbedding.embed,MicrocodeEmbedding.extend_at]
  exact FusedPageClock.page_trajectory ops xs s pos p

end TransposeFollowup.FusedPageClockIO
