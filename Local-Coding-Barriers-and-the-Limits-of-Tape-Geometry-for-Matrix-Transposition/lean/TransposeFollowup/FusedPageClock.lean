import TransposeFollowup.NativeReadFusionCore
import TransposeFollowup.ReusablePageClockTrajectory

/-! Select only the forward clock read and the rewind read for native
read/action fusion. The stored clock word, tapes, and finite source program
are unchanged. No clock preparation or opcode-fetch cost is supplied here. -/
namespace TransposeFollowup.FusedPageClock
open FixedTapeCompiler CopyMachine
open ReusablePageClock (Port Label program cfg frame identityBinding clockBinding)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

def selected : Label → Bool
  | .inl .read | .inr .back => true
  | _ => false
abbrev step (ops : Fin q → PageOpcode) := NativeReadFusion.step (program ops) selected
abbrev Active (ops : Fin q → PageOpcode) := NativeReadFusion.Active (program ops) selected
abbrev Trace (ops : Fin q → PageOpcode) := OperationalTrace.Trace (step ops) (Active ops)
abbrev run (ops : Fin q → PageOpcode) := NativeReadFusion.run (program ops) selected

theorem forward_step (ops : Fin q → PageOpcode) (b : Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    step ops (cfg (.inl .read) ⟨pre,.data b::post⟩ pos) =
      cfg (.inl .read) ⟨.data b::pre,post⟩ (PageClock.advance ops pos 1 (if b then 1 else 0)) := by
  have ht:=MicrocodeEmbedding.trace_embed (identityBinding q).ports Sum.inl (PageClock.program ops) (program ops)
    (frame ⟨pre,.data b::post⟩ pos) (ReusablePageClock.scan_code ops) (PageClock.two_trace ops b pre post pos)
  have he:=OperationalTrace.trace_run ht
  simp only [ReusablePageClock.embed_scan] at he
  have hf : step ops (cfg (.inl .read) ⟨pre,.data b::post⟩ pos) =
      NativeMicrocode.step (program ops) (NativeMicrocode.step (program ops) (cfg (.inl .read) ⟨pre,.data b::post⟩ pos)) := by
    apply NativeReadFusion.step_read_act _ _ _ _ _
      ((identityBinding q).values (PageClock.actions ops b) (fun _ => MicrocodeEmbedding.idle)) (.inl .read) rfl rfl
    simp [cfg,PageClock.bank,CopyMachine.denote_read,Tape.read,program,PageClock.program,FinitePortBinding.instruction,identityBinding]
  exact hf.trans he

theorem forward_trace (ops : Fin q → PageOpcode) (b : Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 1 (cfg (.inl .read) ⟨pre,.data b::post⟩ pos)
      (cfg (.inl .read) ⟨.data b::pre,post⟩ (PageClock.advance ops pos 1 (if b then 1 else 0))) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeReadFusion.active_iff _ _ _).mpr
    simp [NativeMicrocode.Active,cfg,program,PageClock.program,FinitePortBinding.instruction,identityBinding]
  · rw [forward_step];exact .refl _

theorem stop_step (ops : Fin q → PageOpcode) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    step ops (cfg (.inl .read) ⟨pre,.stop::post⟩ pos) = cfg (.inr .back) ⟨pre,.stop::post⟩ pos := by
  have hf : step ops (cfg (.inl .read) ⟨pre,.stop::post⟩ pos) =
      NativeMicrocode.step (program ops) (NativeMicrocode.step (program ops) (cfg (.inl .read) ⟨pre,.stop::post⟩ pos)) := by
    apply NativeReadFusion.step_read_jump _ _ _ _ _ (.inr .back) rfl rfl
    simp [cfg,PageClock.bank,CopyMachine.denote_read,Tape.read,program,identityBinding]
  rw [hf]
  simp [NativeMicrocode.step,Microcode.actualStep,cfg,program,PageClock.program,
    FinitePortBinding.instruction,PageClock.bank,CopyMachine.denote_read,Tape.read,identityBinding]

theorem stop_trace (ops : Fin q → PageOpcode) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 1 (cfg (.inl .read) ⟨pre,.stop::post⟩ pos) (cfg (.inr .back) ⟨pre,.stop::post⟩ pos) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeReadFusion.active_iff _ _ _).mpr
    simp [NativeMicrocode.Active,cfg,program,PageClock.program,FinitePortBinding.instruction,identityBinding]
  · rw [stop_step];exact .refl _

end TransposeFollowup.FusedPageClock
