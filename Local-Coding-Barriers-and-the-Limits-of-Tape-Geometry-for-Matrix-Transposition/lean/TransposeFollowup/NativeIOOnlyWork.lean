import TransposeFollowup.NativeIOFusionRunCore

/-! Reuse an IO-language routine consisting entirely of work instructions
through the existing selected-fusion work compiler. No IO step is dropped. -/
namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

def OnlyWork (p : NativeIO.Program T L) : Prop := ∀ pc,∃ i,p pc=.work i

theorem only_work_step (p : NativeIO.Program T L) (hp : OnlyWork p) (selected : L → Bool)
    (w : List Bool) (c : NativeIO.Config T L) :
    step p selected w c=⟨NativeReadFusion.step (NativeIO.workProgram p) selected c.work,c.inputPos,c.outRev⟩ := by
  obtain ⟨i,hi⟩:=hp c.work.core.pc
  simp [step,hi]

theorem only_work_active (p : NativeIO.Program T L) (hp : OnlyWork p) (selected : L → Bool)
    (c : NativeIO.Config T L) : Active p selected c ↔ NativeReadFusion.Active (NativeIO.workProgram p) selected c.work := by
  obtain ⟨i,hi⟩:=hp c.work.core.pc
  simp only [Active,hi]

theorem only_work_trace (p : NativeIO.Program T L) (hp : OnlyWork p) (selected : L → Bool) (w : List Bool)
    {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (step p selected w) (Active p selected) n c d) :
    OperationalTrace.Trace (NativeReadFusion.step (NativeIO.workProgram p) selected)
      (NativeReadFusion.Active (NativeIO.workProgram p) selected) n c.work d.work := by
  induction h with
  | refl c => exact .refl _
  | cons ha tr ih =>
    apply OperationalTrace.Trace.cons ((only_work_active p hp selected _).mp ha)
    simpa only [only_work_step p hp selected w] using ih

theorem only_work_run (p : NativeIO.Program T L) (hp : OnlyWork p) (selected : L → Bool)
    (w : List Bool) (n : ℕ) (c : NativeIO.Config T L) :
    run p selected w n c=⟨NativeReadFusion.run (NativeIO.workProgram p) selected n c.work,c.inputPos,c.outRev⟩ := by
  induction n generalizing c with
  | zero => cases c;rfl
  | succ n ih =>
    simpa only [run,OperationalTrace.run,only_work_step p hp selected w] using ih (step p selected w c)

end TransposeFollowup.NativeIOFusion
