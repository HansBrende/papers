import TransposeFollowup.NativeIOFusionCore

namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
open NativeIO (Program Config workProgram)
open NativeMicrocode (Encoding)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem step_some_of_active (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (c : Config T L) (ha : Active p selected c) :
    Transpose.step (machine e p selected) w (denote e p selected c)=some (denote e p selected (step p selected w c)) := by
  cases hs : Transpose.step (machine e p selected) w (denote e p selected c) with
  | none => exact False.elim ((step_none_iff e p selected w c).mp hs ha)
  | some d =>
    have hd : d=denote e p selected (step p selected w c) := by
      simpa [NativeMicrocode.totalStep,hs] using step_denote_core e p selected w c
    exact congrArg some hd

theorem run_denote_core (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (n : ℕ) (c : Config T L) :
    OperationalTrace.run (NativeMicrocode.totalStep (machine e p selected) w) n (denote e p selected c)=
      denote e p selected (run p selected w n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [OperationalTrace.run,step_denote_core] using ih (step p selected w c)

theorem trace_stepN (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) {n : ℕ} {c d : Config T L}
    (h : OperationalTrace.Trace (step p selected w) (Active p selected) n c d) :
    Transpose.stepN (machine e p selected) w n (denote e p selected c)=some (denote e p selected d) := by
  induction h with
  | refl c => rfl
  | cons ha tr ih => rw [Transpose.stepN,step_some_of_active e p selected w _ ha];exact ih

theorem work_step (p : Program T L) (selected : L → Bool) (w : List Bool) (c : NativeMicrocode.Config T L)
    (ha : NativeReadFusion.Active (workProgram p) selected c) (inputPos : ℤ) (outRev : List Bool) :
    step p selected w ⟨c,inputPos,outRev⟩=⟨NativeReadFusion.step (workProgram p) selected c,inputPos,outRev⟩ ∧
      Active p selected ⟨c,inputPos,outRev⟩ := by
  cases hp : p c.core.pc with
  | work i => exact ⟨by simp [step,hp],by simpa only [Active,hp] using ha⟩
  | _ => rw [NativeReadFusion.active_iff] at ha;simp [NativeMicrocode.Active,workProgram,hp] at ha

theorem lift_work_trace (p : Program T L) (selected : L → Bool) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    {n : ℕ} {c d : NativeMicrocode.Config T L}
    (h : OperationalTrace.Trace (NativeReadFusion.step (workProgram p) selected) (NativeReadFusion.Active (workProgram p) selected) n c d) :
    OperationalTrace.Trace (step p selected w) (Active p selected) n ⟨c,ip,outRev⟩ ⟨d,ip,outRev⟩ := by
  induction h with
  | refl c => exact .refl _
  | cons ha tr ih =>
    apply OperationalTrace.Trace.cons (work_step p selected w _ ha ip outRev).2
    rw [(work_step p selected w _ ha ip outRev).1]
    exact ih

theorem blank_denote (e : Encoding T L k q) (p : Program T L) (selected : L → Bool) (start : L) (hs : e.label start=0) :
    denote e p selected (⟨NativeMicrocode.blankConfig start,0,[]⟩ : Config T L)=Transpose.init (machine e p selected) := by
  unfold denote NativeMicrocode.blankConfig Transpose.init
  rw [hs]
  congr 1
  funext i z
  rw [AbsoluteTape.blank_cells]
  rfl


end TransposeFollowup.NativeIOFusion
