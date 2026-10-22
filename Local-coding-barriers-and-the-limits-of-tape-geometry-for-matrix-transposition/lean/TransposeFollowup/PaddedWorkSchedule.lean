import TransposeFollowup.ScheduledNativeIO
import TransposeFollowup.NativeZipper
import TransposeFollowup.TracePrefix

/-! Execute a checked work routine for a fixed public budget. Halt/reject
states become actual stationary jump instructions, each charged one native
transition. Their work-state semantics remains the existing frozen run. -/
namespace TransposeFollowup.PaddedWorkSchedule
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false
variable {T L : Type*}

def code (p : Microcode.Program T L) : NativeIO.Program T L := fun pc =>
  .work (match p pc with | .halt | .reject => .jump pc | i => i)

theorem active (p : Microcode.Program T L) (c : NativeIO.Config T L) : NativeIO.Active (code p) c := by
  cases hp : p c.work.core.pc <;> simp [NativeIO.Active,code,hp]

theorem step_eq (p : Microcode.Program T L) (w : List Bool) (c : NativeIO.Config T L) :
    NativeIO.step (code p) w c=⟨NativeMicrocode.step p c.work,c.inputPos,c.outRev⟩ := by
  cases hp : p c.work.core.pc <;>
    simp [NativeIO.step,code,NativeIO.workProgram,NativeMicrocode.step,Microcode.actualStep,hp]

theorem trajectory_eq (p : Microcode.Program T L) (w : List Bool) (c : NativeIO.Config T L) (n : ℕ) :
    trajectory (fun _ => code p) w c n=⟨NativeMicrocode.run p n c.work,c.inputPos,c.outRev⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [trajectory,ih,step_eq]
    have hr := OperationalTrace.run_add (NativeMicrocode.step p) n 1 c.work
    simpa only [NativeMicrocode.run,OperationalTrace.run] using
      congrArg (fun z => (⟨z,c.inputPos,c.outRev⟩ : NativeIO.Config T L)) hr.symm

theorem trajectory_of_trace (p : Microcode.Program T L) (w : List Bool)
    (c d : NativeMicrocode.Config T L) (ip : ℤ) (out : List Bool) {n N : ℕ} (hn : n≤N)
    (htr : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d)
    (hd : ¬NativeMicrocode.Active p d) :
    trajectory (fun _ => code p) w ⟨c,ip,out⟩ N=⟨d,ip,out⟩ := by
  rw [trajectory_eq]
  have hr : NativeMicrocode.run p N c=d := by
    rw [show N=n+(N-n) by omega,NativeMicrocode.run,OperationalTrace.run_add,
      OperationalTrace.trace_run htr]
    exact OperationalTrace.run_fixed _ d (NativeMicrocode.inactive_fixed p d hd) _
  rw [hr]

theorem step_displacement (p : Microcode.Program T L) (c : NativeMicrocode.Config T L) (t : T) :
    |(NativeMicrocode.step p c).pos t-c.pos t|≤1 := by
  cases hp : p c.core.pc with
  | act acts next =>
    cases hm : (acts t).move <;> simp [NativeMicrocode.step,hp,hm,NativeMicrocode.direction,Transpose.Dir.shift]
  | _ => simp [NativeMicrocode.step,hp]

theorem run_displacement (p : Microcode.Program T L) (c : NativeMicrocode.Config T L) (n : ℕ) (t : T) :
    |(NativeMicrocode.run p n c).pos t-c.pos t|≤n := by
  induction n generalizing c with
  | zero => simp [NativeMicrocode.run,OperationalTrace.run]
  | succ n ih =>
    have ha := ih (NativeMicrocode.step p c)
    have hb := step_displacement p c t
    change |(NativeMicrocode.run p n (NativeMicrocode.step p c)).pos t-c.pos t|≤(n+1 : ℕ)
    rw [abs_le] at ha hb ⊢
    constructor <;> push_cast <;> omega

theorem trajectory_displacement (p : Microcode.Program T L) (w : List Bool)
    (c : NativeIO.Config T L) (n : ℕ) (t : T) :
    |(trajectory (fun _ => code p) w c n).work.pos t-c.work.pos t|≤n := by
  rw [trajectory_eq]
  exact run_displacement p c.work n t

end TransposeFollowup.PaddedWorkSchedule
