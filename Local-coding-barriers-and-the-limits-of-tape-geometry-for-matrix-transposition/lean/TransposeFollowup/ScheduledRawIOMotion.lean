import TransposeFollowup.ScheduledRawOutput

/-! Intermediate raw-IO head positions. Loading moves on the second tick
of each three-tick cell; output moves on the third tick. -/
namespace TransposeFollowup.ScheduledRawInput
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

theorem cell_prefix_position (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ 3) (t : Fin 2) :
    (trajectory cellSchedule w c n).work.pos t=c.work.pos t+if t=0 then (n+1)/3 else 0 := by
  interval_cases n <;> fin_cases t <;>
    simp [trajectory,cellSchedule,NativeIO.step,NativeIO.setLabel,action,NativeIO.workProgram,
      NativeMicrocode.step,Microcode.actualStep,Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]

theorem schedule_position (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) :
    (trajectory schedule w c n).work.pos t=c.work.pos t+if t=0 then (n+1)/3 else 0 := by
  have he : n=3*(n/3)+n%3 := by omega
  conv_lhs => rw [he,trajectory_add,schedule_exact]
  rw [trajectory_congr (fun i => schedule (3*(n/3)+i)) cellSchedule w _ (n%3) (by
    intro i hi; simp only [schedule,show (3*(n/3)+i)%3=i by omega]),
    cell_prefix_position w _ _ (by omega),loaded_position]
  by_cases ht : t=0 <;> simp only [ht,ite_true,ite_false]
  · have hq : n/3+(n%3+1)/3=(n+1)/3 := by omega
    rw [add_assoc,← Nat.cast_add,hq]
  · omega

end TransposeFollowup.ScheduledRawInput

namespace TransposeFollowup.ScheduledRawOutput
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (State)
set_option autoImplicit false

theorem cell_prefix_position (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ 3) (t : Fin 2) :
    (trajectory cellSchedule w c n).work.pos t=c.work.pos t+if t=0 then n/3 else 0 := by
  interval_cases n <;> fin_cases t <;>
    simp [trajectory,cellSchedule,NativeIO.step,NativeIO.setLabel,action,NativeIO.workProgram,
      NativeMicrocode.step,Microcode.actualStep,Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]

theorem schedule_position (w : List Bool) (c : State) (n : ℕ) (t : Fin 2) :
    (trajectory schedule w c n).work.pos t=c.work.pos t+if t=0 then n/3 else 0 := by
  have he : n=3*(n/3)+n%3 := by omega
  conv_lhs => rw [he,trajectory_add,schedule_exact]
  rw [trajectory_congr (fun i => schedule (3*(n/3)+i)) cellSchedule w _ (n%3) (by
    intro i hi; simp only [schedule,show (3*(n/3)+i)%3=i by omega]),
    cell_prefix_position w _ _ (by omega),emitted_position]
  have hm : n%3/3=0 := by omega
  simp [hm]

end TransposeFollowup.ScheduledRawOutput
