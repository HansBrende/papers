import TransposeFollowup.PaddedWorkSchedule

/-! Head motion for arbitrary scheduled native IO. The work-step bound is
shared with the padded work interpreter; external IO leaves work heads fixed. -/
namespace TransposeFollowup.ScheduledNativeIO
open FixedTapeCompiler
set_option autoImplicit false
variable {T M : Type*}

theorem io_step_displacement (p : NativeIO.Program T M) (w : List Bool)
    (c : NativeIO.Config T M) (t : T) :
    |(NativeIO.step p w c).work.pos t-c.work.pos t|≤1 := by
  cases hp : p c.work.core.pc with
  | work i =>
    simpa only [NativeIO.step,hp] using
      PaddedWorkSchedule.step_displacement (NativeIO.workProgram p) c.work t
  | _ => simp [NativeIO.step,hp,NativeIO.setLabel]

theorem trajectory_displacement (σ : ℕ → NativeIO.Program T M) (w : List Bool)
    (c : NativeIO.Config T M) (n : ℕ) (t : T) :
    |(trajectory σ w c n).work.pos t-c.work.pos t|≤n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    have hs := io_step_displacement (σ n) w (trajectory σ w c n) t
    rw [abs_le] at ih hs ⊢
    simp only [trajectory,Nat.cast_add,Nat.cast_one]
    constructor <;> omega

end TransposeFollowup.ScheduledNativeIO
