import TransposeFollowup.NativeIOCore

/-! Each physical work head moves by at most one cell per native
instruction. This bounds stream length from a proved output displacement,
without charging a metalevel length computation to the machine. -/
namespace TransposeFollowup.NativeHeadDisplacement
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

theorem work_step_bounds (p : Microcode.Program T L) (c : NativeMicrocode.Config T L) (t : T) :
    c.pos t-1 ≤ (NativeMicrocode.step p c).pos t ∧ (NativeMicrocode.step p c).pos t ≤ c.pos t+1 := by
  cases hp : p c.core.pc with
  | act actions next =>
    cases hm : (actions t).move <;> simp [NativeMicrocode.step,hp,hm,NativeMicrocode.direction,Transpose.Dir.shift] <;> omega
  | _ => simp [NativeMicrocode.step,hp]

theorem io_step_bounds (p : NativeIO.Program T L) (w : List Bool) (c : NativeIO.Config T L) (t : T) :
    c.work.pos t-1 ≤ (NativeIO.step p w c).work.pos t ∧
      (NativeIO.step p w c).work.pos t ≤ c.work.pos t+1 := by
  cases hp : p c.work.core.pc with
  | work i => simpa only [NativeIO.step,hp] using work_step_bounds (NativeIO.workProgram p) c.work t
  | _ => simp [NativeIO.step,hp,NativeIO.setLabel]

theorem trace_bounds (p : NativeIO.Program T L) (w : List Bool) {n : ℕ} {c d : NativeIO.Config T L}
    (h : OperationalTrace.Trace (NativeIO.step p w) (NativeIO.Active p) n c d) (t : T) :
    c.work.pos t-(n : ℤ) ≤ d.work.pos t ∧ d.work.pos t ≤ c.work.pos t+(n : ℤ) := by
  induction h with
  | refl c => simp
  | @cons n c d ha h ih =>
    have hs := io_step_bounds p w c t
    simp only [Nat.cast_add,Nat.cast_one]
    omega

end TransposeFollowup.NativeHeadDisplacement
