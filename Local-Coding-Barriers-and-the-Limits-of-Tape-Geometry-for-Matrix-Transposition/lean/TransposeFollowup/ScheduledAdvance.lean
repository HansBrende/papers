import TransposeFollowup.ScheduledTapeAction

/-! Exact public-length rightward seeks, without changing tape contents.
These reuse the native single-action refinement, alongside the existing
leftward rewind interface. -/
namespace TransposeFollowup.ScheduledTapeAction
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false
variable {T M : Type*} [DecidableEq T]

def advance (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) : NativeIO.Config T M :=
  trajectory (fun _ => action p ⟨none,.right⟩) w c n

theorem advance_position (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) :
    (advance p w c n).work.pos t=c.work.pos t+if t=p then n else 0 := by
  induction n with
  | zero => simp [advance,trajectory]
  | succ n ih =>
    change (NativeIO.step (action p ⟨none,.right⟩) w (advance p w c n)).work.pos t=_
    rw [step_position,ih]
    by_cases h : t=p <;> simp [h,NativeMicrocode.direction,Transpose.Dir.shift]
    omega

theorem advance_cells (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) (z : ℤ) :
    cells (advance p w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cells (NativeIO.step (action p ⟨none,.right⟩) w (advance p w c n)) t z=_
    simpa only [step_cells,Option.getD_none,ite_self] using ih

theorem advance_io (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) :
    (advance p w c n).inputPos=c.inputPos ∧ (advance p w c n).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

end TransposeFollowup.ScheduledTapeAction
