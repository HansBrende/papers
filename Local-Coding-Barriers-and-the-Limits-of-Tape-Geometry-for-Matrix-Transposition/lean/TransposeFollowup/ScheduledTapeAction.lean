import TransposeFollowup.ScheduledNativeIO

/-! Selected-tape actions and exact public-length rewinds. This uses the
existing native action refinement; it introduces no new tape semantics. -/
namespace TransposeFollowup.ScheduledTapeAction
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
set_option autoImplicit false
variable {T M : Type*} [DecidableEq T]

abbrev cells (c : NativeIO.Config T M) (t : T) (z : ℤ) : Sym Bool :=
  AbsoluteTape.cells (c.work.core.tapes t) (c.work.pos t) z

def action (p : T) (a : Microcode.Action) : NativeIO.Program T M :=
  fun m => .work (.act (Microcode.single p a) m)

theorem active (p : T) (a : Microcode.Action) (c : NativeIO.Config T M) :
    NativeIO.Active (action p a) c := by simp [action,NativeIO.Active]

theorem step_position (p : T) (a : Microcode.Action) (w : List Bool)
    (c : NativeIO.Config T M) (t : T) :
    (NativeIO.step (action p a) w c).work.pos t=
      if t=p then (NativeMicrocode.direction a.move).shift (c.work.pos t) else c.work.pos t := by
  by_cases h : t=p <;>
    simp [action,NativeIO.step,NativeIO.workProgram,NativeMicrocode.step,Microcode.actualStep,
      Microcode.single,h,NativeMicrocode.direction,Transpose.Dir.shift]

theorem step_cells (p : T) (a : Microcode.Action) (w : List Bool)
    (c : NativeIO.Config T M) (t : T) (z : ℤ) :
    cells (NativeIO.step (action p a) w c) t z=
      if t=p ∧ z=c.work.pos t then a.write.getD (cells c t z) else cells c t z := by
  have he := NativeMicrocode.action_cells (Microcode.single p a t)
    (c.work.core.tapes t) (c.work.pos t) z
  apply he.trans
  by_cases hp : t=p <;> by_cases hz : z=c.work.pos t <;>
    simp_all [Microcode.single,cells,AbsoluteTape.scanned]

theorem step_io (p : T) (a : Microcode.Action) (w : List Bool) (c : NativeIO.Config T M) :
    (NativeIO.step (action p a) w c).inputPos=c.inputPos ∧
    (NativeIO.step (action p a) w c).outRev=c.outRev := ⟨rfl,rfl⟩

def rewind (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) : NativeIO.Config T M :=
  trajectory (fun _ => action p ⟨none,.left⟩) w c n

theorem rewind_position (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) :
    (rewind p w c n).work.pos t=c.work.pos t-if t=p then n else 0 := by
  induction n with
  | zero => simp [rewind,trajectory]
  | succ n ih =>
    change (NativeIO.step (action p ⟨none,.left⟩) w (rewind p w c n)).work.pos t=_
    rw [step_position,ih]
    by_cases h : t=p <;> simp [h,NativeMicrocode.direction,Transpose.Dir.shift]
    omega

theorem rewind_cells (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) (z : ℤ) :
    cells (rewind p w c n) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cells (NativeIO.step (action p ⟨none,.left⟩) w (rewind p w c n)) t z=_
    simpa only [step_cells,Option.getD_none,ite_self] using ih

theorem rewind_io (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) :
    (rewind p w c n).inputPos=c.inputPos ∧ (rewind p w c n).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

def erase (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) : NativeIO.Config T M :=
  trajectory (fun _ => action p ⟨some .blank,.right⟩) w c n

theorem erase_position (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) :
    (erase p w c n).work.pos t=c.work.pos t+if t=p then n else 0 := by
  induction n with
  | zero => simp [erase,trajectory]
  | succ n ih =>
    change (NativeIO.step (action p ⟨some .blank,.right⟩) w (erase p w c n)).work.pos t=_
    rw [step_position,ih]
    by_cases h : t=p <;> simp [h,NativeMicrocode.direction,Transpose.Dir.shift]
    omega

theorem erase_cells (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) (t : T) (z : ℤ) :
    cells (erase p w c n) t z=
      if t=p ∧ c.work.pos t ≤ z ∧ z<c.work.pos t+n then .blank else cells c t z := by
  induction n with
  | zero => simp [erase,trajectory]
  | succ n ih =>
    change cells (NativeIO.step (action p ⟨some .blank,.right⟩) w (erase p w c n)) t z=_
    rw [step_cells,erase_position,ih]
    by_cases hp : t=p
    · simp only [hp,ite_true,true_and,Option.getD_some]
      split_ifs <;> try rfl
      all_goals omega
    · simp [hp]

theorem erase_io (p : T) (w : List Bool) (c : NativeIO.Config T M) (n : ℕ) :
    (erase p w c n).inputPos=c.inputPos ∧ (erase p w c n).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

end TransposeFollowup.ScheduledTapeAction
