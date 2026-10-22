import TransposeFollowup.RawRowArithmeticRun

/-! Endpoint positions for arbitrary work states. These facts use the
actual cell/seek semantics and do not assume valid arithmetic payloads. -/
namespace TransposeFollowup.CoupledRowMotion
open FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (Mode State)
set_option autoImplicit false

theorem right_position {C : Type} (select : Fin 2 → Bool) (w : List Bool) (c : State C)
    (n : ℕ) (t : Fin 2) :
    (trajectory (fun _ => CoupledRowMoves.right select) w c n).work.pos t=
      c.work.pos t+if select t then (n : ℤ) else 0 := by
  have hs (d : State C) : (NativeIO.step (CoupledRowMoves.right select) w d).work.pos t=
      d.work.pos t+if select t then 1 else 0 := by
    cases h : select t <;> simp [CoupledRowMoves.right,NativeIO.step,NativeIO.workProgram,
      NativeMicrocode.step,NativeMicrocode.direction,Transpose.Dir.shift,h]
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory,hs,ih]
    cases select t <;> simp [Nat.cast_add,add_assoc]

theorem scan_position {C : Type} (f : Mode C → Mode C) (W : ℕ) (w : List Bool) (c : State C) (t : Fin 2) :
    (trajectory (CoupledRowScan.schedule f W) w c (4*W)).work.pos t=c.work.pos t-W := by
  rw [CoupledRowScan.schedule_exact]
  induction W with
  | zero => simp [CoupledRowScan.run]
  | succ W ih =>
    change ((CoupledRowCell.result f)^[W+1] c).work.pos t=_
    rw [Function.iterate_succ_apply',CoupledRowCell.cell_positions]
    change (CoupledRowScan.run f W c).work.pos t-1=_
    rw [ih]
    push_cast
    ring

theorem update_endpoint {C : Type} (f : Mode C → Mode C) (carry : C)
    (W : ℕ) (w : List Bool) (c : State C) (t : Fin 2) :
    (trajectory (RawRowArithmetic.scheduleWithUpdate f carry W) w c (RawRowArithmetic.ticks W)).work.pos t=
      c.work.pos t+if RawRowArithmetic.bankOnly t then (W : ℤ) else 0 := by
  simp only [RawRowArithmetic.scheduleWithUpdate,RawRowArithmetic.ticks,
    append_exact,CoupledRowScan.idle_exact]
  rw [right_position,scan_position,right_position]
  change (c.work.pos t+(if true then (W : ℤ) else 0)-W)+
    (if RawRowArithmetic.bankOnly t then (W : ℤ) else 0)=_
  simp

theorem arithmetic_endpoint (sub : Bool) (W : ℕ) (w : List Bool) (c : State) (t : Fin 2) :
    (trajectory (RawRowArithmetic.schedule sub W) w c (RawRowArithmetic.ticks W)).work.pos t=
      c.work.pos t+if RawRowArithmetic.bankOnly t then (W : ℤ) else 0 :=
  update_endpoint (RawRowArithmetic.update sub) sub W w c t

end TransposeFollowup.CoupledRowMotion
