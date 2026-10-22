import TransposeFollowup.RawRowArithmeticRows
import TransposeFollowup.CoupledRowMotion
import TransposeFollowup.RepeatedScheduleMotion
import TransposeFollowup.BufferedRowLoopMotion

/-! The actual repeated-row schedule stays within8W cells of a scan at
speed1/7 on the bank and a stationary buffer, uniformly over all data. -/
namespace TransposeFollowup.RawRowArithmetic
open FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (State)
set_option autoImplicit false

theorem rows_endpoint (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) (t : Fin 2) :
    (trajectory (rowsSchedule sub W r) w c (r*ticks W)).work.pos t=
      c.work.pos t+if bankOnly t then (r*W : ℕ) else 0 :=
  BufferedRows.rows_endpoint (rule sub) W r w c t

theorem rows_linear_error (sub : Bool) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State) (n : ℕ) (hn : n≤r*ticks W) (t : Fin 2) :
    |((trajectory (rowsSchedule sub W r) w c n).work.pos t : ℝ)-c.work.pos t-
      (if bankOnly t then (n : ℝ)/7 else 0)|≤8*W :=
  BufferedRows.rows_linear_error (rule sub) W r hW w c n hn t

end TransposeFollowup.RawRowArithmetic
