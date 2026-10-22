import TransposeFollowup.BufferedRowRows
import TransposeFollowup.CoupledRowMotion
import TransposeFollowup.RepeatedScheduleMotion

/-! The actual repeated-row schedule stays within8W cells of a scan at
speed1/7 on the bank and a stationary buffer, uniformly over all data. -/
namespace TransposeFollowup.BufferedRows
open FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (State)
open RawRowArithmetic (ticks ticks_eq bankOnly)
set_option autoImplicit false
variable {C : Type}

theorem rows_endpoint (u : Rule C) (W r : ℕ) (w : List Bool) (c : State C) (t : Fin 2) :
    (trajectory (rowsSchedule u W r) w c (r*ticks W)).work.pos t=
      c.work.pos t+if bankOnly t then (r*W : ℕ) else 0 := by
  have h := repeat_endpoint (schedule u W) CoupledRowScan.idle (ticks W) w t
    (if bankOnly t then (W : ℤ) else 0) (fun d => CoupledRowMotion.update_endpoint u.table u.carry W w d t) r c
  cases hb : bankOnly t <;> simpa [rowsSchedule,repeatSchedule,hb] using h

theorem rows_linear_error (u : Rule C) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State C) (n : ℕ) (hn : n≤r*ticks W) (t : Fin 2) :
    |((trajectory (rowsSchedule u W r) w c n).work.pos t : ℝ)-c.work.pos t-
      (if bankOnly t then (n : ℝ)/7 else 0)|≤8*W := by
  have hN : 0<ticks W := by unfold ticks; omega
  have h := repeat_linear_error (schedule u W) CoupledRowScan.idle (ticks W) hN w t
    (if bankOnly t then (W : ℤ) else 0) (fun d => CoupledRowMotion.update_endpoint u.table u.carry W w d t)
    r c n hn
  have he : (n : ℝ)/(ticks W)*W=(n : ℝ)/7 := by
    rw [ticks_eq W hW]
    push_cast
    field_simp [show (W : ℝ)≠0 by positivity]
  cases hb : bankOnly t with
  | false =>
    simp [hb] at h ⊢
    change |((trajectory (rowsSchedule u W r) w c n).work.pos t : ℝ)-c.work.pos t|≤ticks W at h
    rw [ticks_eq W hW] at h
    push_cast at h
    nlinarith [Nat.cast_nonneg (α:=ℝ) W]
  | true =>
    simp [hb,he] at h ⊢
    change |((trajectory (rowsSchedule u W r) w c n).work.pos t : ℝ)-c.work.pos t-(n : ℝ)/7|≤ticks W+(W : ℝ) at h
    rw [ticks_eq W hW] at h
    push_cast at h
    linarith

end TransposeFollowup.BufferedRows
