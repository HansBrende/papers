import TransposeFollowup.BufferedRowBankMotion
import TransposeFollowup.CoupledRowScanInvariant

/-! The generic buffered executor preserves bank cells outside its window,
even on arbitrary, unprepared configurations. This permits nesting it as
an entry-buffer routine inside the existing independent-row scheduler. -/
namespace TransposeFollowup.BufferedRows
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CoupledRowCell (Mode State)
open RawRowArithmetic (ticks bankOnly)
set_option autoImplicit false
variable {C : Type} (u : Rule C)

theorem step_frame (W : ℕ) (w : List Bool) (c : State C) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+W ≤ z) :
    cells (trajectory (schedule u W) w c (ticks W)) 0 z=cells c 0 z := by
  simp only [schedule,RawRowArithmetic.scheduleWithUpdate,ticks,append_exact,CoupledRowScan.idle_exact]
  rw [CoupledRowMoves.right_cells,CoupledRowScan.schedule_exact]
  rw [CoupledRowScan.run_frame u.table W _ 0 z (by
    rw [CoupledRowMotion.right_position]
    change z<c.work.pos 0+(W : ℤ)-W ∨ c.work.pos 0+W ≤ z
    omega)]
  rw [CoupledRowMoves.right_cells]
  rfl

theorem rows_frame (W r : ℕ) (w : List Bool) (c : State C) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+(r*W : ℕ) ≤ z) :
    cells (trajectory (rowsSchedule u W r) w c (r*ticks W)) 0 z=cells c 0 z := by
  induction r generalizing c with
  | zero => simp only [Nat.zero_mul,trajectory]
  | succ r ih =>
    rw [show (r+1)*ticks W=ticks W+r*ticks W by ring]
    change cells (trajectory (append (schedule u W) (rowsSchedule u W r) (ticks W)) w c _) 0 z=_
    rw [append_exact]
    have he := CoupledRowMotion.update_endpoint u.table u.carry W w c 0
    change (trajectory (schedule u W) w c (ticks W)).work.pos 0=c.work.pos 0+(W : ℤ) at he
    rw [ih _ (by rw [he]; simp only [Nat.succ_mul,Nat.cast_add] at hz; omega)]
    exact step_frame u W w c z (by simp only [Nat.succ_mul,Nat.cast_add] at hz; omega)

theorem bank_frame (W r : ℕ) (w : List Bool) (c : State C) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+(r*W : ℕ) ≤ z) :
    cells (bankRun u W r w c) 0 z=cells c 0 z := by
  rw [bankRun,ScheduledBankCleanup.run_cells]
  simp only [show (0 : Fin 2)≠1 by decide,false_and,ite_false]
  exact rows_frame u W r w c z hz

end TransposeFollowup.BufferedRows
