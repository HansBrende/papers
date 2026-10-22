import TransposeFollowup.CoupledRowMotion
import TransposeFollowup.ScheduledTapeAction

/-! Frame and scratch facts for the existing paid paired scan. These
hold for any retained carry type; the original Boolean scan is included. -/
namespace TransposeFollowup.CoupledRowCell
open FixedTapeCompiler ScheduledTapeAction
set_option autoImplicit false
variable {C : Type}

theorem result_frame (f : Mode C → Mode C) (c : State C) (t : Fin 2) (z : ℤ)
    (hz : z≠c.work.pos t-1) : cells (result f c) t z=cells c t z := by
  simp only [result,cells,AbsoluteTape.write_cells,ite_eq_right hz]
  exact AbsoluteTape.move_cells .left (c.work.core.tapes t) (c.work.pos t) z

theorem result_scratch (f : Mode C → Mode C) (hf : ∀ m, (f m).2.2=m.2.2)
    (c : State C) (z : ℤ) : cells (result f c) 1 z=cells c 1 z := by
  simp only [result,cells,show (1 : Fin 2)≠0 by decide,ite_false,hf,Turing.Tape.write_self]
  exact AbsoluteTape.move_cells .left (c.work.core.tapes 1) (c.work.pos 1) z

end TransposeFollowup.CoupledRowCell

namespace TransposeFollowup.CoupledRowScan
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CoupledRowCell (Mode State)
set_option autoImplicit false
variable {C : Type}

theorem run_position (f : Mode C → Mode C) (n : ℕ) (c : State C) (t : Fin 2) :
    (run f n c).work.pos t=c.work.pos t-n := by
  rw [← schedule_exact f n [] c]
  exact CoupledRowMotion.scan_position f n [] c t

theorem run_frame (f : Mode C → Mode C) (n : ℕ) (c : State C) (t : Fin 2) (z : ℤ)
    (hz : z<c.work.pos t-n ∨ c.work.pos t ≤ z) : cells (run f n c) t z=cells c t z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    change cells (CoupledRowCell.result f (run f n c)) t z=_
    rw [CoupledRowCell.result_frame f _ t z (by rw [run_position]; push_cast at hz; omega)]
    apply ih
    push_cast at hz
    omega

theorem run_scratch (f : Mode C → Mode C) (hf : ∀ m, (f m).2.2=m.2.2)
    (n : ℕ) (c : State C) (z : ℤ) : cells (run f n c) 1 z=cells c 1 z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    exact (CoupledRowCell.result_scratch f hf (run f n c) z).trans ih

theorem run_io (f : Mode C → Mode C) (n : ℕ) (c : State C) :
    (run f n c).inputPos=c.inputPos ∧ (run f n c).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [run,Function.iterate_succ_apply']
    exact ih

end TransposeFollowup.CoupledRowScan

namespace TransposeFollowup.CoupledRowMoves
open FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CoupledRowCell (Mode State)
set_option autoImplicit false
variable {C : Type}

theorem right_cells (select : Fin 2 → Bool) (w : List Bool) (c : State C)
    (n : ℕ) (t : Fin 2) (z : ℤ) :
    cells (trajectory (fun _ => right select) w c n) t z=cells c t z := by
  have hs (d : State C) : cells (NativeIO.step (right select) w d) t z=cells d t z := by
    have h := NativeMicrocode.action_cells (⟨none,if select t then .right else .stay⟩ : Microcode.Action)
      (d.work.core.tapes t) (d.work.pos t) z
    apply h.trans
    simp only [Option.getD_none]
    split_ifs with hz
    · subst z
      exact (AbsoluteTape.scanned (d.work.core.tapes t) (d.work.pos t)).symm
    · rfl
  induction n with
  | zero => rfl
  | succ n ih => rw [trajectory,hs,ih]

theorem right_io (select : Fin 2 → Bool) (w : List Bool) (c : State C) (n : ℕ) :
    (trajectory (fun _ => right select) w c n).inputPos=c.inputPos ∧
      (trajectory (fun _ => right select) w c n).outRev=c.outRev := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih

end TransposeFollowup.CoupledRowMoves
