import TransposeFollowup.RawMaskedStrideWord
import TransposeFollowup.MaskedStrideWordMotion
import TransposeFollowup.RawBankProgramMotion
import Transpose.Tape.MStarTM

/-! The actual whole-word native head paths, including raw IO, every
stage/reset, and the frozen halted tail. Internal stage excursions are
added at their paid public start times. -/
namespace TransposeFollowup.RawMaskedStrideWord
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideWord (Operation Valid)
open MaskedStrideCell (State)
set_option autoImplicit false

def motion (P : ℕ) (ops : List Operation) (hv : Valid P ops) : RawBankProgram.Motion (body P ops) where
  path := MaskedStrideWord.path P ops
  position := MaskedStrideWord.schedule_position P ops hv
  after := MaskedStrideWord.path_after P ops hv

def path (P : ℕ) (ops : List Operation) (t : Fin 2) (n : ℕ) : ℤ :=
  MaskedStrideWord.path P ops t (n-4*P)+
    if t=0 then ((min ((n+1)/3) P : ℕ) : ℤ)-(min (n-3*P) P : ℕ)+
      (min ((n-(4*P+MaskedStrideWord.ticks P ops))/3) P : ℕ) else 0

theorem schedule_position (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (c : State) (n : ℕ) (hn : n ≤ ticks P ops) (t : Fin 2) :
    (trajectory (schedule P ops) w c n).work.pos t = c.work.pos t+path P ops t n :=
  RawBankProgram.schedule_position P (body P ops) (motion P ops hv) w c n hn t

theorem path_after (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2)
    (n : ℕ) (hn : ticks P ops ≤ n) : path P ops t n = if t=0 then (P : ℤ) else 0 :=
  RawBankProgram.path_after P (body P ops) (motion P ops hv) t n hn

theorem path_frozen (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2) (n : ℕ) :
    path P ops t (min n (ticks P ops)) = path P ops t n :=
  RawBankProgram.path_frozen P (body P ops) (motion P ops hv) t n

theorem workTraj_position (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (n : ℕ) (t : Fin 2) :
    Transpose.Tape.workTraj (machine P ops) w n ((encoding P ops).port t) = path P ops t n :=
  RawBankProgram.workTraj_position P (body P ops) (motion P ops hv) (body_correct P ops hv) w n t

end TransposeFollowup.RawMaskedStrideWord
