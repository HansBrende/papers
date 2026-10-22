import TransposeFollowup.MixedBinaryWord
import TransposeFollowup.BackwardStrideMotion
import TransposeFollowup.BankRotationMotion

/-! Complete mixed-word head paths. Every concrete operation supplies its
proved paid path; the shared composition theorem handles arbitrary words. -/
namespace TransposeFollowup.BinaryBankOperation
open Classical ScheduledNativeIO
open MaskedStrideCell (State)
set_option autoImplicit false

def path (P : ℕ) : Operation → Fin 2 → ℕ → ℤ
  | .forward _ _ S => MaskedStrideBankStage.path P S
  | .backward _ _ S => BackwardMaskedStride.path P S
  | .reverse => BankReversal.path P
  | .rotate R => BankRotation.path P R

theorem schedule_position (P : ℕ) (op : Operation) (hv : Valid P op) (w : List Bool) (c : State)
    (n : ℕ) (hn : n≤ticks P op) (t : Fin 2) :
    (trajectory (schedule P op) w c n).work.pos t=c.work.pos t+path P op t n := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.schedule_position pre mask P hv.1 w c n hn t
  | backward pre mask S => exact BackwardMaskedStride.schedule_position pre mask P hv.1 w c n hn t
  | reverse => exact BankReversal.schedule_position P w c n hn t
  | rotate R => exact BankRotation.schedule_position P R w c n hn t

theorem path_zero (P : ℕ) (op : Operation) (hv : Valid P op) (t : Fin 2) : path P op t 0=0 := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.path_zero P hv.1 t
  | backward pre mask S => exact BackwardMaskedStride.path_zero P hv.1 t
  | reverse => exact BankReversal.path_zero P t
  | rotate R => exact BankRotation.path_zero P R t

theorem path_after (P : ℕ) (op : Operation) (hv : Valid P op) (t : Fin 2) (n : ℕ) (hn : ticks P op≤n) :
    path P op t n=0 := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.path_after P hv.1 t n hn
  | backward pre mask S => exact BackwardMaskedStride.path_after P hv.1 t n hn
  | reverse => exact BankReversal.path_after P t n hn
  | rotate R => exact BankRotation.path_after P R t n hn

theorem path_frozen (P : ℕ) (op : Operation) (hv : Valid P op) (t : Fin 2) (n : ℕ) :
    path P op t (min n (ticks P op))=path P op t n := by
  cases op with
  | forward pre mask S => exact MaskedStrideBankStage.path_frozen P S t n
  | backward pre mask S => exact BackwardMaskedStride.path_frozen P hv.1 t n
  | reverse => exact BankReversal.path_frozen P t n
  | rotate R => exact BankRotation.path_frozen P R t n

end TransposeFollowup.BinaryBankOperation

namespace TransposeFollowup.MixedBinaryWord
open Classical ScheduledNativeIO
open MaskedStrideCell (State)
open BinaryBankOperation (Operation)
set_option autoImplicit false

def path (P : ℕ) (ops : List Operation) : Fin 2 → ℕ → ℤ :=
  ScheduledWord.path (BinaryBankOperation.ticks P) (BinaryBankOperation.path P) ops

theorem path_zero (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2) : path P ops t 0=0 :=
  ScheduledWord.path_zero _ _ ops t (fun op hop => BinaryBankOperation.path_zero P op (hv op hop) t)

theorem path_after (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2)
    (n : ℕ) (hn : ticks P ops≤n) : path P ops t n=0 :=
  ScheduledWord.path_after _ _ ops t
    (fun op hop m hm => BinaryBankOperation.path_after P op (hv op hop) t m hm) n hn

theorem path_frozen (P : ℕ) (ops : List Operation) (hv : Valid P ops) (t : Fin 2) (n : ℕ) :
    path P ops t (min n (ticks P ops))=path P ops t n :=
  ScheduledWord.path_frozen _ _ ops t
    (fun op hop m hm => BinaryBankOperation.path_after P op (hv op hop) t m hm) n

theorem schedule_position (P : ℕ) (ops : List Operation) (hv : Valid P ops)
    (w : List Bool) (c : State) (n : ℕ) (hn : n≤ticks P ops) (t : Fin 2) :
    (trajectory (schedule P ops) w c n).work.pos t=c.work.pos t+path P ops t n :=
  ScheduledWord.schedule_position _ _ _ _ ops w c n hn t
    (fun op hop d m hm => BinaryBankOperation.schedule_position P op (hv op hop) w d m hm t)
    (fun op hop m => BinaryBankOperation.path_frozen P op (hv op hop) t m)

end TransposeFollowup.MixedBinaryWord
