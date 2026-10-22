import TransposeFollowup.RawRowArithmeticRows
import TransposeFollowup.ScheduledBankCleanup
import TransposeFollowup.ZipperListCells
import TransposeFollowup.BufferedRowBank

/-! A complete clean bank update, including zero seed, buffer erase and
both rewinds. The initially blank buffer is already zero under the checked
decoder; representing W blank cells does not allocate or write them. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
set_option autoImplicit false

def bankTicks (W r : ℕ) : ℕ := r*ticks W+ScheduledBankCleanup.ticks (r*W) W

def bankSchedule (sub : Bool) (W r : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (rowsSchedule sub W r) (ScheduledBankCleanup.schedule (r*W) W) (r*ticks W)

def bankRun (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) : State :=
  ScheduledBankCleanup.run (r*W) W w (trajectory (rowsSchedule sub W r) w c (r*ticks W))

def bankStart {C : Type} (m : Mode C) (rows : List (List (Sym Bool))) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State C :=
  cfg m ![⟨pre,rows.flatten++suffix⟩,⟨[],[]⟩] pos ip out

def bankOutput (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool))) : List (Sym Bool) :=
  (rowsResult sub rows (List.replicate W .blank)).1

theorem bank_active (sub : Bool) (W r i : ℕ) (c : State) :
    NativeIO.Active (bankSchedule sub W r i) c :=
  BufferedRows.bank_active (rule sub) W r i c

theorem bank_exact (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) :
    trajectory (bankSchedule sub W r) w c (bankTicks W r)=bankRun sub W r w c :=
  BufferedRows.bank_exact (rule sub) W r w c

theorem bank_seed (m : Mode) (W : ℕ) (rows : List (List (Sym Bool)))
    (pre suffix : List (Sym Bool)) (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    bankStart m rows pre suffix pos ip out=
      initial m rows.flatten (List.replicate W .blank) pre [] suffix [] pos ip out :=
  BufferedRows.bank_seed m W rows pre suffix pos ip out

theorem bank_spec (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let d := bankRun sub W rows.length w (bankStart m rows pre suffix pos ip out)
    (∀ t, d.work.pos t=pos t) ∧
    (∀ z, cells d 0 z=AbsoluteTape.cells
      (⟨pre,bankOutput sub W rows++suffix⟩ : Tape Bool).denote (pos 0) z) ∧
    (∀ z, cells d 1 z=.blank) ∧ d.inputPos=ip ∧ d.outRev=out :=
  BufferedRows.bank_spec (rule sub) W rows hw m pre suffix pos ip out w

theorem bank_ticks_eq (W r : ℕ) (hW : 0<W) : bankTicks W r=8*(r*W)+2*W :=
  BufferedRows.bank_ticks_eq W r hW

theorem bank_ticks_linear (W r : ℕ) (hW : 0<W) (hr : 0<r) : bankTicks W r≤10*(r*W) :=
  BufferedRows.bank_ticks_linear W r hW hr

end TransposeFollowup.RawRowArithmetic
