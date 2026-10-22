import TransposeFollowup.BufferedRowRows
import TransposeFollowup.ScheduledBankCleanup
import TransposeFollowup.ZipperListCells

/-! A complete clean bank update, including a blank seed, buffer erase and
both rewinds. Representing W initially blank cells does not allocate or write them.
Each rule supplies its own interpretation of that physical blank seed. -/
namespace TransposeFollowup.BufferedRows
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open CopyMachine (Sym Tape)
open CoupledRowCell (Mode State cfg)
open RawRowArithmetic (initial ticks ticks_eq bankOnly)
set_option autoImplicit false
variable {C : Type}

def bankTicks (W r : ℕ) : ℕ := r*ticks W+ScheduledBankCleanup.ticks (r*W) W

def bankSchedule (u : Rule C) (W r : ℕ) : ℕ → NativeIO.Program (Fin 2) (Mode C) :=
  append (rowsSchedule u W r) (ScheduledBankCleanup.schedule (r*W) W) (r*ticks W)

def bankRun (u : Rule C) (W r : ℕ) (w : List Bool) (c : State C) : State C :=
  ScheduledBankCleanup.run (r*W) W w (trajectory (rowsSchedule u W r) w c (r*ticks W))

def bankStart (m : Mode C) (rows : List (List (Sym Bool))) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) : State C :=
  cfg m ![⟨pre,rows.flatten++suffix⟩,⟨[],[]⟩] pos ip out

def bankOutput (u : Rule C) (W : ℕ) (rows : List (List (Sym Bool))) : List (Sym Bool) :=
  (rowsResult u rows (List.replicate W .blank)).1

theorem bank_active (u : Rule C) (W r i : ℕ) (c : State C) :
    NativeIO.Active (bankSchedule u W r i) c := by
  apply append_active
  · intro j; exact rows_active u W r j c
  · intro j; exact ScheduledBankCleanup.schedule_active _ _ j c

theorem bank_exact (u : Rule C) (W r : ℕ) (w : List Bool) (c : State C) :
    trajectory (bankSchedule u W r) w c (bankTicks W r)=bankRun u W r w c := by
  simp only [bankSchedule,bankTicks,append_exact,ScheduledBankCleanup.schedule_exact,bankRun]

theorem bank_seed (m : Mode C) (W : ℕ) (rows : List (List (Sym Bool)))
    (pre suffix : List (Sym Bool)) (pos : Fin 2 → ℤ) (ip : ℤ) (out : List Bool) :
    bankStart m rows pre suffix pos ip out=
      initial m rows.flatten (List.replicate W .blank) pre [] suffix [] pos ip out := by
  unfold bankStart initial cfg
  congr 2
  congr 1
  funext t
  fin_cases t
  · rfl
  · change (⟨[],[]⟩ : Tape Bool).denote=
      (⟨[],List.replicate W .blank++[]⟩ : Tape Bool).denote
    rw [List.append_nil]
    exact (ZipperListCells.blank_front W).symm

theorem bank_spec (u : Rule C) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode C) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let d := bankRun u W rows.length w (bankStart m rows pre suffix pos ip out)
    (∀ t, d.work.pos t=pos t) ∧
    (∀ z, cells d 0 z=AbsoluteTape.cells
      (⟨pre,bankOutput u W rows++suffix⟩ : Tape Bool).denote (pos 0) z) ∧
    (∀ z, cells d 1 z=.blank) ∧ d.inputPos=ip ∧ d.outRev=out := by
  obtain ⟨m',hr⟩ := rows_exact u W rows hw m (List.replicate W .blank)
    pre [] suffix [] (by simp) pos ip out w
  rw [← bank_seed m W rows pre suffix pos ip out] at hr
  have hl := rows_lengths u W rows hw (List.replicate W .blank) (by simp)
  dsimp only
  unfold bankRun
  rw [hr]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t
    rw [ScheduledBankCleanup.run_position]
    simp [cfg,bankOnly]
  · intro z
    rw [ScheduledBankCleanup.run_cells]
    simpa [cells,cfg,bankOnly,bankOutput,hl.1] using
      ZipperListCells.end_cells (rowsResult u rows (List.replicate W .blank)).1
        pre suffix (pos 0) z
  · apply ScheduledBankCleanup.run_clean
    intro z hz
    have hh : ¬(pos 1≤z ∧ z<pos 1+(rowsResult u rows (List.replicate W .blank)).2.length) := by
      simpa [cfg,bankOnly,hl.2] using hz
    simpa [cells,cfg,bankOnly] using ZipperListCells.front_outside
      (rowsResult u rows (List.replicate W .blank)).2 (pos 1) z hh
  · exact (ScheduledBankCleanup.run_io _ _ w _).1
  · exact (ScheduledBankCleanup.run_io _ _ w _).2

theorem bank_ticks_eq (W r : ℕ) (hW : 0<W) : bankTicks W r=8*(r*W)+2*W := by
  rw [bankTicks,ticks_eq W hW,ScheduledBankCleanup.ticks]
  ring

theorem bank_ticks_linear (W r : ℕ) (hW : 0<W) (hr : 0<r) : bankTicks W r≤10*(r*W) := by
  rw [bank_ticks_eq W r hW]
  have h : W≤r*W := by simpa using Nat.mul_le_mul_right W hr
  omega

end TransposeFollowup.BufferedRows
