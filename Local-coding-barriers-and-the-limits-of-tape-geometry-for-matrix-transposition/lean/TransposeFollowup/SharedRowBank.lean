import TransposeFollowup.ScheduledModeRawIO
import TransposeFollowup.RawRowBankMotion
import TransposeFollowup.BufferedRowBankInvariant
import TransposeFollowup.BufferedRowBankFrame

/-! One fixed controller serves raw IO and coupled-row arithmetic.
The IO component has four states and the row component fifty. Swapping
the product selects the row component; this is a wiring choice, not a
runtime operation. All physical instructions retain their original cost. -/
namespace TransposeFollowup.SharedRowBank
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open NativeIOModeProduct
open CopyMachine (Sym)
set_option autoImplicit false

abbrev Mode := MaskedStrideCell.Mode × CoupledRowCell.Mode
abbrev State := NativeIO.Config (Fin 2) Mode

def ioModes : Mode ≃ MaskedStrideCell.Mode × CoupledRowCell.Mode := Equiv.refl _
def rowModes : Mode ≃ CoupledRowCell.Mode × MaskedStrideCell.Mode := Equiv.prodComm _ _

theorem mode_card : Fintype.card Mode=200 := by decide +kernel

noncomputable def ruleSchedule (u : BufferedRows.Rule Bool) (W r i : ℕ) : NativeIO.Program (Fin 2) Mode :=
  NativeIOModeProduct.program rowModes (BufferedRows.bankSchedule u W r i)

def ruleRun (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) (c : State) : State :=
  attach rowModes c.work.core.pc.1
    (BufferedRows.bankRun u W r w (project rowModes c))

theorem rule_active (u : BufferedRows.Rule Bool) (W r i : ℕ) (c : State) :
    NativeIO.Active (ruleSchedule u W r i) c :=
  NativeIOModeProduct.active rowModes _ (BufferedRows.bank_active u W r i) c

theorem rule_exact (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) (c : State) :
    trajectory (ruleSchedule u W r) w c (BufferedRows.bankTicks W r)=ruleRun u W r w c := by
  unfold ruleSchedule
  rw [trajectory_eq,BufferedRows.bank_exact]
  rfl

theorem rule_spec (u : BufferedRows.Rule Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let c := attach rowModes m.1 (BufferedRows.bankStart m.2 rows pre suffix pos ip out)
    let d := ruleRun u W rows.length w c
    (∀ t, d.work.pos t=pos t) ∧
    (∀ z, cells d 0 z=AbsoluteTape.cells
      (⟨pre,BufferedRows.bankOutput u W rows++suffix⟩ : CopyMachine.Tape Bool).denote (pos 0) z) ∧
    (∀ z, cells d 1 z=.blank) ∧ d.inputPos=ip ∧ d.outRev=out ∧ d.work.core.pc.1=m.1 := by
  dsimp only
  simp only [ruleRun,project_attach]
  have h := BufferedRows.bank_spec u W rows hw m.2 pre suffix pos ip out w
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,rfl⟩

theorem rule_curve_error (u : BufferedRows.Rule Bool) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State) (n : ℕ) (t : Fin 2) :
    |((trajectory (ruleSchedule u W r) w c (min n (BufferedRows.bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t n|≤8*W := by
  unfold ruleSchedule
  rw [trajectory_eq]
  exact BufferedRows.bank_curve_error u W r hW w (project rowModes c) n t

theorem rule_resources (u : BufferedRows.Rule Bool) (W r : ℕ) (m : Mode) :
    let N := BufferedRows.bankTicks W r
    let e := NativeMicrocode.initialEncoding (T:=Fin 2) ((⟨0,by omega⟩,m) : Fin (N+1) × Mode)
    let M := NativeIO.machine e (ScheduledNativeIO.program (ruleSchedule u W r) N)
    M.k=2 ∧ M.g+1=5 ∧ M.q+1=(N+1)*200 := by
  refine ⟨rfl,rfl,?_⟩
  simpa only [mode_card] using native_state_count (ruleSchedule u W r) (BufferedRows.bankTicks W r) m

theorem rule_represents (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) (c : State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (ruleRun u W r w c)
      (BufferedRows.bankValue u W r (BankWord.input BankWord.symbols c)) :=
  BufferedRows.bank_represents u W r w (project rowModes c) hc

theorem rule_endpoint (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) (c : State) (t : Fin 2) :
    (ruleRun u W r w c).work.pos t=c.work.pos t := by
  rw [← rule_exact]
  unfold ruleSchedule
  rw [trajectory_eq]
  exact BufferedRows.bank_endpoint u W r w (project rowModes c) t

theorem rule_frame (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) (c : State) (z : ℤ)
    (hz : z<c.work.pos 0 ∨ c.work.pos 0+(r*W : ℕ) ≤ z) :
    cells (ruleRun u W r w c) 0 z=cells c 0 z :=
  BufferedRows.bank_frame u W r w (project rowModes c) z hz

theorem rule_real_curve_error (u : BufferedRows.Rule Bool) (W r : ℕ) (hW : 0<W)
    (w : List Bool) (c : State) (x : ℝ) (t : Fin 2) :
    |((trajectory (ruleSchedule u W r) w c (min ⌊x⌋₊ (BufferedRows.bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t x| ≤ 8*W+4 := by
  unfold ruleSchedule
  rw [trajectory_eq]
  exact BufferedRows.bank_real_curve_error u W r hW w (project rowModes c) x t

noncomputable def schedule (sub : Bool) (W r i : ℕ) : NativeIO.Program (Fin 2) Mode :=
  NativeIOModeProduct.program rowModes (RawRowArithmetic.bankSchedule sub W r i)

def run (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) : State :=
  attach rowModes c.work.core.pc.1
    (RawRowArithmetic.bankRun sub W r w (project rowModes c))

theorem schedule_active (sub : Bool) (W r i : ℕ) (c : State) :
    NativeIO.Active (schedule sub W r i) c :=
  rule_active (RawRowArithmetic.rule sub) W r i c

theorem schedule_exact (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) :
    trajectory (schedule sub W r) w c (RawRowArithmetic.bankTicks W r)=run sub W r w c :=
  rule_exact (RawRowArithmetic.rule sub) W r w c

theorem bank_spec (sub : Bool) (W : ℕ) (rows : List (List (Sym Bool)))
    (hw : ∀ xs ∈ rows, xs.length=W) (m : Mode) (pre suffix : List (Sym Bool))
    (pos : Fin 2 → ℤ) (ip : ℤ) (out w : List Bool) :
    let c := attach rowModes m.1 (RawRowArithmetic.bankStart m.2 rows pre suffix pos ip out)
    let d := run sub W rows.length w c
    (∀ t, d.work.pos t=pos t) ∧
    (∀ z, cells d 0 z=AbsoluteTape.cells
      (⟨pre,RawRowArithmetic.bankOutput sub W rows++suffix⟩ : CopyMachine.Tape Bool).denote (pos 0) z) ∧
    (∀ z, cells d 1 z=.blank) ∧ d.inputPos=ip ∧ d.outRev=out ∧ d.work.core.pc.1=m.1 :=
  rule_spec (RawRowArithmetic.rule sub) W rows hw m pre suffix pos ip out w

theorem bank_curve_error (sub : Bool) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State) (n : ℕ) (t : Fin 2) :
    |((trajectory (schedule sub W r) w c (min n (RawRowArithmetic.bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t n|≤8*W :=
  rule_curve_error (RawRowArithmetic.rule sub) W r hW w c n t

theorem native_resources (sub : Bool) (W r : ℕ) (m : Mode) :
    let N := RawRowArithmetic.bankTicks W r
    let e := NativeMicrocode.initialEncoding (T:=Fin 2) ((⟨0,by omega⟩,m) : Fin (N+1) × Mode)
    let M := NativeIO.machine e (ScheduledNativeIO.program (schedule sub W r) N)
    M.k=2 ∧ M.g+1=5 ∧ M.q+1=(N+1)*200 :=
  rule_resources (RawRowArithmetic.rule sub) W r m

end TransposeFollowup.SharedRowBank
