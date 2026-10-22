import TransposeFollowup.RawProgramShell
import TransposeFollowup.SharedRowBank

/-! Raw integer-row prefix/difference execution from the original TM's
blank initial work tapes through its actual output tape. The clean-bank
invariant and generic IO shell discharge all preparation assumptions. -/
namespace TransposeFollowup.SharedRowBank
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
set_option autoImplicit false

theorem represents (sub : Bool) (W r : ℕ) (w : List Bool) (c : State)
    (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols (r*W) c (run sub W r w c)
      (RawRowArithmetic.bankValue sub W r (BankWord.input BankWord.symbols c)) :=
  RawRowArithmetic.bank_represents sub W r w (NativeIOModeProduct.project rowModes c) hc

def initialRowMode : CoupledRowCell.Mode := (false,.blank,.blank)

def rawTicks (W r : ℕ) : ℕ := RawProgramShell.ticks (r*W) (RawRowArithmetic.bankTicks W r)

noncomputable def rawRuleMachine (u : BufferedRows.Rule Bool) (W r : ℕ) :=
  RawProgramShell.machine initialRowMode (r*W) (RawRowArithmetic.bankTicks W r) (ruleSchedule u W r)

def rawRuleOutput (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) : List Bool :=
  (List.range (r*W)).map (fun j => MaskedStrideCell.bit
    (BufferedRows.bankValue u W r (fun i : ℕ => .data (ScheduledRawInput.inputBit w i)) j))

theorem raw_rule_resources (u : BufferedRows.Rule Bool) (W r : ℕ) :
    (rawRuleMachine u W r).k=2 ∧ (rawRuleMachine u W r).g+1=5 ∧
    (rawRuleMachine u W r).q+1=(rawTicks W r+1)*200 := by
  have h := RawProgramShell.fixed_resources initialRowMode (r*W)
    (RawRowArithmetic.bankTicks W r) (ruleSchedule u W r)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

theorem raw_rule_native_correct (u : BufferedRows.Rule Bool) (W r : ℕ) (w : List Bool) :
    ∃ d : Transpose.Config (rawRuleMachine u W r),
      Transpose.stepN (rawRuleMachine u W r) w (rawTicks W r) (Transpose.init (rawRuleMachine u W r))=some d ∧
      Transpose.step (rawRuleMachine u W r) w d=none ∧
      d.outRev=(rawRuleOutput u W r w).reverse ∧
      ∀ z, d.work ((RawProgramShell.encoding initialRowMode (r*W)
        (RawRowArithmetic.bankTicks W r)).port 1) z=0 := by
  exact RawProgramShell.native_correct initialRowMode (r*W)
    (RawRowArithmetic.bankTicks W r) (ruleSchedule u W r) (rule_active u W r)
    (BufferedRows.bankValue u W r)
    (BufferedRows.bankValue_congr u W r)
    (fun w c hc => by
      have h := rule_represents u W r w c hc
      rw [← rule_exact u W r w c] at h
      exact h) w

noncomputable def rawMachine (sub : Bool) (W r : ℕ) :=
  RawProgramShell.machine initialRowMode (r*W) (RawRowArithmetic.bankTicks W r) (schedule sub W r)

def rawOutput (sub : Bool) (W r : ℕ) (w : List Bool) : List Bool :=
  (List.range (r*W)).map (fun j => MaskedStrideCell.bit
    (RawRowArithmetic.bankValue sub W r (fun i : ℕ => .data (ScheduledRawInput.inputBit w i)) j))

theorem raw_ticks_eq (W r : ℕ) (hW : 0<W) : rawTicks W r=15*(r*W)+2*W := by
  rw [rawTicks,RawProgramShell.ticks_eq,RawRowArithmetic.bank_ticks_eq W r hW]
  omega

theorem raw_ticks_linear (W r : ℕ) (hW : 0<W) (hr : 0<r) : rawTicks W r≤17*(r*W) := by
  rw [raw_ticks_eq W r hW]
  have h : W≤r*W := by simpa using Nat.mul_le_mul_right W hr
  omega

theorem raw_resources (sub : Bool) (W r : ℕ) :
    (rawMachine sub W r).k=2 ∧ (rawMachine sub W r).g+1=5 ∧
    (rawMachine sub W r).q+1=(rawTicks W r+1)*200 :=
  raw_rule_resources (RawRowArithmetic.rule sub) W r

theorem raw_native_correct (sub : Bool) (W r : ℕ) (w : List Bool) :
    ∃ d : Transpose.Config (rawMachine sub W r),
      Transpose.stepN (rawMachine sub W r) w (rawTicks W r) (Transpose.init (rawMachine sub W r))=some d ∧
      Transpose.step (rawMachine sub W r) w d=none ∧
      d.outRev=(rawOutput sub W r w).reverse ∧
      ∀ z, d.work ((RawProgramShell.encoding initialRowMode (r*W)
        (RawRowArithmetic.bankTicks W r)).port 1) z=0 :=
  raw_rule_native_correct (RawRowArithmetic.rule sub) W r w

end TransposeFollowup.SharedRowBank
