import TransposeFollowup.BankSymbolRotation

/-! Turn the shared buffered bank into one independent outer-row update.
Stationary padding gives exactly 10nB steps for positive buffer width B
and group count n. Every reset and buffer clear is already paid. -/
namespace TransposeFollowup.BufferedRowUpdate
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false

def ticks (B n : ℕ) : ℕ := BufferedRows.bankTicks B n+(10*(n*B)-BufferedRows.bankTicks B n)

noncomputable def schedule (u : BufferedRows.Rule Bool) (B n : ℕ) :=
  append (SharedRowBank.ruleSchedule u B n) (fun _ => BankSymbolRotation.idle) (BufferedRows.bankTicks B n)

theorem ticks_eq (B n : ℕ) (hB : 0<B) (hn : 0<n) : ticks B n=10*(n*B) :=
  Nat.add_sub_of_le (BufferedRows.bank_ticks_linear B n hB hn)

theorem schedule_exact (u : BufferedRows.Rule Bool) (B n : ℕ) (w : List Bool) (c : SharedRowBank.State) :
    trajectory (schedule u B n) w c (ticks B n)=SharedRowBank.ruleRun u B n w c := by
  rw [schedule,ticks,append_exact,SharedRowBank.rule_exact,BankSymbolRotation.idle_exact]

theorem schedule_active (u : BufferedRows.Rule Bool) (B n i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule u B n i) c := by
  unfold schedule
  apply append_active
  · intro j; exact SharedRowBank.rule_active u B n j c
  · intro _; simp [BankSymbolRotation.idle,NativeIO.Active]

noncomputable def update (u : BufferedRows.Rule Bool) (B n : ℕ) :
    ScheduledBankRows.Update SharedRowBank.Mode (n*B) where
  cost := ticks B n
  code := schedule u B n
  value := BufferedRows.bankValue u B n
  congruent := BufferedRows.bankValue_congr u B n
  active := schedule_active u B n
  endpoint := by intro w c t; rw [schedule_exact]; exact SharedRowBank.rule_endpoint u B n w c t
  represents := by intro w c hc; rw [schedule_exact]; exact SharedRowBank.rule_represents u B n w c hc
  frame := by intro w c z hz; rw [schedule_exact]; exact SharedRowBank.rule_frame u B n w c z hz

end TransposeFollowup.BufferedRowUpdate
