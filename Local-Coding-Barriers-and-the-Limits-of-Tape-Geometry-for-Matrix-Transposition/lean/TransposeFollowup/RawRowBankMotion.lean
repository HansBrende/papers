import TransposeFollowup.RawRowBankNative
import TransposeFollowup.RawRowLoopMotion
import TransposeFollowup.ScheduledCleanupMotion
import TransposeFollowup.RowBankCurve
import TransposeFollowup.BufferedRowBankMotion

/-! Uniform geometry of the actual clean row bank, including intermediate
row work, all cleanup passes and the frozen stopped tail. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (Mode State)
set_option autoImplicit false

theorem bank_endpoint (sub : Bool) (W r : ℕ) (w : List Bool) (c : State) (t : Fin 2) :
    (trajectory (bankSchedule sub W r) w c (bankTicks W r)).work.pos t=c.work.pos t :=
  BufferedRows.bank_endpoint (rule sub) W r w c t

theorem bank_curve_error (sub : Bool) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State) (n : ℕ) (t : Fin 2) :
    |((trajectory (bankSchedule sub W r) w c (min n (bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t n|≤8*W :=
  BufferedRows.bank_curve_error (rule sub) W r hW w c n t

theorem bank_real_curve_error (sub : Bool) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State) (x : ℝ) (t : Fin 2) :
    |((trajectory (bankSchedule sub W r) w c (min ⌊x⌋₊ (bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t x|≤8*W+4 :=
  BufferedRows.bank_real_curve_error (rule sub) W r hW w c x t

theorem bank_native_prefix_error {k q : ℕ} (sub : Bool) (W r : ℕ) (hW : 0<W)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (bankTicks W r+1) × Mode) k q)
    (w : List Bool) (c : State) (n : ℕ) (hn : n≤bankTicks W r) :
    let p := program (bankSchedule sub W r) (bankTicks W r)
    ∃ d : Transpose.Config (NativeIO.machine e p),
      Transpose.stepN (NativeIO.machine e p) w n ((lift ⟨0,by omega⟩ c).denote e p)=some d ∧
      ∀ t : Fin 2, |(d.workPos (e.port t) : ℝ)-c.work.pos t-
        RowBankCurve.curve (r*W) W t n|≤8*W :=
  BufferedRows.bank_native_prefix_error (rule sub) W r hW e w c n hn

end TransposeFollowup.RawRowArithmetic
