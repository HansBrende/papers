import TransposeFollowup.BufferedRowBank
import TransposeFollowup.BufferedRowLoopMotion
import TransposeFollowup.ScheduledCleanupMotion
import TransposeFollowup.RowBankCurve

/-! Uniform geometry of the actual clean row bank, including intermediate
row work, all cleanup passes and the frozen stopped tail. -/
namespace TransposeFollowup.BufferedRows
open Classical FixedTapeCompiler ScheduledNativeIO
open CoupledRowCell (Mode State)
open RawRowArithmetic (ticks ticks_eq bankOnly)
set_option autoImplicit false
variable {C : Type}

theorem bank_endpoint (u : Rule C) (W r : ℕ) (w : List Bool) (c : State C) (t : Fin 2) :
    (trajectory (bankSchedule u W r) w c (bankTicks W r)).work.pos t=c.work.pos t := by
  rw [bank_exact]
  simp [bankRun,ScheduledBankCleanup.run_position,rows_endpoint,bankOnly]

theorem bank_curve_error (u : Rule C) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State C) (n : ℕ) (t : Fin 2) :
    |((trajectory (bankSchedule u W r) w c (min n (bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t n|≤8*W := by
  have hs : r*ticks W=7*(r*W) := by rw [ticks_eq W hW]; ring
  have ht := bank_ticks_eq W r hW
  by_cases hr : n≤r*ticks W
  · have hn : n≤bankTicks W r := by unfold bankTicks; omega
    rw [Nat.min_eq_left hn,bankSchedule,append_prefix _ _ _ _ _ _ hr,
      RowBankCurve.before (r*W) W n (by omega)]
    simpa [bankOnly] using rows_linear_error u W r hW w c n hr t
  · by_cases hn : n≤bankTicks W r
    · rw [Nat.min_eq_left hn]
      have hm : n-r*ticks W≤ScheduledBankCleanup.ticks (r*W) W := by
        unfold bankTicks at hn; omega
      have he : n=r*ticks W+(n-r*ticks W) := by omega
      have hx : trajectory (bankSchedule u W r) w c n=
          trajectory (ScheduledBankCleanup.schedule (r*W) W) w
            (trajectory (rowsSchedule u W r) w c (r*ticks W)) (n-r*ticks W) := by
        conv_lhs => rw [he]
        exact append_exact _ _ _ _ _ _
      have hc := RowBankCurve.cleanup (r*W) W (n-r*ticks W)
        (by unfold ScheduledBankCleanup.ticks at hm; omega) t
      rw [show 7*(r*W)+(n-r*ticks W)=n by omega] at hc
      rw [hx,ScheduledBankCleanup.schedule_position _ _ _ _ _ hm,rows_endpoint,hc]
      fin_cases t
      · simp [bankOnly,ScheduledBankCleanup.path]
        ring_nf
        rw [abs_zero]
        positivity
      · have hb := ScheduledBankCleanup.scratch_bounds W (n-r*ticks W)
        have hb' : |(ScheduledBankCleanup.path W 1 (n-r*ticks W) : ℝ)|≤8*W := by
          have ha : |ScheduledBankCleanup.path W 1 (n-r*ticks W)|≤8*W := by
            rw [abs_of_nonneg hb.1]; omega
          exact_mod_cast ha
        simpa [bankOnly] using hb'
    · rw [Nat.min_eq_right (by omega),bank_endpoint,
        RowBankCurve.after (r*W) W n (by omega)]
      simp

theorem bank_real_curve_error (u : Rule C) (W r : ℕ) (hW : 0<W) (w : List Bool)
    (c : State C) (x : ℝ) (t : Fin 2) :
    |((trajectory (bankSchedule u W r) w c (min ⌊x⌋₊ (bankTicks W r))).work.pos t : ℝ)-
      c.work.pos t-RowBankCurve.curve (r*W) W t x|≤8*W+4 := by
  have ha := bank_curve_error u W r hW w c ⌊x⌋₊ t
  have hb := RowBankCurve.sample_stability (r*W) W t x
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith

theorem bank_native_prefix_error {k q : ℕ} (u : Rule C) (W r : ℕ) (hW : 0<W)
    (e : NativeMicrocode.Encoding (Fin 2) (Fin (bankTicks W r+1) × Mode C) k q)
    (w : List Bool) (c : State C) (n : ℕ) (hn : n≤bankTicks W r) :
    let p := program (bankSchedule u W r) (bankTicks W r)
    ∃ d : Transpose.Config (NativeIO.machine e p),
      Transpose.stepN (NativeIO.machine e p) w n ((lift ⟨0,by omega⟩ c).denote e p)=some d ∧
      ∀ t : Fin 2, |(d.workPos (e.port t) : ℝ)-c.work.pos t-
        RowBankCurve.curve (r*W) W t n|≤8*W := by
  refine ⟨_,native_prefix e (bankSchedule u W r) w c
    (fun i _ => bank_active u W r i _) n hn,?_⟩
  intro t
  simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply,Nat.min_eq_left hn]
    using bank_curve_error u W r hW w c n t

end TransposeFollowup.BufferedRows
