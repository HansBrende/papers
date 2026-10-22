import TransposeFollowup.MatrixPermutationPalette
import TransposeFollowup.BankBlockReversalApproximation
import TransposeFollowup.IndexedBankRowsMotion

/-! Actual-state geometry for the shared permutation palette, at arbitrary
prefix times. The common constants also cover the two arithmetic palettes. -/
namespace TransposeFollowup.MatrixPermutationPalette
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

def coverSize : ℕ := 81*81*81*9

def errorBound (W : ℕ) : ℝ := 32*((W : ℝ)+1)

noncomputable def approximation (b d : ℕ) : Operation → ℕ → Fin 2 → ℝ → ℝ
  | .rows => BankBlockReversal.approximation (d*(d*b))
  | .entries => fun A => ScheduledBankRows.curve (d*(d*b)) 11 A
  | .rotate _ => fun A => ScheduledBankRows.curve (d*(d*b)) 23 A

theorem approximation_cover (b d : ℕ) (op : Operation) (A : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover coverSize (approximation b d op A t) H := by
  cases op with
  | rows => exact (BankBlockReversal.approximation_cover _ A hH t).mono (by norm_num) (by norm_num [coverSize])
  | entries => exact (ScheduledBankRows.curve_cover _ 11 A (by norm_num) hH t).mono (by norm_num) (by norm_num [coverSize])
  | rotate sub => exact (ScheduledBankRows.curve_cover _ 23 A (by norm_num) hH t).mono (by norm_num) (by norm_num [coverSize])

theorem approximation_error (b d : ℕ) (hb : 0<b) (hd : 0<d) (op : Operation)
    (A : ℕ) (w : List Bool) (c : SharedRowBank.State) (x : ℝ) (t : Fin 2) :
    |((trajectory (code b d op) w c (min (⌊x⌋₊-A) (cost b d op))).work.pos t : ℝ)-
      c.work.pos t-approximation b d op A t x| ≤ errorBound (d*b) := by
  have hW := Nat.mul_pos hd hb
  have hnonneg : (0 : ℝ) ≤ (d*b : ℕ) := Nat.cast_nonneg _
  cases op with
  | rows =>
    have h := BankBlockReversal.schedule_curve_error SharedBankSymbols.read SharedBankSymbols.write
      SharedBankSymbols.reset (d*b) d A hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | entries =>
    have hc : (RawEntryReversal.update b d).cost+d*b=11*(d*b) := by
      change BankBlockReversal.ticks b d+d*b=11*(d*b)
      rw [BankBlockReversal.ticks_eq]; omega
    have h := ScheduledBankRows.schedule_curve_error (RawEntryReversal.update b d) d 11 A hc
      (by norm_num) hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | rotate sub =>
    have h := IndexedBankRows.schedule_curve_error (RawEntryRotation.update sub b d) d 23 A
      (RawEntryRotation.update_cost sub b d) (by norm_num) hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)

end TransposeFollowup.MatrixPermutationPalette
