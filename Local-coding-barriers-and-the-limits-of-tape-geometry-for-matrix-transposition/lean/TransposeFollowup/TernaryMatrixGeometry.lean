import TransposeFollowup.TernaryMatrixPalette
import TransposeFollowup.MatrixPermutationGeometry
import TransposeFollowup.BufferedRowShiftApproximation
import TransposeFollowup.BankSymbolRotationApproximation

/-! Concrete geometry for every full b-trit F3 operation. The bounds use
actual stage states and arbitrary paid prefix times, as required by the
word-composition theorem. -/
namespace TransposeFollowup.TernaryMatrixPalette
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
open MatrixPermutationPalette (coverSize errorBound)
set_option autoImplicit false

noncomputable def approximation (b d : ℕ) : Operation → ℕ → Fin 2 → ℝ → ℝ
  | .permutation op => MatrixPermutationPalette.approximation b d op
  | .vertical _ => SharedRowBank.rowApproximation (d*(d*b)) (d*b)
  | .horizontal _ => fun A => ScheduledBankRows.curve (d*(d*b)) 11 A
  | .phase => fun A => ScheduledBankRows.curve (d*(d*b)) 11 A
  | .shift right => BankSymbolRotation.approximation (d*(d*b)) (RawEntryShift.offset right b (d*d))

theorem approximation_cover (b d : ℕ) (op : Operation) (A : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover coverSize (approximation b d op A t) H := by
  cases op with
  | permutation op => exact MatrixPermutationPalette.approximation_cover b d op A hH t
  | vertical sub => exact (SharedRowBank.rowApproximation_cover _ _ A hH t).mono (by norm_num) (by norm_num [coverSize])
  | horizontal sub => exact (ScheduledBankRows.curve_cover _ 11 A (by norm_num) hH t).mono (by norm_num) (by norm_num [coverSize])
  | phase => exact (ScheduledBankRows.curve_cover _ 11 A (by norm_num) hH t).mono (by norm_num) (by norm_num [coverSize])
  | shift right => exact BankSymbolRotation.approximation_cover _ _ A hH t

theorem approximation_error (b d : ℕ) (hb : 0<b) (hd : 0<d) (op : Operation)
    (A : ℕ) (w : List Bool) (c : SharedRowBank.State) (x : ℝ) (t : Fin 2) :
    |((trajectory (code b d op) w c (min (⌊x⌋₊-A) (cost b d op))).work.pos t : ℝ)-
      c.work.pos t-approximation b d op A t x| ≤ errorBound (d*b) := by
  have hW := Nat.mul_pos hd hb
  have hnonneg : (0 : ℝ) ≤ (d*b : ℕ) := Nat.cast_nonneg _
  cases op with
  | permutation op => exact MatrixPermutationPalette.approximation_error b d hb hd op A w c x t
  | vertical sub =>
    have h := SharedRowBank.rule_shifted_curve_error (TernaryBank.bufferRule sub) (d*b) d A hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | horizontal sub =>
    have h := ScheduledBankRows.schedule_curve_error (RawTernaryMatrixHorizontal.update sub b d) d 11 A
      (RawTernaryMatrixHorizontal.update_cost sub b d hb hd) (by norm_num) hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | phase =>
    have h := IndexedBankRows.schedule_curve_error (RawSymbolMap.update (TernaryPhase.table b d)) (d*(d*b)) 11 A
      (RawSymbolMap.update_cost (TernaryPhase.table b d)) (by norm_num) (by norm_num) w c x t
    have he : (14 : ℝ) ≤ errorBound (d*b) := by dsimp [errorBound]; nlinarith
    have hh := h.trans (by convert he using 1; norm_num)
    simpa only [code,cost,approximation,RawSymbolMap.schedule,RawSymbolMap.internalTicks,Nat.mul_one] using hh
  | shift right =>
    have h := BankSymbolRotation.schedule_curve_error (d*(d*b)) (RawEntryShift.offset right b (d*d)) A w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)

end TransposeFollowup.TernaryMatrixPalette
