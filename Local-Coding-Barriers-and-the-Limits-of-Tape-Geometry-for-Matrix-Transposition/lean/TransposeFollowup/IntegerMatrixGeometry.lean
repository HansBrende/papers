import TransposeFollowup.IntegerMatrixPalette
import TransposeFollowup.MatrixPermutationGeometry
import TransposeFollowup.BufferedRowShiftApproximation
import TransposeFollowup.RawRowXorApproximation
import TransposeFollowup.RawUnitArithmeticApproximation

/-! Concrete geometry for every declared integer operation, uniformly over
its public choice and its actual starting configuration. -/
namespace TransposeFollowup.IntegerMatrixPalette
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
open MatrixPermutationPalette (coverSize errorBound)
set_option autoImplicit false

noncomputable def approximation (b d : ℕ) : Operation → ℕ → Fin 2 → ℝ → ℝ
  | .permutation op => MatrixPermutationPalette.approximation b d op
  | .addRows _ => SharedRowBank.rowApproximation (d*(d*b)) (d*b)
  | .xorRows _ => MaskedStrideBankStage.smallApproximation (d*(d*b))
  | .unit _ => RawCarryBank.approximation (d*(d*b))

theorem approximation_cover (b d : ℕ) (op : Operation) (A : ℕ)
    {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover coverSize (approximation b d op A t) H := by
  cases op with
  | permutation op => exact MatrixPermutationPalette.approximation_cover b d op A hH t
  | addRows sub => exact (SharedRowBank.rowApproximation_cover _ _ A hH t).mono (by norm_num) (by norm_num [coverSize])
  | xorRows isPrefix => exact (MaskedStrideBankStage.smallApproximation_cover _ A hH t).mono (by norm_num) (by norm_num [coverSize])
  | unit sub => exact (RawCarryBank.approximation_cover _ A hH t).mono (by norm_num) (by norm_num [coverSize])

theorem approximation_error (b d : ℕ) (hb : 0<b) (hd : 0<d) (op : Operation)
    (A : ℕ) (w : List Bool) (c : SharedRowBank.State) (x : ℝ) (t : Fin 2) :
    |((trajectory (code b d op) w c (min (⌊x⌋₊-A) (cost b d op))).work.pos t : ℝ)-
      c.work.pos t-approximation b d op A t x| ≤ errorBound (d*b) := by
  have hW := Nat.mul_pos hd hb
  have hnonneg : (0 : ℝ) ≤ (d*b : ℕ) := Nat.cast_nonneg _
  cases op with
  | permutation op => exact MatrixPermutationPalette.approximation_error b d hb hd op A w c x t
  | addRows sub =>
    have h := SharedRowBank.rule_shifted_curve_error (RawRowArithmetic.rule sub) (d*b) d A hW w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | xorRows isPrefix =>
    have h := RawRowXor.schedule_curve_error isPrefix (d*(d*b)) hW A w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)
  | unit sub =>
    have h := RawUnitArithmetic.schedule_curve_error sub (d*(d*b)) A (Nat.mul_pos hd hW) w c x t
    exact h.trans (by dsimp [errorBound]; nlinarith)

end TransposeFollowup.IntegerMatrixPalette
