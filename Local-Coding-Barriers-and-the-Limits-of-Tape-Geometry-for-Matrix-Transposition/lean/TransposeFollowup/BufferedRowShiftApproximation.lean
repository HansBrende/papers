import TransposeFollowup.SharedRowBank

/-! The existing buffered-row curve at an arbitrary paid prefix time.
Only translation of two clipped ramps and mathlib's floor identity are
needed; the native execution bound is reused unchanged. -/
namespace TransposeFollowup.SharedRowBank
open Classical FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

noncomputable def rowApproximation (P W A : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  if t=0 then clippedRamp P A 7 x-clippedRamp P (A+(7*P+2*W) : ℕ) 1 x else 0

theorem rowApproximation_shift (P W A : ℕ) (t : Fin 2) (x : ℝ) :
    RowBankCurve.curve P W t (x-A)=rowApproximation P W A t x := by
  have h (B : ℕ) (D : ℝ) : clippedRamp P B D (x-A)=clippedRamp P (A+B : ℕ) D x := by
    have he : x-(A : ℝ)-(B : ℝ)=x-((A+B : ℕ) : ℝ) := by push_cast; ring
    unfold clippedRamp
    rw [he]
  have h0 := h 0 7
  simp only [Nat.cast_zero,Nat.add_zero] at h0
  simp only [RowBankCurve.curve,rowApproximation,h0,h]

theorem rowApproximation_cover (P W A : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 9 (rowApproximation P W A t) H := by
  change HasAffineIntervalCover 9 (fun x => rowApproximation P W A t x) H
  by_cases ht : t=0
  · simp only [rowApproximation,ite_eq_left ht]
    exact (clippedRamp_cover hH (Nat.cast_nonneg P) (Nat.cast_nonneg A) (by norm_num)).sub
      (clippedRamp_cover hH (Nat.cast_nonneg P) (Nat.cast_nonneg _) (by norm_num))
  · simp only [rowApproximation,ite_eq_right ht]
    exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

theorem rule_shifted_curve_error (u : BufferedRows.Rule Bool) (W r A : ℕ) (hW : 0<W)
    (w : List Bool) (c : State) (x : ℝ) (t : Fin 2) :
    |((trajectory (ruleSchedule u W r) w c
      (min (⌊x⌋₊-A) (BufferedRows.bankTicks W r))).work.pos t : ℝ)-c.work.pos t-
      rowApproximation (r*W) W A t x| ≤ 8*W+4 := by
  have h := rule_real_curve_error u W r hW w c (x-A) t
  rw [Nat.floor_sub_natCast,rowApproximation_shift] at h
  exact h

end TransposeFollowup.SharedRowBank
