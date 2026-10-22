import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawRowProgram
import TransposeFollowup.RawRowBankApproximation

/-! The row-bank approximation through the entire raw native execution.
All offsets are paid clock times. Existing clipped-ramp covers, floor
translation and the original frozen trajectory theorem do the work. -/
namespace TransposeFollowup.RowBankCurve
open AffineMotion
set_option autoImplicit false

theorem shift_cover (P W A : ℕ) {H : ℝ} (hH : 0≤H) (t : Fin 2) :
    HasAffineIntervalCover 9 (fun x => curve P W t (x-A)) H := by
  by_cases ht : t=0
  · simp only [curve,ite_eq_left ht,RawMaskedStride.clippedRamp_shift,zero_add]
    exact (clippedRamp_cover hH (by positivity) (by positivity) (by norm_num : (0 : ℝ)<7)).sub
      (clippedRamp_cover hH (by positivity) (by positivity) (by norm_num : (0 : ℝ)<1))
  · simp only [curve,ite_eq_right ht]
    exact (HasAffineIntervalCover.const hH 0).mono (by norm_num) (by norm_num)

end TransposeFollowup.RowBankCurve

namespace TransposeFollowup.SharedRowBank
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

noncomputable def rawCurve (W r : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  RowBankCurve.curve (r*W) W t (x-(4*(r*W) : ℕ))+
    RawBankProgram.ioCurve (r*W) (RawRowArithmetic.bankTicks W r) t x

theorem rawCurve_cover (W r : ℕ) {H : ℝ} (hH : 0≤H) (t : Fin 2) :
    HasAffineIntervalCover 243 (rawCurve W r t) H :=
  (RowBankCurve.shift_cover (r*W) W (4*(r*W)) hH t).add
    (RawBankProgram.ioCurve_cover (r*W) (RawRowArithmetic.bankTicks W r) hH t)

theorem rawRuleCurve_error (u : BufferedRows.Rule Bool) (W r : ℕ) (hW : 0<W) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (rawRuleMachine u W r) w ⌊x⌋₊
      ((RawProgramShell.encoding initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)).port t) : ℝ)-
      rawCurve W r t x|≤8*W+8 := by
  let c := RawProgramShell.prepared initialRowMode (r*W) w
  have hpos : (NativeIOModeProduct.project rowModes c).work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl Mode) initialRowMode (r*W) w).1 t
  have hb := BufferedRows.bank_real_curve_error u W r hW w
    (NativeIOModeProduct.project rowModes c) (x-(4*(r*W) : ℕ)) t
  rw [hpos,Int.cast_zero,sub_zero,Nat.floor_sub_natCast] at hb
  have hbody : |((trajectory (ruleSchedule u W r) w c
      (min (⌊x⌋₊-4*(r*W)) (RawRowArithmetic.bankTicks W r))).work.pos t : ℝ)-
      RowBankCurve.curve (r*W) W t (x-(4*(r*W) : ℕ))|≤8*W+4 := by
    unfold ruleSchedule
    rw [NativeIOModeProduct.trajectory_eq]
    exact hb
  have hi := RawBankProgram.ioPath_curve_error (r*W) (RawRowArithmetic.bankTicks W r) t x
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine initialRowMode (r*W) (RawRowArithmetic.bankTicks W r) (ruleSchedule u W r))
    w ⌊x⌋₊ ((RawProgramShell.encoding initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)).port t) : ℝ)-_|
      ≤8*W+8
  rw [RawProgramShell.workTraj_decomposition initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)
    (ruleSchedule u W r) (rule_active u W r)]
  simp only [rawCurve,Int.cast_add]
  rw [abs_le] at hbody hi ⊢
  constructor <;> linarith

theorem raw_rule_scaled_approximation (u : BufferedRows.Rule Bool) (W r : ℕ) (hW : 0<W) (hP : 0<r*W)
    {H : ℝ} (hH : 0≤H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243 (fun x => rawCurve W r t ((r*W : ℕ)*x)/(r*W : ℕ)) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (rawRuleMachine u W r) w ⌊(r*W : ℕ)*x⌋₊
        ((RawProgramShell.encoding initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)).port t) : ℝ)/(r*W : ℕ)-
        rawCurve W r t ((r*W : ℕ)*x)/(r*W : ℕ)|≤(8*W+8 : ℝ)/(r*W : ℕ) := by
  have hp : (0 : ℝ)<(r*W : ℕ) := by exact_mod_cast hP
  refine ⟨(rawCurve_cover W r (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (rawRuleCurve_error u W r hW w ((r*W : ℕ)*x) t) hp.le


theorem rawCurve_error (sub : Bool) (W r : ℕ) (hW : 0<W) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (rawMachine sub W r) w ⌊x⌋₊
      ((RawProgramShell.encoding initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)).port t) : ℝ)-
      rawCurve W r t x|≤8*W+8 :=
  rawRuleCurve_error (RawRowArithmetic.rule sub) W r hW w x t

theorem raw_scaled_approximation (sub : Bool) (W r : ℕ) (hW : 0<W) (hP : 0<r*W)
    {H : ℝ} (hH : 0≤H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243 (fun x => rawCurve W r t ((r*W : ℕ)*x)/(r*W : ℕ)) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (rawMachine sub W r) w ⌊(r*W : ℕ)*x⌋₊
        ((RawProgramShell.encoding initialRowMode (r*W) (RawRowArithmetic.bankTicks W r)).port t) : ℝ)/(r*W : ℕ)-
        rawCurve W r t ((r*W : ℕ)*x)/(r*W : ℕ)|≤(8*W+8 : ℝ)/(r*W : ℕ) :=
  raw_rule_scaled_approximation (RawRowArithmetic.rule sub) W r hW hP hH w t

theorem raw_error_vanishes {P W : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hW : Tendsto (fun i => (W i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (8*W i+8 : ℝ)/P i) atTop (𝓝 0) := by
  have ha := RawRowArithmetic.bank_error_vanishes hP hW
  have hb : Tendsto (fun i => (4 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  convert ha.add hb using 1
  · ext i
    rw [← add_div]
    congr 1
    ring
  · simp

end TransposeFollowup.SharedRowBank
