import TransposeFollowup.RawRowBankMotion

/-! Rescaling and the vanishing-row-width limit use the existing affine
cover and limit interfaces. Raw external IO is still a separate wrapper. -/
namespace TransposeFollowup.RawRowArithmetic
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open CoupledRowCell (State)
set_option autoImplicit false

theorem bank_scaled_cover (W r : ℕ) (hP : 0<r*W) {H : ℝ} (hH : 0≤H) (t : Fin 2) :
    HasAffineIntervalCover 9
      (fun x => RowBankCurve.curve (r*W) W t ((r*W : ℕ)*x)/(r*W : ℕ)) H := by
  have hp : (0 : ℝ)<(r*W : ℕ) := by exact_mod_cast hP
  exact (RowBankCurve.cover (r*W) W (mul_nonneg hp.le hH) t).rescale hp

theorem bank_scaled_error (sub : Bool) (W r : ℕ) (hW : 0<W) (hP : 0<r*W)
    (w : List Bool) (c : State) (x : ℝ) (t : Fin 2) :
    |(((trajectory (bankSchedule sub W r) w c
        (min ⌊(r*W : ℕ)*x⌋₊ (bankTicks W r))).work.pos t : ℝ)-c.work.pos t)/(r*W : ℕ)-
      RowBankCurve.curve (r*W) W t ((r*W : ℕ)*x)/(r*W : ℕ)|≤(8*W+4 : ℝ)/(r*W : ℕ) := by
  have hp : (0 : ℝ)<(r*W : ℕ) := by exact_mod_cast hP
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right
    (bank_real_curve_error sub W r hW w c ((r*W : ℕ)*x) t) hp.le

theorem bank_error_vanishes {P W : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hW : Tendsto (fun i => (W i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (8*W i+4 : ℝ)/P i) atTop (𝓝 0) := by
  have ha := hW.const_mul (8 : ℝ)
  have hb : Tendsto (fun i => (4 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using ha.add hb

end TransposeFollowup.RawRowArithmetic
