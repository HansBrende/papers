import TransposeFollowup.RawTernaryMatrixHorizontal
import TransposeFollowup.RawEntryReversalApproximation

/-! Q/q uses the already established 11W-per-row affine reference curve.
Its within-row implementation differs from entry reversal; the generic
row-block theorem supplies the error bound for this actual schedule.
The existing curve cover, normalization and limit facts are reused. -/
namespace TransposeFollowup.RawTernaryMatrixHorizontal
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem curve_error (sub : Bool) (b d r : ℕ) (hb : 0<b) (hd : 0<d)
    (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine sub b d r) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)-
      RawEntryReversal.curve b d r t x| ≤ 12*(d*b : ℕ)+6 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode (r*(d*b)) w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode (r*(d*b)) w).1 t
  have hbody := ScheduledBankRows.schedule_curve_error (update sub b d) r 11 (4*(r*(d*b)))
    (update_cost sub b d hb hd) (by norm_num) (Nat.mul_pos hd hb) w c x t
  rw [hpos,Int.cast_zero,sub_zero] at hbody
  have hc : |((trajectory (schedule sub b d r) w c
      (min (⌊x⌋₊-4*(r*(d*b))) (internalTicks b d r))).work.pos t : ℝ)-
      ScheduledBankRows.curve (r*(d*b)) 11 (4*(r*(d*b))) t x| ≤ 12*(d*b : ℕ)+2 := by
    simpa only [schedule,internalTicks,ScheduledBankRows.ticks,update,BufferedRowUpdate.update,
      Nat.cast_ofNat,show (11 : ℝ)+1=12 by norm_num] using hbody
  have hi := RawBankProgram.ioPath_curve_error (r*(d*b)) (internalTicks b d r) t x
  have hN : internalTicks b d r=RawEntryReversal.internalTicks b d r := by
    rw [internal_ticks_eq b d r hb hd,RawEntryReversal.internal_ticks_eq]
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r) (schedule sub b d r))
    w ⌊x⌋₊ ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)-
    RawEntryReversal.curve b d r t x| ≤ 12*(d*b : ℕ)+6
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode (r*(d*b))
    (internalTicks b d r) (schedule sub b d r) (schedule_active sub b d r)]
  simp only [RawEntryReversal.curve,← hN,Int.cast_add]
  rw [abs_le] at hc hi ⊢
  constructor <;> linarith

theorem scaled_approximation (sub : Bool) (b d r : ℕ) (hb : 0<b) (hd : 0<d) (hP : 0<r*(d*b))
    {H : ℝ} (hH : 0 ≤ H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243
      (fun x => RawEntryReversal.curve b d r t ((r*(d*b) : ℕ)*x)/(r*(d*b) : ℕ)) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine sub b d r) w ⌊(r*(d*b) : ℕ)*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)/(r*(d*b) : ℕ)-
        RawEntryReversal.curve b d r t ((r*(d*b) : ℕ)*x)/(r*(d*b) : ℕ)| ≤ (12*(d*b : ℕ)+6 : ℝ)/(r*(d*b) : ℕ) := by
  have hp : (0 : ℝ)<(r*(d*b) : ℕ) := by exact_mod_cast hP
  refine ⟨(RawEntryReversal.curve_cover b d r (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error sub b d r hb hd w ((r*(d*b) : ℕ)*x) t) hp.le

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (sub : ℕ → Bool) (b d r : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, r i*(d i*b i)=inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (sub i) (b i) (d i) (r i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  have ht : ∀ᶠ i in atTop,
      RawProgramShell.ticks (inputLength (ns i)) (internalTicks (b i) (d i) (r i)) ≤
        19*inputLength (ns i) := by
    filter_upwards [hP,(inputLength_tendsto hns).eventually_ge_atTop 1] with i hi hp
    have hn : 1 ≤ inputLength (ns i) := by exact_mod_cast hp
    have hpos : 0<r i*(d i*b i) := by omega
    have hw : 0<d i*b i := Nat.pos_of_mul_pos_left hpos
    rw [← hi]
    exact (ticks_eq (b i) (d i) (r i) (Nat.pos_of_mul_pos_left hw) (Nat.pos_of_mul_pos_right hw)).le
  have h := RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => internalTicks (b i) (d i) (r i)) (fun i => schedule (sub i) (b i) (d i) (r i)) ht
  apply h.congr'
  filter_upwards [hP] with i hi
  simp only [machine,hi]

end TransposeFollowup.RawTernaryMatrixHorizontal
