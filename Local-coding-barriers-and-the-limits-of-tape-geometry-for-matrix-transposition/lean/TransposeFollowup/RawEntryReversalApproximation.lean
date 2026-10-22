import TransposeFollowup.RawEntryReversal
import TransposeFollowup.ScheduledBankRowsMotion
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Complete raw-native geometry of entry reversal. Each row is a paid
11W-step block with net displacement(W,0); the outer rewind costs P.
The shared shell adds raw IO, including the actual frozen halted tail. -/
namespace TransposeFollowup.RawEntryReversal
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

noncomputable def curve (b d r : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  ScheduledBankRows.curve (r*(d*b)) 11 (4*(r*(d*b))) t x+
    RawBankProgram.ioCurve (r*(d*b)) (internalTicks b d r) t x

theorem curve_cover (b d r : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 243 (curve b d r t) H :=
  (ScheduledBankRows.curve_cover (r*(d*b)) 11 (4*(r*(d*b))) (by norm_num) hH t).add
    (RawBankProgram.ioCurve_cover (r*(d*b)) (internalTicks b d r) hH t)

theorem curve_error (b d r : ℕ) (hW : 0<d*b) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine b d r) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)-
      curve b d r t x| ≤ 12*(d*b : ℕ)+6 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode (r*(d*b)) w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode (r*(d*b)) w).1 t
  have hc : (update b d).cost+d*b=11*(d*b) := by
    simp only [update,BankBlockReversal.ticks_eq]
    omega
  have hb := ScheduledBankRows.schedule_curve_error (update b d) r 11 (4*(r*(d*b))) hc (by norm_num) hW w c x t
  rw [hpos,Int.cast_zero,sub_zero] at hb
  have hbody : |((trajectory (schedule b d r) w c
      (min (⌊x⌋₊-4*(r*(d*b))) (internalTicks b d r))).work.pos t : ℝ)-
      ScheduledBankRows.curve (r*(d*b)) 11 (4*(r*(d*b))) t x| ≤ 12*(d*b : ℕ)+2 := by
    simpa only [schedule,internalTicks,Nat.cast_ofNat,show (11 : ℝ)+1=12 by norm_num] using hb
  have hi := RawBankProgram.ioPath_curve_error (r*(d*b)) (internalTicks b d r) t x
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r) (schedule b d r))
    w ⌊x⌋₊ ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)-
    curve b d r t x| ≤ 12*(d*b : ℕ)+6
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode (r*(d*b))
    (internalTicks b d r) (schedule b d r) (schedule_active b d r)]
  simp only [curve,Int.cast_add]
  rw [abs_le] at hbody hi ⊢
  constructor <;> linarith

theorem scaled_approximation (b d r : ℕ) (hW : 0<d*b) (hP : 0<r*(d*b))
    {H : ℝ} (hH : 0 ≤ H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243 (fun x => curve b d r t ((r*(d*b) : ℕ)*x)/(r*(d*b) : ℕ)) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine b d r) w ⌊(r*(d*b) : ℕ)*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode (r*(d*b)) (internalTicks b d r)).port t) : ℝ)/(r*(d*b) : ℕ)-
        curve b d r t ((r*(d*b) : ℕ)*x)/(r*(d*b) : ℕ)| ≤ (12*(d*b : ℕ)+6 : ℝ)/(r*(d*b) : ℕ) := by
  have hp : (0 : ℝ)<(r*(d*b) : ℕ) := by exact_mod_cast hP
  refine ⟨(curve_cover b d r (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error b d r hW w ((r*(d*b) : ℕ)*x) t) hp.le

theorem error_vanishes {P W : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hW : Tendsto (fun i => (W i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (12*W i+6 : ℝ)/P i) atTop (𝓝 0) := by
  have hb : Tendsto (fun i => (6 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hW.const_mul (12 : ℝ)).add hb

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (b d r : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, r i*(d i*b i)=Transpose.inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (b i) (d i) (r i)).q+1) : ℝ)
      /Transpose.inputLength (ns i)) atTop (𝓝 0) := by
  have ht : ∀ᶠ i in atTop,
      RawProgramShell.ticks (Transpose.inputLength (ns i)) (internalTicks (b i) (d i) (r i)) ≤
        19*Transpose.inputLength (ns i) := by
    filter_upwards [hP] with i hi
    rw [← hi]
    exact (ticks_eq (b i) (d i) (r i)).le
  have h := RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => internalTicks (b i) (d i) (r i)) (fun i => schedule (b i) (d i) (r i)) ht
  apply h.congr'
  filter_upwards [hP] with i hi
  simp only [machine,hi]

end TransposeFollowup.RawEntryReversal
