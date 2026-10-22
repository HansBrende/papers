import TransposeFollowup.RawBlockReversal
import TransposeFollowup.BankBlockReversalApproximation
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Full raw-native block reversal: all-time physical head geometry,
including the halted tail, and sublinear state bits. The imported shell
retains the actual body path and accounts for every raw-IO step. -/
namespace TransposeFollowup.RawBlockReversal
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open SharedBankSymbols
set_option autoImplicit false

noncomputable def curve (B n : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  BankBlockReversal.approximation (n*B) (4*(n*B)) t x+
    RawBankProgram.ioCurve (n*B) (BankBlockReversal.ticks B n) t x

theorem curve_cover (B n : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 2187 (curve B n t) H :=
  (BankBlockReversal.approximation_cover (n*B) (4*(n*B)) hH t).add
    (RawBankProgram.ioCurve_cover (n*B) (BankBlockReversal.ticks B n) hH t)

theorem curve_error (B n : ℕ) (hB : 0<B) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine B n) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n)).port t) : ℝ)-
      curve B n t x| ≤ 5*B+8 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode (n*B) w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode (n*B) w).1 t
  have hb := BankBlockReversal.schedule_curve_error read write reset B n (4*(n*B)) hB w c x t
  rw [hpos,Int.cast_zero,sub_zero] at hb
  have hbody : |((trajectory (schedule B n) w c
      (min (⌊x⌋₊-4*(n*B)) (BankBlockReversal.ticks B n))).work.pos t : ℝ)-
      BankBlockReversal.approximation (n*B) (4*(n*B)) t x| ≤ 5*B+4 := hb
  have hi := RawBankProgram.ioPath_curve_error (n*B) (BankBlockReversal.ticks B n) t x
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n) (schedule B n))
    w ⌊x⌋₊ ((RawProgramShell.encoding SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n)).port t) : ℝ)-
    curve B n t x| ≤ 5*B+8
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode (n*B)
    (BankBlockReversal.ticks B n) (schedule B n) (schedule_active B n)]
  simp only [curve,Int.cast_add]
  rw [abs_le] at hbody hi ⊢
  constructor <;> linarith

theorem scaled_approximation (B n : ℕ) (hB : 0<B) (hP : 0<n*B)
    {H : ℝ} (hH : 0 ≤ H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 2187 (fun x => curve B n t ((n*B : ℕ)*x)/(n*B : ℕ)) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine B n) w ⌊(n*B : ℕ)*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode (n*B) (BankBlockReversal.ticks B n)).port t) : ℝ)/(n*B : ℕ)-
        curve B n t ((n*B : ℕ)*x)/(n*B : ℕ)| ≤ (5*B+8 : ℝ)/(n*B : ℕ) := by
  have hp : (0 : ℝ)<(n*B : ℕ) := by exact_mod_cast hP
  refine ⟨(curve_cover B n (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error B n hB w ((n*B : ℕ)*x) t) hp.le

theorem error_vanishes {P B : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hB : Tendsto (fun i => (B i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (5*B i+8 : ℝ)/P i) atTop (𝓝 0) := by
  have hb : Tendsto (fun i => (8 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hB.const_mul (5 : ℝ)).add hb

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (B n : ℕ → ℕ)
    (hP : ∀ᶠ i in atTop, n i*B i=Transpose.inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (B i) (n i)).q+1) : ℝ)
      /Transpose.inputLength (ns i)) atTop (𝓝 0) := by
  have ht : ∀ᶠ i in atTop,
      RawProgramShell.ticks (Transpose.inputLength (ns i)) (BankBlockReversal.ticks (B i) (n i)) ≤
        17*Transpose.inputLength (ns i) := by
    filter_upwards [hP] with i hi
    rw [← hi]
    exact (ticks_eq (B i) (n i)).le
  have h := RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => BankBlockReversal.ticks (B i) (n i)) (fun i => schedule (B i) (n i)) ht
  apply h.congr'
  filter_upwards [hP] with i hi
  simp only [machine,hi]

end TransposeFollowup.RawBlockReversal
