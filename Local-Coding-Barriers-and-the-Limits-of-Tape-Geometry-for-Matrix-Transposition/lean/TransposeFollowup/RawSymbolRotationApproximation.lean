import TransposeFollowup.RawSymbolRotation
import TransposeFollowup.BankSymbolRotationApproximation
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Constant-error raw-native geometry for exact-symbol whole-bank
rotation, including S/s. The offset may depend arbitrarily on input size;
no small-row-width hypothesis is needed. -/
namespace TransposeFollowup.RawSymbolRotation
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

noncomputable def curve (P R : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  BankSymbolRotation.approximation P R (4*P) t x+
    RawBankProgram.ioCurve P (BankSymbolRotation.ticks P R) t x

theorem curve_cover (P R : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover ((81*81*81*9)*27) (curve P R t) H :=
  (BankSymbolRotation.approximation_cover P R (4*P) hH t).add
    (RawBankProgram.ioCurve_cover P (BankSymbolRotation.ticks P R) hH t)

theorem curve_error (P R : ℕ) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(workTraj (machine P R) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)).port t) : ℝ)-
      curve P R t x| ≤ 33 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode P w
  have hp : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode P w).1 t
  have hb := BankSymbolRotation.schedule_curve_error P R (4*P) w c x t
  rw [hp,Int.cast_zero,sub_zero] at hb
  have hi := RawBankProgram.ioPath_curve_error P (BankSymbolRotation.ticks P R) t x
  change |(workTraj (RawProgramShell.machine SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)
      (BankSymbolRotation.schedule P R)) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)).port t) : ℝ)-
      curve P R t x| ≤ 33
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode P
    (BankSymbolRotation.ticks P R) (BankSymbolRotation.schedule P R) (BankSymbolRotation.schedule_active P R)]
  simp only [curve,Int.cast_add]
  rw [abs_le] at hb hi ⊢
  constructor <;> linarith

theorem scaled_approximation {P : ℕ} (R : ℕ) (hP : 0 < P) {H : ℝ} (hH : 0 ≤ H)
    (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover ((81*81*81*9)*27) (fun x => curve P R t (P*x)/P) H ∧
    ∀ x : ℝ,
      |(workTraj (machine P R) w ⌊P*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode P (BankSymbolRotation.ticks P R)).port t) : ℝ)/P-
        curve P R t (P*x)/P| ≤ 33/(P : ℝ) := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨(curve_cover P R (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error P R w (P*x) t) hp.le

theorem error_vanishes {P : ℕ → ℕ} (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop) :
    Tendsto (fun i => 33/(P i : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (R : ℕ → ℕ)
    (hR : ∀ᶠ i in atTop, R i ≤ inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (inputLength (ns i)) (R i)).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => BankSymbolRotation.ticks (inputLength (ns i)) (R i))
    (fun i => BankSymbolRotation.schedule (inputLength (ns i)) (R i)) (C:=29)
  filter_upwards [hR] with i hi
  exact (ticks_eq _ _ hi).le

theorem shift_state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (right : ℕ → Bool) :
    Tendsto (fun i => (Nat.clog 2 ((machine (inputLength (ns i))
        (shiftOffset (right i) (inputLength (ns i)))).q+1) : ℝ)/inputLength (ns i)) atTop (𝓝 0) :=
  state_bits_vanish hns (fun i => shiftOffset (right i) (inputLength (ns i)))
    (Filter.Eventually.of_forall (fun i => shiftOffset_le (right i) (inputLength (ns i))))

end TransposeFollowup.RawSymbolRotation
