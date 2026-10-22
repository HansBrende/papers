import TransposeFollowup.RawUnitArithmeticNative
import TransposeFollowup.RawCarryBankApproximation
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Full native geometry/resources for whole-bank increment/decrement.
The error is twelve cells independent of input length, so it vanishes
after physical normalization. Raw IO and the halted tail are included. -/
namespace TransposeFollowup.RawUnitArithmetic
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
open Transpose Transpose.Tape Transpose.Tape.Impl
set_option autoImplicit false

theorem schedule_curve_error (sub : Bool) (P A : ℕ) (hP : 0 < P)
    (w : List Bool) (c : SharedRowBank.State) (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule sub P) w c (min (⌊x⌋₊-A) (RawCarryBank.ticks P))).work.pos t : ℝ)-
      c.work.pos t-RawCarryBank.approximation P A t x| ≤ 8 := by
  unfold schedule
  rw [NativeIOModeProduct.trajectory_eq]
  exact RawCarryBank.schedule_curve_error sub (!sub) P A hP w
    (NativeIOModeProduct.project SharedRowBank.rowModes c) x t

noncomputable def curve (P : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  RawCarryBank.approximation P (4*P) t x+RawBankProgram.ioCurve P (RawCarryBank.ticks P) t x

theorem curve_cover (P : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 2187 (curve P t) H :=
  (RawCarryBank.approximation_cover P (4*P) hH t).add
    (RawBankProgram.ioCurve_cover P (RawCarryBank.ticks P) hH t)

theorem curve_error (sub : Bool) (P : ℕ) (hP : 0 < P) (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(workTraj (machine sub P) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (RawCarryBank.ticks P)).port t) : ℝ)-
      curve P t x| ≤ 12 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode P w
  have hp : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode P w).1 t
  have hb := schedule_curve_error sub P (4*P) hP w c x t
  rw [hp,Int.cast_zero,sub_zero] at hb
  have hi := RawBankProgram.ioPath_curve_error P (RawCarryBank.ticks P) t x
  change |(workTraj (RawProgramShell.machine SharedRowBank.initialRowMode P (RawCarryBank.ticks P)
      (schedule sub P)) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (RawCarryBank.ticks P)).port t) : ℝ)-
      curve P t x| ≤ 12
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode P
    (RawCarryBank.ticks P) (schedule sub P) (schedule_active sub P)]
  simp only [curve,Int.cast_add]
  rw [abs_le] at hb hi ⊢
  constructor <;> linarith

theorem scaled_approximation (sub : Bool) {P : ℕ} (hP : 0 < P) {H : ℝ} (hH : 0 ≤ H)
    (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 2187 (fun x => curve P t (P*x)/P) H ∧
    ∀ x : ℝ,
      |(workTraj (machine sub P) w ⌊P*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode P (RawCarryBank.ticks P)).port t) : ℝ)/P-
        curve P t (P*x)/P| ≤ 12/(P : ℝ) := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨(curve_cover P (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error sub P hP w (P*x) t) hp.le

theorem error_vanishes {P : ℕ → ℕ} (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop) :
    Tendsto (fun i => 12/(P i : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (sub : ℕ → Bool) :
    Tendsto (fun i => (Nat.clog 2 ((machine (sub i) (inputLength (ns i))).q+1) : ℝ)
      /inputLength (ns i)) atTop (𝓝 0) := by
  apply RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => RawCarryBank.ticks (inputLength (ns i))) (fun i => schedule (sub i) (inputLength (ns i)))
    (C:=17)
  filter_upwards [(inputLength_tendsto hns).eventually_ge_atTop 1] with i hi
  have hp : 0 < inputLength (ns i) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) hi)
  exact (raw_ticks_eq _ hp).le

end TransposeFollowup.RawUnitArithmetic
