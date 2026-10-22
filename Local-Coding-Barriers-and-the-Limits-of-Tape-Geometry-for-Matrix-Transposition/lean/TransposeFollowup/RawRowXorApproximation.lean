import TransposeFollowup.RawRowXor
import TransposeFollowup.StrideStageApproximation
import TransposeFollowup.RawShellNativeMotion
import TransposeFollowup.RawShellResources

/-! Reuse the small-stride curve of the existing scan on the shared
controller, then add the paid raw IO shell. The physical estimate includes
every prefix and the halted tail. No new scan or path approximation is used. -/
namespace TransposeFollowup.RawRowXor
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

theorem schedule_position (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W)
    (w : List Bool) (c : SharedRowBank.State) (n : ℕ) (t : Fin 2) :
    (trajectory (schedule isPrefix P W) w c (min n (MaskedStrideBankStage.ticks P W))).work.pos t=
      c.work.pos t+MaskedStrideBankStage.path P W t n := by
  unfold schedule
  rw [NativeIOModeProduct.trajectory_eq]
  change (trajectory (MaskedStrideBankStage.schedule isPrefix (fun _ => true) P W) w
    (NativeIOModeProduct.project SharedRowBank.ioModes c)
    (min n (MaskedStrideBankStage.ticks P W))).work.pos t= _
  rw [MaskedStrideBankStage.schedule_position isPrefix (fun _ => true) P hW w _ _
    (Nat.min_le_right _ _),MaskedStrideBankStage.path_frozen]
  rfl

theorem schedule_curve_error (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W)
    (A : ℕ) (w : List Bool) (c : SharedRowBank.State) (x : ℝ) (t : Fin 2) :
    |((trajectory (schedule isPrefix P W) w c
      (min (⌊x⌋₊-A) (MaskedStrideBankStage.ticks P W))).work.pos t : ℝ)-c.work.pos t-
      MaskedStrideBankStage.smallApproximation P A t x| ≤ 7*(W : ℝ)+2 := by
  rw [schedule_position isPrefix P hW,Int.cast_add,add_sub_cancel_left]
  exact MaskedStrideBankStage.smallApproximation_error P hW A t x

noncomputable def curve (P W : ℕ) (t : Fin 2) (x : ℝ) : ℝ :=
  MaskedStrideBankStage.smallApproximation P (4*P) t x+
    RawBankProgram.ioCurve P (MaskedStrideBankStage.ticks P W) t x

theorem curve_cover (P W : ℕ) {H : ℝ} (hH : 0 ≤ H) (t : Fin 2) :
    HasAffineIntervalCover 243 (curve P W t) H :=
  (MaskedStrideBankStage.smallApproximation_cover P (4*P) hH t).add
    (RawBankProgram.ioCurve_cover P (MaskedStrideBankStage.ticks P W) hH t)

theorem curve_error (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W)
    (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine isPrefix P W) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)).port t) : ℝ)-
      curve P W t x| ≤ 7*(W : ℝ)+6 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode P w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode P w).1 t
  have hb := schedule_curve_error isPrefix P hW (4*P) w c x t
  rw [hpos,Int.cast_zero,sub_zero] at hb
  have hi := RawBankProgram.ioPath_curve_error P (MaskedStrideBankStage.ticks P W) t x
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)
      (schedule isPrefix P W)) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)).port t) : ℝ)-
      curve P W t x| ≤ 7*(W : ℝ)+6
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode P
    (MaskedStrideBankStage.ticks P W) (schedule isPrefix P W) (schedule_active isPrefix P W)]
  simp only [curve,Int.cast_add]
  rw [abs_le] at hb hi ⊢
  constructor <;> linarith

theorem scaled_approximation (isPrefix : Bool) {P W : ℕ} (hP : 0 < P) (hW : 0 < W)
    {H : ℝ} (hH : 0 ≤ H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243 (fun x => curve P W t (P*x)/P) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine isPrefix P W) w ⌊P*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)).port t) : ℝ)/P-
        curve P W t (P*x)/P| ≤ (7*W+6 : ℝ)/P := by
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  refine ⟨(curve_cover P W (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error isPrefix P hW w (P*x) t) hp.le

theorem error_vanishes {P W : ℕ → ℕ}
    (hP : Tendsto (fun i => (P i : ℝ)) atTop atTop)
    (hW : Tendsto (fun i => (W i : ℝ)/P i) atTop (𝓝 0)) :
    Tendsto (fun i => (7*W i+6 : ℝ)/P i) atTop (𝓝 0) := by
  have hb : Tendsto (fun i => (6 : ℝ)/P i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hP
  simpa only [mul_zero,add_zero,add_div,mul_div_assoc] using (hW.const_mul (7 : ℝ)).add hb

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (isPrefix : ℕ → Bool) (W : ℕ → ℕ)
    (hWP : ∀ᶠ i in atTop, W i ≤ Transpose.inputLength (ns i)) :
    Tendsto (fun i => (Nat.clog 2 ((machine (isPrefix i) (Transpose.inputLength (ns i)) (W i)).q+1) : ℝ)
      /Transpose.inputLength (ns i)) atTop (𝓝 0) := by
  apply RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => MaskedStrideBankStage.ticks (Transpose.inputLength (ns i)) (W i))
    (fun i => schedule (isPrefix i) (Transpose.inputLength (ns i)) (W i))
  filter_upwards [hWP] with i hi
  exact ticks_linear _ _ hi

end TransposeFollowup.RawRowXor
