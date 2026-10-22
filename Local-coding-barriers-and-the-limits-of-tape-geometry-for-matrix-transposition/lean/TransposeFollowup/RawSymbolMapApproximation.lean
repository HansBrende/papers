import TransposeFollowup.RawSymbolMap
import TransposeFollowup.RawEntryReversalApproximation

/-! Public symbol maps reuse the indexed one-cell block bound and the
existing 11-step reference curve. Error is constant even when the public
tables change at every position; all raw IO and frozen halt samples count. -/
namespace TransposeFollowup.RawSymbolMap
open Classical Filter Topology FixedTapeCompiler ScheduledNativeIO AffineMotion
set_option autoImplicit false

theorem curve_error (f : ℕ → CopyMachine.Sym Bool → CopyMachine.Sym Bool) (P : ℕ)
    (w : List Bool) (x : ℝ) (t : Fin 2) :
    |(Transpose.Tape.workTraj (machine f P) w ⌊x⌋₊
      ((RawProgramShell.encoding SharedRowBank.initialRowMode P (internalTicks f P)).port t) : ℝ)-
      RawEntryReversal.curve 1 1 P t x| ≤ 18 := by
  let c := RawProgramShell.prepared SharedRowBank.initialRowMode P w
  have hpos : c.work.pos t=0 :=
    (ScheduledModeRawIO.prepared_spec (Equiv.refl SharedRowBank.Mode) SharedRowBank.initialRowMode P w).1 t
  have hbody := IndexedBankRows.schedule_curve_error (update f) P 11 (4*P)
    (update_cost f) (by norm_num) (by norm_num) w c x t
  rw [hpos,Int.cast_zero,sub_zero] at hbody
  have hc : |((trajectory (schedule f P) w c
      (min (⌊x⌋₊-4*P) (internalTicks f P))).work.pos t : ℝ)-
      ScheduledBankRows.curve P 11 (4*P) t x| ≤ 14 := by
    simpa only [schedule,internalTicks,Nat.mul_one,Nat.cast_one,Nat.cast_ofNat,
      mul_one,show (11 : ℝ)+1+2=14 by norm_num] using hbody
  have hi := RawBankProgram.ioPath_curve_error P (internalTicks f P) t x
  have hN : internalTicks f P=RawEntryReversal.internalTicks 1 1 P := by
    rw [internal_ticks_eq,RawEntryReversal.internal_ticks_eq,Nat.mul_one]
  change |(Transpose.Tape.workTraj
    (RawProgramShell.machine SharedRowBank.initialRowMode P (internalTicks f P) (schedule f P))
    w ⌊x⌋₊ ((RawProgramShell.encoding SharedRowBank.initialRowMode P (internalTicks f P)).port t) : ℝ)-
    RawEntryReversal.curve 1 1 P t x| ≤ 18
  rw [RawProgramShell.workTraj_decomposition SharedRowBank.initialRowMode P
    (internalTicks f P) (schedule f P) (schedule_active f P)]
  simp only [RawEntryReversal.curve,Nat.mul_one,← hN,Int.cast_add]
  rw [abs_le] at hc hi ⊢
  constructor <;> linarith

theorem scaled_approximation (f : ℕ → CopyMachine.Sym Bool → CopyMachine.Sym Bool)
    (P : ℕ) (hP : 0<P) {H : ℝ} (hH : 0 ≤ H) (w : List Bool) (t : Fin 2) :
    HasAffineIntervalCover 243
      (fun x => RawEntryReversal.curve 1 1 P t (P*x)/P) H ∧
    ∀ x : ℝ,
      |(Transpose.Tape.workTraj (machine f P) w ⌊P*x⌋₊
        ((RawProgramShell.encoding SharedRowBank.initialRowMode P (internalTicks f P)).port t) : ℝ)/P-
        RawEntryReversal.curve 1 1 P t (P*x)/P| ≤ 18/P := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  refine ⟨(RawEntryReversal.curve_cover 1 1 P (mul_nonneg hp.le hH) t).rescale hp,?_⟩
  intro x
  rw [← sub_div,abs_div,abs_of_pos hp]
  exact div_le_div_of_nonneg_right (curve_error f P w (P*x) t) hp.le

theorem state_bits_vanish {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    (f : ℕ → ℕ → CopyMachine.Sym Bool → CopyMachine.Sym Bool) :
    Tendsto (fun i => (Nat.clog 2 ((machine (f i) (Transpose.inputLength (ns i))).q+1) : ℝ)
      /Transpose.inputLength (ns i)) atTop (𝓝 0) := by
  exact RawProgramShell.state_bits_vanish hns SharedRowBank.initialRowMode
    (fun i => internalTicks (f i) (Transpose.inputLength (ns i)))
    (fun i => schedule (f i) (Transpose.inputLength (ns i)))
    (Filter.Eventually.of_forall (fun i => (ticks_eq (f i) (Transpose.inputLength (ns i))).le))

end TransposeFollowup.RawSymbolMap
