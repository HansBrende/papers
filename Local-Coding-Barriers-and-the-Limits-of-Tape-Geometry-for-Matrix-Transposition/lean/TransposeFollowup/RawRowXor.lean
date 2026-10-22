import TransposeFollowup.RawRowProgram
import TransposeFollowup.MaskedStrideBankStage

/-! The integer palette's row XOR prefix/difference is the existing
masked-stride scan with mask true and stride equal to the row width.
Only the controller embedding is new; every instruction, cleanup step and
raw IO cost is reused. The symbol transformer explicitly decodes bits and
is not a ternary arithmetic operation. -/
namespace TransposeFollowup.RawRowXor
open Classical FixedTapeCompiler ScheduledNativeIO
open CopyMachine (Sym)
open MaskedStrideCell (bit)
set_option autoImplicit false

def bitValue (isPrefix : Bool) (W : ℕ) (x : ℕ → Bool) (j : ℕ) : Bool :=
  MaskedStrideScan.value isPrefix (fun _ => true) x W j

theorem bitValue_first (isPrefix : Bool) {W : ℕ} (hW : 0 < W)
    (x : ℕ → Bool) (j : ℕ) (hj : j < W) : bitValue isPrefix W x j=x j := by
  rw [bitValue,MaskedStrideScan.value_recurrence isPrefix (fun _ => true) x hW]
  simp [hj,MaskedStrideCell.output]

theorem bitValue_next (isPrefix : Bool) {W : ℕ} (hW : 0 < W)
    (x : ℕ → Bool) (k j : ℕ) :
    bitValue isPrefix W x ((k+1)*W+j)=Bool.xor (x ((k+1)*W+j))
      (if isPrefix then bitValue isPrefix W x (k*W+j) else x (k*W+j)) := by
  have hn : ¬(k+1)*W+j < W := by nlinarith
  have hs : (k+1)*W+j-W=k*W+j := by rw [Nat.add_mul]; omega
  rw [bitValue,MaskedStrideScan.value_recurrence isPrefix (fun _ => true) x hW]
  simp only [hn,ite_false,hs,MaskedStrideCell.output,Bool.true_and,bitValue]

def value (isPrefix : Bool) (W : ℕ) (x : ℕ → Sym Bool) (j : ℕ) : Sym Bool :=
  .data (bitValue isPrefix W (fun i => bit (x i)) j)

theorem value_congr (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W) :
    BankWord.Congruent P (value isPrefix W) := by
  intro x y hxy j hj
  apply congrArg Sym.data
  exact MaskedStrideScan.value_congr_upto isPrefix (fun _ => true) _ _ hW j
    (fun i hi => congrArg bit (hxy i (by omega)))

noncomputable def schedule (isPrefix : Bool) (P W i : ℕ) : NativeIO.Program (Fin 2) SharedRowBank.Mode :=
  NativeIOModeProduct.program SharedRowBank.ioModes
    (MaskedStrideBankStage.schedule isPrefix (fun _ => true) P W i)

theorem schedule_active (isPrefix : Bool) (P W i : ℕ) (c : SharedRowBank.State) :
    NativeIO.Active (schedule isPrefix P W i) c :=
  NativeIOModeProduct.active SharedRowBank.ioModes _
    (MaskedStrideBankStage.schedule_active isPrefix (fun _ => true) P W i) c

theorem represents (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W)
    (w : List Bool) (c : SharedRowBank.State) (hc : BankWord.symbols.clean c) :
    BankWord.Represents BankWord.symbols P c
      (trajectory (schedule isPrefix P W) w c (MaskedStrideBankStage.ticks P W))
      (value isPrefix W (BankWord.input BankWord.symbols c)) := by
  unfold schedule
  rw [NativeIOModeProduct.trajectory_eq,MaskedStrideBankStage.schedule_exact isPrefix (fun _ => true) P hW]
  exact MaskedStrideBankStage.result_spec isPrefix (fun _ => true) P hW w
    (NativeIOModeProduct.project SharedRowBank.ioModes c) hc

def ticks (P W : ℕ) : ℕ := RawProgramShell.ticks P (MaskedStrideBankStage.ticks P W)

noncomputable def machine (isPrefix : Bool) (P W : ℕ) :=
  RawProgramShell.machine SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)
    (schedule isPrefix P W)

def output (isPrefix : Bool) (P W : ℕ) (w : List Bool) : List Bool :=
  (List.range P).map (bitValue isPrefix W (fun i => ScheduledRawInput.inputBit w i))

theorem ticks_linear (P W : ℕ) (hWP : W ≤ P) : ticks P W ≤ 18*P := by
  have h := MaskedStrideBankStage.ticks_le P W hWP
  rw [ticks,RawProgramShell.ticks_eq]
  omega

theorem native_correct (isPrefix : Bool) (P : ℕ) {W : ℕ} (hW : 0 < W) (w : List Bool) :
    ∃ d : Transpose.Config (machine isPrefix P W),
      Transpose.stepN (machine isPrefix P W) w (ticks P W) (Transpose.init (machine isPrefix P W))=some d ∧
      Transpose.step (machine isPrefix P W) w d=none ∧ d.outRev=(output isPrefix P W w).reverse ∧
      ∀ z, d.work ((RawProgramShell.encoding SharedRowBank.initialRowMode P
        (MaskedStrideBankStage.ticks P W)).port 1) z=0 := by
  exact RawProgramShell.native_correct SharedRowBank.initialRowMode P (MaskedStrideBankStage.ticks P W)
    (schedule isPrefix P W) (schedule_active isPrefix P W) (value isPrefix W)
    (value_congr isPrefix P hW) (fun w c hc => represents isPrefix P hW w c hc) w

theorem resources (isPrefix : Bool) (P W : ℕ) :
    (machine isPrefix P W).k=2 ∧ (machine isPrefix P W).g+1=5 ∧
      (machine isPrefix P W).q+1=(ticks P W+1)*200 := by
  have h := RawProgramShell.fixed_resources SharedRowBank.initialRowMode P
    (MaskedStrideBankStage.ticks P W) (schedule isPrefix P W)
  rw [show Fintype.card CoupledRowCell.Mode=50 by decide +kernel] at h
  exact h

end TransposeFollowup.RawRowXor
