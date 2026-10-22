import TransposeFollowup.RawMaskedStrideExecution

/-! Correct raw output and complete scratch erasure for the paid executor.
The exact stride recurrence is evaluated on the external input, not on an
assumed prepared bank. All hypotheses of the bank theorem are discharged. -/
namespace TransposeFollowup.RawMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
open CopyMachine (Sym)
set_option autoImplicit false

theorem initial_cells (t : Fin 2) (z : ℤ) : cells initial t z=.blank := AbsoluteTape.blank_cells _ _

theorem prepared_position (P : ℕ) (w : List Bool) (t : Fin 2) : (prepared P w).work.pos t=0 := by
  simp [prepared,rewind_position,ScheduledRawInput.loaded_position,initial,NativeMicrocode.blankConfig]

theorem prepared_io (P : ℕ) (w : List Bool) : (prepared P w).inputPos=P ∧ (prepared P w).outRev=[] := by
  have h := rewind_io 0 w (ScheduledRawInput.loaded w initial P) P
  have hload := ScheduledRawInput.loaded_io w initial P
  exact ⟨h.1.trans (by simpa [initial] using hload.1),h.2.trans hload.2⟩

theorem prepared_scratch (P : ℕ) (w : List Bool) (z : ℤ) : cells (prepared P w) 1 z=.blank := by
  rw [prepared,rewind_cells,ScheduledRawInput.loaded_outside w initial P 1 z (Or.inl (by decide)),initial_cells]

theorem prepared_zero (P S : ℕ) (w : List Bool) :
    ∀ j < S, bit (cells (prepared P w) 1 ((prepared P w).work.pos 1+j))=false := by
  intro j _
  rw [prepared_scratch]
  rfl

theorem prepared_input (P : ℕ) (w : List Bool) (j : ℕ) (hj : j<P) :
    MaskedStrideScan.input (prepared P w) j=ScheduledRawInput.inputBit w j := by
  unfold MaskedStrideScan.input
  change bit (cells (prepared P w) 0 ((prepared P w).work.pos 0+j))=_
  rw [prepared_position,zero_add,prepared,rewind_cells]
  simpa [initial,NativeMicrocode.blankConfig,bit] using
    congrArg bit (ScheduledRawInput.loaded_written w initial P j hj)

theorem processed_correct (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) :
    (processed isPrefix mask P S w).work.pos 0=P ∧ (processed isPrefix mask P S w).work.pos 1=0 ∧
    ∀ j < P, cells (processed isPrefix mask P S w) 0 j=
      .data (MaskedStrideScan.value isPrefix mask (fun i : ℕ => ScheduledRawInput.inputBit w i) S j) := by
  have h := MaskedStrideScan.result_correct isPrefix mask P hS w (prepared P w) (prepared_zero P S w)
  refine ⟨?_,?_,?_⟩
  · simpa [processed,prepared_position] using h.1
  · simpa [processed,prepared_position] using h.2.1
  · intro j hj
    have hv := MaskedStrideScan.value_congr_upto isPrefix mask (MaskedStrideScan.input (prepared P w))
      (fun i : ℕ => ScheduledRawInput.inputBit w i) hS j
      (fun i hi => prepared_input P w i (by omega))
    simpa [processed,prepared_position,hv] using h.2.2.1 j hj

theorem processed_io (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) :
    (processed isPrefix mask P S w).inputPos=P ∧ (processed isPrefix mask P S w).outRev=[] := by
  have h := MaskedStrideScan.result_io isPrefix mask P S w (prepared P w)
  exact ⟨h.1.trans (prepared_io P w).1,h.2.trans (prepared_io P w).2⟩

theorem processed_scratch_outside (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (z : ℤ) (hz : z<0 ∨ (S : ℤ) ≤ z) :
    cells (processed isPrefix mask P S w) 1 z=.blank := by
  have h := MaskedStrideScan.result_scratch_outside isPrefix mask P hS w (prepared P w)
    (prepared_zero P S w) z (by simpa [prepared_position] using hz)
  exact h.trans (prepared_scratch P w z)

theorem cleared_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) :
    (cleared isPrefix mask P S w).work.pos 0=P ∧ (cleared isPrefix mask P S w).work.pos 1=0 := by
  have h := processed_correct isPrefix mask P hS w
  constructor <;> simp [cleared,rewind_position,erase_position,h.1,h.2.1]

theorem cleared_bank (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) (z : ℤ) :
    cells (cleared isPrefix mask P S w) 0 z=cells (processed isPrefix mask P S w) 0 z := by
  simp [cleared,rewind_cells,erase_cells]

theorem cleared_scratch (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (z : ℤ) : cells (cleared isPrefix mask P S w) 1 z=.blank := by
  rw [cleared,rewind_cells,erase_cells,(processed_correct isPrefix mask P hS w).2.1]
  simp only [zero_add,true_and]
  split_ifs with hz
  · rfl
  · exact processed_scratch_outside isPrefix mask P hS w z (by omega)

theorem cleared_io (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) :
    (cleared isPrefix mask P S w).inputPos=P ∧ (cleared isPrefix mask P S w).outRev=[] := by
  have h := rewind_io 1 w (erase 1 w (processed isPrefix mask P S w) S) S
  have he := erase_io 1 w (processed isPrefix mask P S w) S
  have hp := processed_io isPrefix mask P S w
  exact ⟨h.1.trans (he.1.trans hp.1),h.2.trans (he.2.trans hp.2)⟩

theorem ready_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (t : Fin 2) : (ready isPrefix mask P S w).work.pos t=0 := by
  have h := cleared_position isPrefix mask P hS w
  fin_cases t <;> simp [ready,rewind_position,h.1,h.2]

theorem ready_io (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) :
    (ready isPrefix mask P S w).inputPos=P ∧ (ready isPrefix mask P S w).outRev=[] := by
  have h := rewind_io 0 w (cleared isPrefix mask P S w) P
  have hc := cleared_io isPrefix mask P S w
  exact ⟨h.1.trans hc.1,h.2.trans hc.2⟩

theorem ready_bank (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (j : ℕ) (hj : j<P) : cells (ready isPrefix mask P S w) 0 j=
      .data (MaskedStrideScan.value isPrefix mask (fun i : ℕ => ScheduledRawInput.inputBit w i) S j) := by
  rw [ready,rewind_cells,cleared_bank]
  exact (processed_correct isPrefix mask P hS w).2.2 j hj

def outputWord (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) : List Bool :=
  (List.range P).map (fun j : ℕ => MaskedStrideScan.value isPrefix mask
    (fun i : ℕ => ScheduledRawInput.inputBit w i) S j)

theorem result_output (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) : (result isPrefix mask P S w).outRev=(outputWord isPrefix mask P S w).reverse := by
  rw [result,ScheduledRawOutput.emitted_output,ready_position isPrefix mask P hS w 0,
    (ready_io isPrefix mask P S w).2,List.append_nil]
  simp only [zero_add]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [ready_bank isPrefix mask P hS w j (List.mem_range.mp hj)]
  rfl

theorem result_scratch (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) (z : ℤ) : cells (result isPrefix mask P S w) 1 z=.blank := by
  rw [result,ScheduledRawOutput.emitted_cells,ready,rewind_cells]
  exact cleared_scratch isPrefix mask P hS w z

theorem native_correct (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (hSP : S ≤ P) (w : List Bool) :
    ∃ c : Transpose.Config (machine isPrefix mask P S),
      ticks P S ≤ 18*P ∧
      Transpose.stepN (machine isPrefix mask P S) w (ticks P S) (Transpose.init (machine isPrefix mask P S))=some c ∧
      Transpose.step (machine isPrefix mask P S) w c=none ∧
      c.outRev=(outputWord isPrefix mask P S w).reverse ∧
      ∀ z, c.work ((encoding P S).port 1) z=0 := by
  refine ⟨(lift (⟨ticks P S,by omega⟩ : Fin (ticks P S+1)) (result isPrefix mask P S w)).denote
    (encoding P S) (program (schedule isPrefix mask P S) (ticks P S)),ticks_le P S hSP,
    (native_complete isPrefix mask P hS w).1,(native_complete isPrefix mask P hS w).2,
    result_output isPrefix mask P hS w,?_⟩
  intro z
  change NativeMicrocode.symbolCode
    (cells (result isPrefix mask P S w) ((encoding P S).port.symm ((encoding P S).port 1)) z)=0
  rw [Equiv.symm_apply_apply,result_scratch isPrefix mask P hS w]
  rfl

end TransposeFollowup.RawMaskedStride
