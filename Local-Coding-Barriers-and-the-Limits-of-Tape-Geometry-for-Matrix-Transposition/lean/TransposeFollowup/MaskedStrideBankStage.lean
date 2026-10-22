import TransposeFollowup.RawMaskedStrideCorrectness

/-! A reusable internal-bank stage. The scan, scratch clearing and both
head resets are actual scheduled actions. The bank may start at arbitrary
head coordinates, with arbitrary local mode and external IO fields. -/
namespace TransposeFollowup.MaskedStrideBankStage
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State bit)
set_option autoImplicit false

def ticks (P S : ℕ) : ℕ := MaskedStrideScan.ticks P S+(S+(S+P))

def schedule (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append (MaskedStrideScan.schedule isPrefix mask P S)
    (append (fun _ => action 1 ⟨some .blank,.right⟩)
      (append (fun _ => action 1 ⟨none,.left⟩) (fun _ => action 0 ⟨none,.left⟩) S) S)
    (MaskedStrideScan.ticks P S)

def result (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) (c : State) : State :=
  rewind 0 w (rewind 1 w (erase 1 w (MaskedStrideScan.result isPrefix mask P S w c) S) S) P

theorem schedule_active (isPrefix : Bool) (mask : ℕ → Bool) (P S i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask P S i) c := by
  unfold schedule
  apply append_active
  · intro j; exact MaskedStrideScan.schedule_active _ _ _ _ j _
  · intro j
    apply append_active
    · intro _; exact ScheduledTapeAction.active _ _ _
    · intro j
      apply append_active <;> intro _ <;> exact ScheduledTapeAction.active _ _ _

theorem schedule_exact (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) :
    trajectory (schedule isPrefix mask P S) w c (ticks P S) = result isPrefix mask P S w c := by
  simp only [schedule,ticks,append_exact,MaskedStrideScan.schedule_exact isPrefix mask P hS]
  rfl

theorem ticks_le (P S : ℕ) (hSP : S ≤ P) : ticks P S ≤ 11*P := by
  have h := MaskedStrideScan.ticks_le P S hSP
  unfold ticks
  omega

/-- The output again satisfies the scratch and head interface for another
stage. Only the work bank changes; no external output is used as storage. -/
theorem result_spec (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0 < S)
    (w : List Bool) (c : State) (hblank : ∀ z, cells c 1 z = .blank) :
    (∀ t, (result isPrefix mask P S w c).work.pos t = c.work.pos t) ∧
    (∀ j < P, cells (result isPrefix mask P S w c) 0 (c.work.pos 0+j) =
      .data (MaskedStrideScan.value isPrefix mask (MaskedStrideScan.input c) S j)) ∧
    (∀ z, cells (result isPrefix mask P S w c) 1 z = .blank) ∧
    (result isPrefix mask P S w c).inputPos = c.inputPos ∧
    (result isPrefix mask P S w c).outRev = c.outRev := by
  have hz : ∀ j < S, bit (cells c 1 (c.work.pos 1+j)) = false := by
    intro j _; rw [hblank]; rfl
  have hs := MaskedStrideScan.result_correct isPrefix mask P hS w c hz
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    fin_cases t <;> simp [result,rewind_position,erase_position,hs.1,hs.2.1]
  · intro j hj
    simpa only [result,rewind_cells,erase_cells,show (0 : Fin 2) ≠ 1 by decide,
      false_and,ite_false] using hs.2.2.1 j hj
  · intro z
    rw [result,rewind_cells,rewind_cells,erase_cells,hs.2.1]
    simp only [true_and]
    split_ifs with h
    · rfl
    · exact (MaskedStrideScan.result_scratch_outside isPrefix mask P hS w c hz z (by omega)).trans (hblank z)
  · have hi := MaskedStrideScan.result_io isPrefix mask P S w c
    have he := erase_io 1 w (MaskedStrideScan.result isPrefix mask P S w c) S
    have hr := rewind_io 1 w (erase 1 w (MaskedStrideScan.result isPrefix mask P S w c) S) S
    have hb := rewind_io 0 w (rewind 1 w (erase 1 w (MaskedStrideScan.result isPrefix mask P S w c) S) S) P
    exact ⟨hb.1.trans (hr.1.trans (he.1.trans hi.1)),hb.2.trans (hr.2.trans (he.2.trans hi.2))⟩

/-- This is exactly the internal part of the verified raw executor. -/
theorem prepared_result (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) :
    result isPrefix mask P S w (RawMaskedStride.prepared P w) =
      RawMaskedStride.ready isPrefix mask P S w := rfl

end TransposeFollowup.MaskedStrideBankStage
