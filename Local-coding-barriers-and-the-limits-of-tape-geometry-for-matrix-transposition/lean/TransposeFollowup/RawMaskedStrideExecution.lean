import TransposeFollowup.ScheduledRawOutput
import TransposeFollowup.ScheduledSegments
import TransposeFollowup.MaskedStrideInterfaces

/-! The complete raw-input executor, with every pass in a single public
native clock. Input loading, two bank rewinds, scratch erasure/rewind and
raw output are included in its time. Functional correctness is connected
separately to the already proved stride recurrence. -/
namespace TransposeFollowup.RawMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO ScheduledTapeAction
open MaskedStrideCell (Mode State)
set_option autoImplicit false

def initial : State := ⟨NativeMicrocode.blankConfig (false,false),0,[]⟩

def prepared (P : ℕ) (w : List Bool) : State :=
  rewind 0 w (ScheduledRawInput.loaded w initial P) P

def processed (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) : State :=
  MaskedStrideScan.result isPrefix mask P S w (prepared P w)

def cleared (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) : State :=
  rewind 1 w (erase 1 w (processed isPrefix mask P S w) S) S

def ready (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) : State :=
  rewind 0 w (cleared isPrefix mask P S w) P

def result (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) (w : List Bool) : State :=
  ScheduledRawOutput.emitted w (ready isPrefix mask P S w) P

def ticks (P S : ℕ) : ℕ := 3*P+(P+(MaskedStrideScan.ticks P S+(S+(S+(P+3*P)))))

def schedule (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) : ℕ → NativeIO.Program (Fin 2) Mode :=
  append ScheduledRawInput.schedule
    (append (fun _ => action 0 ⟨none,.left⟩)
      (append (MaskedStrideScan.schedule isPrefix mask P S)
        (append (fun _ => action 1 ⟨some .blank,.right⟩)
          (append (fun _ => action 1 ⟨none,.left⟩)
            (append (fun _ => action 0 ⟨none,.left⟩) ScheduledRawOutput.schedule P) S) S)
        (MaskedStrideScan.ticks P S)) P) (3*P)

theorem schedule_active (isPrefix : Bool) (mask : ℕ → Bool) (P S i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask P S i) c := by
  unfold schedule
  apply append_active
  · intro j
    exact ScheduledRawInput.cell_active _ _
  · intro j
    apply append_active
    · intro _; exact ScheduledTapeAction.active _ _ _
    · intro j
      apply append_active
      · intro j; exact MaskedStrideScan.schedule_active _ _ _ _ j _
      · intro j
        apply append_active
        · intro _; exact ScheduledTapeAction.active _ _ _
        · intro j
          apply append_active
          · intro _; exact ScheduledTapeAction.active _ _ _
          · intro j
            apply append_active
            · intro _; exact ScheduledTapeAction.active _ _ _
            · intro _; exact ScheduledRawOutput.cell_active _ _

theorem schedule_exact (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) : trajectory (schedule isPrefix mask P S) w initial (ticks P S)=result isPrefix mask P S w := by
  simp only [schedule,ticks,append_exact,ScheduledRawInput.schedule_exact,
    MaskedStrideScan.schedule_exact isPrefix mask P hS,ScheduledRawOutput.schedule_exact]
  rfl

theorem ticks_le (P S : ℕ) (hSP : S ≤ P) : ticks P S ≤ 18*P := by
  have h := MaskedStrideScan.ticks_le P S hSP
  unfold ticks
  omega

noncomputable def encoding (P S : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 2)
  ((⟨0,by omega⟩,(false,false)) : Fin (ticks P S+1) × Mode)

noncomputable def machine (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) :=
  NativeIO.machine (encoding P S) (program (schedule isPrefix mask P S) (ticks P S))

theorem native_complete (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ} (hS : 0<S)
    (w : List Bool) :
    Transpose.stepN (machine isPrefix mask P S) w (ticks P S) (Transpose.init (machine isPrefix mask P S))=
      some ((lift (⟨ticks P S,by omega⟩ : Fin (ticks P S+1)) (result isPrefix mask P S w)).denote
        (encoding P S) (program (schedule isPrefix mask P S) (ticks P S))) ∧
    Transpose.step (machine isPrefix mask P S) w
      ((lift (⟨ticks P S,by omega⟩ : Fin (ticks P S+1)) (result isPrefix mask P S w)).denote
        (encoding P S) (program (schedule isPrefix mask P S) (ticks P S)))=none := by
  have h := native_run_and_halt (encoding P S) (schedule isPrefix mask P S) w initial
    (fun i _ => schedule_active isPrefix mask P S i _)
  rw [schedule_exact isPrefix mask P hS] at h
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P S+1)) initial).denote
      (encoding P S) (program (schedule isPrefix mask P S) (ticks P S))=
      Transpose.init (machine isPrefix mask P S) :=
    NativeIO.blank_denote (encoding P S) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  exact h

theorem fixed_resources (isPrefix : Bool) (mask : ℕ → Bool) (P S : ℕ) :
    (machine isPrefix mask P S).k=2 ∧ (machine isPrefix mask P S).g+1=5 ∧
    (machine isPrefix mask P S).q+1=(ticks P S+1)*4 := by
  refine ⟨rfl,rfl,?_⟩
  exact native_state_count (schedule isPrefix mask P S) (ticks P S) (false,false)

end TransposeFollowup.RawMaskedStride
