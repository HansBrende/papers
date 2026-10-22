import TransposeFollowup.RawMaskedStrideScheduleMotion
import TransposeFollowup.MaskedStrideRamps
import TransposeFollowup.ExcursionPulse

/-! The complete raw-input native head paths, at every integer time,
including the frozen halted tail. All setup, scratch erasure, rewinds and
output moves appear explicitly in the ramp formulas. -/
namespace TransposeFollowup.RawMaskedStride
open Classical FixedTapeCompiler ScheduledNativeIO
set_option autoImplicit false

def bankPath (P S n : ℕ) : ℤ :=
  (min ((n+1)/3) P : ℕ)-cappedRamp P (3*P) n+
    (MaskedStrideScan.bankPosition P S (n-4*P) : ℕ)-
    cappedRamp P (4*P+MaskedStrideScan.ticks P S+2*S) n+
    (MaskedStrideScan.rise P (5*P+MaskedStrideScan.ticks P S+2*S) n : ℕ)

def scratchPath (P S n : ℕ) : ℤ :=
  MaskedStrideScan.scratchPosition P S (min (n-4*P) (MaskedStrideScan.ticks P S))+
    cappedRamp S (4*P+MaskedStrideScan.ticks P S) n-
    cappedRamp S (4*P+MaskedStrideScan.ticks P S+S) n

theorem bankPrefix_frozen (P : ℕ) {S : ℕ} (hS : 0<S) (n : ℕ) :
    bankPrefix P S (min n (ticks P S))=bankPath P S n := by
  have ht : ticks P S=8*P+MaskedStrideScan.ticks P S+2*S := by unfold ticks; omega
  have h0 : (min (min n (ticks P S)) (3*P)+1)/3=min ((n+1)/3) P := by omega
  have h1 : min (min n (ticks P S)-3*P) P=min (n-3*P) P := by omega
  have h2 : min (min n (ticks P S)-3*P-P) (MaskedStrideScan.ticks P S)=
      min (n-4*P) (MaskedStrideScan.ticks P S) := by omega
  have h3 : min (min n (ticks P S)-3*P-P-MaskedStrideScan.ticks P S-S-S) P=
      min (n-(4*P+MaskedStrideScan.ticks P S+2*S)) P := by omega
  have h4 : (min n (ticks P S)-3*P-P-MaskedStrideScan.ticks P S-S-S-P)/3=
      min ((n-(5*P+MaskedStrideScan.ticks P S+2*S))/3) P := by omega
  simp only [bankPrefix,h0,h1,h2,h3,h4,MaskedStrideScan.bankPosition_freeze P hS,
    bankPath,cappedRamp,MaskedStrideScan.rise]

theorem scratchPrefix_frozen (P S n : ℕ) :
    scratchPrefix P S (min n (ticks P S))=scratchPath P S n := by
  have ht : ticks P S=8*P+MaskedStrideScan.ticks P S+2*S := by unfold ticks; omega
  have h0 : min (min n (ticks P S)-3*P-P) (MaskedStrideScan.ticks P S)=
      min (n-4*P) (MaskedStrideScan.ticks P S) := by omega
  have h1 : min (min n (ticks P S)-3*P-P-MaskedStrideScan.ticks P S) S=
      min (n-(4*P+MaskedStrideScan.ticks P S)) S := by omega
  have h2 : min (min n (ticks P S)-3*P-P-MaskedStrideScan.ticks P S-S) S=
      min (n-(4*P+MaskedStrideScan.ticks P S+S)) S := by omega
  simp only [scratchPrefix,h0,h1,h2,scratchPath,cappedRamp]

theorem native_halts (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) : Transpose.Tape.HaltsAt (machine isPrefix mask P S) w (ticks P S) := by
  obtain ⟨hs,hh⟩ := native_complete isPrefix mask P hS w
  have hr := (Transpose.Tape.Impl.stepN_init_eq_some_iff (ticks P S) _).mp hs
  refine ⟨hr.1,(Transpose.Tape.Impl.step_run_eq_none_iff (ticks P S)).mp ?_⟩
  rw [hr.2]
  exact hh

theorem workTraj_prefix (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (n : ℕ) (hn : n ≤ ticks P S) (t : Fin 2) :
    Transpose.Tape.workTraj (machine isPrefix mask P S) w n ((encoding P S).port t)=
      if t=0 then bankPrefix P S n else scratchPrefix P S n := by
  have h := native_prefix (encoding P S) (schedule isPrefix mask P S) w initial
    (fun i _ => schedule_active isPrefix mask P S i _) n hn
  have hb : (lift (⟨0,by omega⟩ : Fin (ticks P S+1)) initial).denote
      (encoding P S) (program (schedule isPrefix mask P S) (ticks P S))=
      Transpose.init (machine isPrefix mask P S) :=
    NativeIO.blank_denote (encoding P S) _ _ (NativeMicrocode.initialEncoding_start _)
  rw [hb] at h
  have hr := (Transpose.Tape.Impl.stepN_init_eq_some_iff n _).mp h
  have hp := congrArg (fun d => d.workPos ((encoding P S).port t)) hr.2
  change Transpose.Tape.workTraj (machine isPrefix mask P S) w n _=_ at hp
  refine hp.trans ?_
  simpa only [NativeIO.Config.denote,lift,Equiv.symm_apply_apply,initial,
    NativeMicrocode.blankConfig,zero_add] using schedule_position isPrefix mask P hS w initial n hn t

theorem workTraj_position (isPrefix : Bool) (mask : ℕ → Bool) (P : ℕ) {S : ℕ}
    (hS : 0<S) (w : List Bool) (n : ℕ) (t : Fin 2) :
    Transpose.Tape.workTraj (machine isPrefix mask P S) w n ((encoding P S).port t)=
      if t=0 then bankPath P S n else scratchPath P S n := by
  have hf := congrFun (Transpose.Tape.Impl.workTraj_frozen
    (native_halts isPrefix mask P hS w) ((encoding P S).port t)) n
  exact hf.symm.trans ((workTraj_prefix isPrefix mask P hS w _ (Nat.min_le_right _ _) t).trans
    (by rw [bankPrefix_frozen P hS,scratchPrefix_frozen]))

end TransposeFollowup.RawMaskedStride
