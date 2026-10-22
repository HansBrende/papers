import TransposeFollowup.ReusablePageClockTrajectory
import Transpose.Tape.MStarTM
import TransposeFollowup.DimensionCandidateSearch

/-! A concrete seven-phase Boolean clock. A reusable execution has exactly
28R+6 transitions; the movement ramp runs at half native speed,then stays
fixed while the clock rewinds. Clock construction and opcode fetch remain
separate paid obligations. -/
namespace TransposeFollowup.SevenPhaseClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

def word (R : ℕ) : List Bool := List.replicate R false++List.replicate (4*R) true++List.replicate (2*R) false

theorem word_length (R : ℕ) : (word R).length=7*R := by simp [word];omega
theorem word_count (R : ℕ) : (word R).count true=4*R := by simp [word,List.count_replicate]
theorem take_count (R i : ℕ) : ((word R).take i).count true=min (i-R) (4*R) := by
  simp [word,List.take_append,List.take_replicate,List.count_replicate,Nat.min_comm]
theorem count_ramp (R i : ℕ) : (((word R).take i).count true:ℤ)=cappedRamp (4*R) R i := by
  rw [take_count]
  unfold cappedRamp
  omega

theorem native_record (ops : Fin q → PageOpcode) (R : ℕ) (pos : PageClock.Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (ReusablePageClock.nativeMachine ops) input (28*R+6)
      ((ReusablePageClock.cfg (.inl .read) (Counter.marked (word R)) pos).denote
        (ReusablePageClock.nativeEncoding q) (ReusablePageClock.program ops) ip outRev)=
      some ((ReusablePageClock.cfg (.inr .done) (Counter.marked (word R)) (PageClock.advance ops pos 0 (4*R))).denote
        (ReusablePageClock.nativeEncoding q) (ReusablePageClock.program ops) ip outRev) ∧
    Transpose.step (ReusablePageClock.nativeMachine ops) input
      ((ReusablePageClock.cfg (.inr .done) (Counter.marked (word R)) (PageClock.advance ops pos 0 (4*R))).denote
        (ReusablePageClock.nativeEncoding q) (ReusablePageClock.program ops) ip outRev)=none := by
  have h:=ReusablePageClock.native_complete ops (word R) pos input ip outRev
  simpa only [word_length,word_count,show 4*(7*R)+6=28*R+6 by ring] using h

theorem record_trajectory (ops : Fin q → PageOpcode) (R s : ℕ) (pos : PageClock.Port q → ℤ) (p : Fin q) :
    (NativeMicrocode.run (ReusablePageClock.program ops) s
      (ReusablePageClock.cfg (.inl .read) (Counter.marked (word R)) pos)).pos (some p)=
      recordRun R (ops p) (pos (some p)) (s/2) := by
  rw [ReusablePageClock.page_trajectory,count_ramp,recordRun_eq]

theorem native_record_trajectory (ops : Fin q → PageOpcode) (R s : ℕ) (pos : PageClock.Port q → ℤ) (p : Fin q)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (ReusablePageClock.nativeMachine ops) input) s
      ((ReusablePageClock.cfg (.inl .read) (Counter.marked (word R)) pos).denote
        (ReusablePageClock.nativeEncoding q) (ReusablePageClock.program ops) ip outRev)).workPos
        ((ReusablePageClock.nativeEncoding q).port (some p))=recordRun R (ops p) (pos (some p)) (s/2) := by
  rw [ReusablePageClock.native_page_trajectory,count_ramp,recordRun_eq]

theorem row_calls_linear (n G K : ℕ) (hn:1≤n) (hG:1≤G) :
    2*n*(28*(K*Transpose.Tape.TSDiagram.blockSize G n)+6)≤(56*K+12)*Transpose.inputLength n := by
  have hr:=Transpose.Tape.Impl.blockSize_le (n:=n) hG
  have hm:=Nat.mul_le_mul_left (n*K) hr
  have hnP:=DimensionCandidate.dimension_le_length n hn
  unfold Transpose.inputLength at hnP ⊢
  nlinarith

end TransposeFollowup.SevenPhaseClock
