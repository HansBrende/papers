import TransposeFollowup.NativeReadFusion
import TransposeFollowup.FusedPageClockRun
import TransposeFollowup.SevenPhaseClock

namespace TransposeFollowup.FusedPageClock
open FixedTapeCompiler CopyMachine
open ReusablePageClock (Port Label program cfg nativeEncoding)
set_option autoImplicit false
variable {q : ℕ}

theorem rewind_region_step (ops : Fin q → PageOpcode) (c : NativeMicrocode.Config (Port q) Label)
    (h : ∃ pc,c.core.pc=.inr pc) : ∃ pc,(step ops c).core.pc=.inr pc := by
  simp only [step]
  rcases NativeReadFusion.step_one_or_two (program ops) selected c with he|he
  · rw [he];exact ReusablePageClock.rewind_region_step ops c h
  · rw [he]
    exact ReusablePageClock.rewind_region_step ops _ (ReusablePageClock.rewind_region_step ops c h)

theorem rewind_page_step (ops : Fin q → PageOpcode) (c : NativeMicrocode.Config (Port q) Label)
    (h : ∃ pc,c.core.pc=.inr pc) (p : Fin q) : (step ops c).pos (some p)=c.pos (some p) := by
  simp only [step]
  rcases NativeReadFusion.step_one_or_two (program ops) selected c with he|he
  · rw [he];exact ReusablePageClock.rewind_page_step ops c h p
  · rw [he]
    exact (ReusablePageClock.rewind_page_step ops _ (ReusablePageClock.rewind_region_step ops c h) p).trans
      (ReusablePageClock.rewind_page_step ops c h p)

theorem rewind_page_run (ops : Fin q → PageOpcode) (s : ℕ) (c : NativeMicrocode.Config (Port q) Label)
    (h : ∃ pc,c.core.pc=.inr pc) (p : Fin q) : (run ops s c).pos (some p)=c.pos (some p) := by
  induction s generalizing c with
  | zero => rfl
  | succ s ih => exact (ih (step ops c) (rewind_region_step ops c h)).trans (rewind_page_step ops c h p)

theorem page_trajectory (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (pos : Port q → ℤ) (p : Fin q) :
    (run ops s (cfg (.inl .read) (Counter.marked xs) pos)).pos (some p)=
      pos (some p)+(ops p).direction*((xs.take s).count true) := by
  by_cases hs : s ≤ xs.length
  · rw [prefix_run ops xs s hs pos];rfl
  · have hr:=OperationalTrace.trace_run (scan_trace ops xs pos)
    have ht:s=(xs.length+1)+(s-(xs.length+1)):=by omega
    have hi:xs.length ≤ s:=by omega
    simp only [run,NativeReadFusion.run]
    conv_lhs => rw [ht,OperationalTrace.run_add,hr]
    rw [rewind_page_run ops _ _ ⟨.back,rfl⟩,List.take_of_length_le hi]
    rfl

theorem native_page_trajectory (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (pos : Port q → ℤ) (p : Fin q)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine ops) input) s
      (NativeReadFusion.denote (nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inl .read) (Counter.marked xs) pos))).workPos
        ((nativeEncoding q).port (some p))=pos (some p)+(ops p).direction*((xs.take s).count true) := by
  unfold nativeMachine
  rw [NativeReadFusion.run_denote]
  simpa only [NativeReadFusion.denote,Equiv.symm_apply_apply] using page_trajectory ops xs s pos p

theorem native_record (ops : Fin q → PageOpcode) (R : ℕ) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine ops) input (14*R+3)
      (NativeReadFusion.denote (nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inl .read) (Counter.marked (SevenPhaseClock.word R)) pos))=
      some (NativeReadFusion.denote (nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inr .done) (Counter.marked (SevenPhaseClock.word R)) (PageClock.advance ops pos 0 (4*R)))) ∧
    Transpose.step (nativeMachine ops) input
      (NativeReadFusion.denote (nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inr .done) (Counter.marked (SevenPhaseClock.word R)) (PageClock.advance ops pos 0 (4*R))))=none := by
  have h:=native_complete ops (SevenPhaseClock.word R) pos input ip outRev
  simpa only [SevenPhaseClock.word_length,SevenPhaseClock.word_count,show 2*(7*R)+3=14*R+3 by ring] using h

theorem native_record_trajectory (ops : Fin q → PageOpcode) (R s : ℕ) (pos : Port q → ℤ) (p : Fin q)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine ops) input) s
      (NativeReadFusion.denote (nativeEncoding q) (program ops) selected ip outRev
        (cfg (.inl .read) (Counter.marked (SevenPhaseClock.word R)) pos))).workPos
        ((nativeEncoding q).port (some p))=recordRun R (ops p) (pos (some p)) s := by
  rw [native_page_trajectory,SevenPhaseClock.count_ramp,recordRun_eq]

theorem row_calls_linear (n G K : ℕ) (hn : 1 ≤ n) (hG : 1 ≤ G) :
    2*n*(14*(K*Transpose.Tape.TSDiagram.blockSize G n)+3) ≤ (28*K+6)*Transpose.inputLength n := by
  have hr:=Transpose.Tape.Impl.blockSize_le (n:=n) hG
  have hm:=Nat.mul_le_mul_left (n*K) hr
  have hnP:=DimensionCandidate.dimension_le_length n hn
  unfold Transpose.inputLength at hnP ⊢
  nlinarith

end TransposeFollowup.FusedPageClock
