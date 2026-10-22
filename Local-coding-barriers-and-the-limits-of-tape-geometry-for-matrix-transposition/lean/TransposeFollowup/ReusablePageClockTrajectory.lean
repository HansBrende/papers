import TransposeFollowup.NativeMicrocodeRun
import TransposeFollowup.ReusablePageClockRun

namespace TransposeFollowup.ReusablePageClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem forward_positions (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (hs:s≤2*xs.length+1) (pos : Port q → ℤ) :
    (NativeMicrocode.run (program ops) s (cfg (.inl .read) (Counter.marked xs) pos)).pos=
      PageClock.advance ops pos (s/2) ((xs.take (s/2)).count true) := by
  have h:=OperationalTrace.take_trace (PageClock.complete_trace ops xs pos) s hs
  have he:=OperationalTrace.trace_run (MicrocodeEmbedding.trace_embed (identityBinding q).ports Sum.inl
    (PageClock.program ops) (program ops) (frame (Counter.marked xs) pos) (scan_code ops) h)
  simp only [embed_scan] at he
  simp only [NativeMicrocode.run]
  rw [he]
  change (Function.extend (identityBinding q).ports
    (NativeMicrocode.run (PageClock.program ops) s (PageClock.cfg .read (Counter.marked xs) pos)).pos pos)=_
  rw [← (identityBinding q).values_eq_extend]
  exact PageClock.forward_positions ops xs s hs pos

theorem rewind_region_step (ops : Fin q → PageOpcode) (c : NativeMicrocode.Config (Port q) Label)
    (h:∃ pc,c.core.pc=.inr pc) : ∃ pc,(NativeMicrocode.step (program ops) c).core.pc=.inr pc := by
  obtain ⟨pc,hpc⟩:=h
  cases pc <;> simp only [NativeMicrocode.step,Microcode.actualStep,hpc,program,
    NativeSealBack.program,FinitePortBinding.instruction]
  all_goals exact ⟨_,rfl⟩

theorem rewind_page_step (ops : Fin q → PageOpcode) (c : NativeMicrocode.Config (Port q) Label)
    (h:∃ pc,c.core.pc=.inr pc) (p : Fin q) :
    (NativeMicrocode.step (program ops) c).pos (some p)=c.pos (some p) := by
  obtain ⟨pc,hpc⟩:=h
  cases pc <;> simp [NativeMicrocode.step,hpc,program,NativeSealBack.program,FinitePortBinding.instruction,
    FinitePortBinding.values,clockBinding,MicrocodeEmbedding.idle,NativeMicrocode.direction,Transpose.Dir.shift]

theorem rewind_page_run (ops : Fin q → PageOpcode) (s : ℕ) (c : NativeMicrocode.Config (Port q) Label)
    (h:∃ pc,c.core.pc=.inr pc) (p : Fin q) :
    (NativeMicrocode.run (program ops) s c).pos (some p)=c.pos (some p) := by
  induction s generalizing c with
  | zero => rfl
  | succ s ih =>
    exact (ih (NativeMicrocode.step (program ops) c) (rewind_region_step ops c h)).trans (rewind_page_step ops c h p)

theorem page_trajectory (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (pos : Port q → ℤ) (p : Fin q) :
    (NativeMicrocode.run (program ops) s (cfg (.inl .read) (Counter.marked xs) pos)).pos (some p)=
      pos (some p)+(ops p).direction*((xs.take (s/2)).count true) := by
  by_cases hs:s≤2*xs.length+1
  · rw [forward_positions ops xs s hs pos];rfl
  · have ha:=scan_call ops xs pos
    have hb:=transfer_trace ops (RowStream.closedTape xs) (PageClock.advance ops pos xs.length (xs.count true))
    have hr:=OperationalTrace.trace_run (NativeCountedLoop.trace_trans ha hb)
    have ht:s=(2*xs.length+1+1)+(s-(2*xs.length+1+1)):=by omega
    have hi:xs.length ≤ s/2:=by omega
    simp only [NativeMicrocode.run]
    conv_lhs => rw [ht,OperationalTrace.run_add,hr]
    rw [rewind_page_run ops _ _ ⟨.back,rfl⟩,List.take_of_length_le hi]
    rfl

theorem native_page_trajectory (ops : Fin q → PageOpcode) (xs : List Bool) (s : ℕ) (pos : Port q → ℤ) (p : Fin q)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine ops) input) s
      ((cfg (.inl .read) (Counter.marked xs) pos).denote (nativeEncoding q) (program ops) ip outRev)).workPos
        ((nativeEncoding q).port (some p))=pos (some p)+(ops p).direction*((xs.take (s/2)).count true) := by
  unfold nativeMachine
  rw [NativeMicrocode.run_denote]
  simpa only [NativeMicrocode.Config.denote,Equiv.symm_apply_apply] using page_trajectory ops xs s pos p

theorem framed_page_trajectory {U J : Type*} (ops : Fin q → PageOpcode) (ports : Port q ↪ U)
    (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program ops pc≠.halt → program ops pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (s : ℕ) (hs:s≤4*xs.length+6) (pos : Port q → ℤ) (p : Fin q) :
    (NativeMicrocode.run target s (MicrocodeEmbedding.embed ports labels
      (cfg (.inl .read) (Counter.marked xs) pos) outerFrame)).pos (ports (some p))=
      pos (some p)+(ops p).direction*((xs.take (s/2)).count true) := by
  have h:=OperationalTrace.take_trace (complete_trace ops xs pos) s hs
  have he:=OperationalTrace.trace_run (MicrocodeEmbedding.trace_embed ports labels (program ops) target outerFrame hc h)
  simp only [NativeMicrocode.run]
  rw [he]
  simp only [MicrocodeEmbedding.embed,MicrocodeEmbedding.extend_at]
  exact page_trajectory ops xs s pos p

theorem native_framed_page_trajectory {U J : Type*} {k z : ℕ} (encoding : NativeMicrocode.Encoding U J k z)
    (ops : Fin q → PageOpcode) (ports : Port q ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program ops pc≠.halt → program ops pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (s : ℕ) (hs:s≤4*xs.length+6) (pos : Port q → ℤ) (p : Fin q)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (NativeMicrocode.machine encoding target) input) s
      ((MicrocodeEmbedding.embed ports labels (cfg (.inl .read) (Counter.marked xs) pos) outerFrame).denote encoding target ip outRev)).workPos
        (encoding.port (ports (some p)))=pos (some p)+(ops p).direction*((xs.take (s/2)).count true) := by
  rw [NativeMicrocode.run_denote]
  simpa only [NativeMicrocode.Config.denote,Equiv.symm_apply_apply] using
    framed_page_trajectory ops ports labels target outerFrame hc xs s hs pos p

end TransposeFollowup.ReusablePageClock
