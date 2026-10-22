import TransposeFollowup.ReusablePageClockMachine

namespace TransposeFollowup.ReusablePageClock
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

theorem complete_trace (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ) :
    Trace ops (4*xs.length+6) (cfg (.inl .read) (Counter.marked xs) pos)
      (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) := by
  have ha:=scan_call ops xs pos
  have hb:=transfer_trace ops (RowStream.closedTape xs) (PageClock.advance ops pos xs.length (xs.count true))
  have hc:=rewind_call ops xs pos
  have hn:(2*xs.length+1)+1+(2*xs.length+4)=4*xs.length+6:=by omega
  simpa only [hn] using trace_trans (trace_trans ha hb) hc

noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (.inl .read : Label)
noncomputable def nativeMachine (ops : Fin q → PageOpcode) := NativeMicrocode.machine (nativeEncoding q) (program ops)

theorem native_complete (ops : Fin q → PageOpcode) (xs : List Bool) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine ops) input (4*xs.length+6)
      ((cfg (.inl .read) (Counter.marked xs) pos).denote (nativeEncoding q) (program ops) ip outRev)=
      some ((cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))).denote
        (nativeEncoding q) (program ops) ip outRev) ∧
    Transpose.step (nativeMachine ops) input
      ((cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))).denote
        (nativeEncoding q) (program ops) ip outRev)=none := by
  refine ⟨NativeMicrocode.trace_stepN _ _ input ip outRev (complete_trace ops xs pos),?_⟩
  apply (NativeMicrocode.step_none_iff _ _ input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSealBack.program]

theorem native_call {U J : Type*} {k z : ℕ} (encoding : NativeMicrocode.Encoding U J k z)
    (ops : Fin q → PageOpcode) (ports : Port q ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program ops pc≠.halt → program ops pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program ops pc))
    (xs : List Bool) (pos : Port q → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (NativeMicrocode.machine encoding target) input (4*xs.length+6)
      ((MicrocodeEmbedding.embed ports labels (cfg (.inl .read) (Counter.marked xs) pos) outerFrame).denote encoding target ip outRev)=
      some ((MicrocodeEmbedding.embed ports labels
        (cfg (.inr .done) (Counter.marked xs) (PageClock.advance ops pos 0 (xs.count true))) outerFrame).denote encoding target ip outRev) :=
  MicrocodeEmbedding.native_call encoding ports labels _ target outerFrame input ip outRev hc (complete_trace ops xs pos)

theorem fixed_resources (ops : Fin q → PageOpcode) : (nativeMachine ops).k=q+1 ∧
    (nativeMachine ops).g+1=5 ∧ (nativeMachine ops).q+1=11 ∧ (nativeEncoding q).label (.inl .read)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card (Option (Fin q))=q+1;simp
  · change Fintype.card Label-1+1=11;decide +kernel

end TransposeFollowup.ReusablePageClock
