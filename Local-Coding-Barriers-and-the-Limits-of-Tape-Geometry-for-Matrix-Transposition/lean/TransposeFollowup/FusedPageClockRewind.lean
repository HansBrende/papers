import TransposeFollowup.FusedPageClockScan

namespace TransposeFollowup.FusedPageClock
open FixedTapeCompiler CopyMachine
open ReusablePageClock (Port Label program cfg frame clockBinding)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

def shiftClock (pos : Port q → ℤ) (d : ℤ) : Port q → ℤ
  | none => pos none+d
  | some p => pos (some p)

theorem shiftClock_zero (pos : Port q → ℤ) : shiftClock pos 0=pos := by
  funext p;cases p <;> simp [shiftClock]
theorem shiftClock_add (pos : Port q → ℤ) (a b : ℤ) : shiftClock (shiftClock pos a) b=shiftClock pos (a+b) := by
  funext p;cases p <;> simp [shiftClock,add_assoc]

theorem rewind_step (ops : Fin q → PageOpcode) (s a : Sym Bool) (hs : s≠.start) (hb : s≠.blank)
    (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    step ops (cfg (.inr .back) ⟨a::pre,s::post⟩ pos)=
      cfg (.inr .back) ⟨pre,a::s::post⟩ (shiftClock pos (-1)) := by
  have ht:=MicrocodeEmbedding.trace_embed (clockBinding q).ports Sum.inr NativeSealBack.program (program ops)
    (frame ⟨a::pre,s::post⟩ pos) (ReusablePageClock.rewind_code ops)
    (NativeClosedStream.rewind_pair s a hs hb pre post (fun _ => pos none))
  have he:=OperationalTrace.trace_run ht
  simp only [ReusablePageClock.embed_rewind,ReusablePageClock.clock_positions] at he
  have hf : step ops (cfg (.inr .back) ⟨a::pre,s::post⟩ pos)=
      NativeMicrocode.step (program ops) (NativeMicrocode.step (program ops) (cfg (.inr .back) ⟨a::pre,s::post⟩ pos)) := by
    apply NativeReadFusion.step_read_act _ _ _ _ _
      ((clockBinding q).values (Microcode.single 0 ⟨none,.left⟩) (fun _ => MicrocodeEmbedding.idle)) (.inr .back) rfl rfl
    change program ops (.inr (match (⟨a::pre,s::post⟩ : Tape Bool).denote.head with
      | .start => .right | .stop | .data _ => .left | .blank => .reject)) = _
    cases s <;> simp_all [Tape.read,program,NativeSealBack.program,FinitePortBinding.instruction]
  rw [hf]
  change OperationalTrace.run (NativeMicrocode.step (program ops)) 2 _ = _
  rw [he]
  congr 1
  funext p;cases p <;> simp [clockBinding,FinitePortBinding.values,shiftClock,sub_eq_add_neg]

theorem rewind_finish_step (ops : Fin q → PageOpcode) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    step ops (cfg (.inr .back) ⟨pre,.start::post⟩ pos)=
      cfg (.inr .done) ⟨.start::pre,post⟩ (shiftClock pos 1) := by
  have ht:=MicrocodeEmbedding.trace_embed (clockBinding q).ports Sum.inr NativeSealBack.program (program ops)
    (frame ⟨pre,.start::post⟩ pos) (ReusablePageClock.rewind_code ops)
    (NativeClosedStream.rewind_finish pre post (fun _ => pos none))
  have he:=OperationalTrace.trace_run ht
  simp only [ReusablePageClock.embed_rewind,ReusablePageClock.clock_positions] at he
  have hf : step ops (cfg (.inr .back) ⟨pre,.start::post⟩ pos)=
      NativeMicrocode.step (program ops) (NativeMicrocode.step (program ops) (cfg (.inr .back) ⟨pre,.start::post⟩ pos)) := by
    apply NativeReadFusion.step_read_act _ _ _ _ _
      ((clockBinding q).values (Microcode.single 0 ⟨none,.right⟩) (fun _ => MicrocodeEmbedding.idle)) (.inr .done) rfl rfl
    change program ops (.inr (match (⟨pre,.start::post⟩ : Tape Bool).denote.head with
      | .start => .right | .stop | .data _ => .left | .blank => .reject)) = _
    simp [Tape.read,program,NativeSealBack.program,FinitePortBinding.instruction]
  rw [hf]
  change OperationalTrace.run (NativeMicrocode.step (program ops)) 2 _ = _
  rw [he]
  congr 1
  funext p;cases p <;> rfl

theorem rewind_trace (ops : Fin q → PageOpcode) (s a : Sym Bool) (hs : s≠.start) (hb : s≠.blank)
    (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 1 (cfg (.inr .back) ⟨a::pre,s::post⟩ pos)
      (cfg (.inr .back) ⟨pre,a::s::post⟩ (shiftClock pos (-1))) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeReadFusion.active_iff _ _ _).mpr
    simp [NativeMicrocode.Active,cfg,program,NativeSealBack.program,FinitePortBinding.instruction]
  · rw [rewind_step ops s a hs hb];exact .refl _

theorem rewind_finish_trace (ops : Fin q → PageOpcode) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 1 (cfg (.inr .back) ⟨pre,.start::post⟩ pos)
      (cfg (.inr .done) ⟨.start::pre,post⟩ (shiftClock pos 1)) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeReadFusion.active_iff _ _ _).mpr
    simp [NativeMicrocode.Active,cfg,program,NativeSealBack.program,FinitePortBinding.instruction]
  · rw [rewind_finish_step];exact .refl _

end TransposeFollowup.FusedPageClock
