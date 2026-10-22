import TransposeFollowup.RepeatedAddCalls
import TransposeFollowup.ModularRowWord

/-! Shared add/subtract-and-recycle block with four paid jumps. The old
repeated-addition body specializes it and pays its extra entry jump. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
set_option autoImplicit false

theorem update_trace_to (target : Microcode.Program Port Label)
    (haCode : ∀ copy pc, BinaryCarry.program pc ≠ .halt → BinaryCarry.program pc ≠ .reject →
      target (.arithmetic copy pc) = MicrocodeEmbedding.instruction (arithmeticBinding copy).ports
        (Label.arithmetic copy) (BinaryCarry.program pc))
    (hcCode : ∀ scratch pc, NativeBuffer.program pc ≠ .halt → NativeBuffer.program pc ≠ .reject →
      target (.clear scratch pc) = MicrocodeEmbedding.instruction (clearBinding scratch).ports
        (Label.clear scratch) (NativeBuffer.program pc))
    (haDone : ∀ copy carry, target (.arithmetic copy (.done carry)) = .jump (.clear copy (.erase 2)))
    (hcDone : ∀ scratch, target (.clear scratch .done) =
      .jump (if scratch then .counter 0 else .arithmetic true (.scan false false)))
    (sub : Bool) (fuel a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ 18 * x.length + 30,
      OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) t (cfg (.arithmetic false (.scan sub sub)) (ready fuel a x) pos)
        (cfg (.counter 0) (ready fuel (ModularRowWord.operation sub a x) x) pos) := by
  let r := ModularRowWord.operation sub a x
  have hr : r.length = x.length := ModularRowWord.operation_length sub a x h
  let b0 := ready fuel a x
  let b1 := {b0 with scratch := BinaryCarry.marked r}
  let b2 := {b1 with acc := BinaryCarry.preparedOutput}
  let b3 := {b2 with acc := BinaryCarry.marked r}
  let b4 := {b3 with scratch := BinaryCarry.preparedOutput}
  let carry := (BinaryCarry.result sub sub a x).2
  obtain ⟨ta, ha, hAdd⟩ := arithmetic_call_to target (haCode false) sub a x h b0 pos
  have tAdd : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) ta (cfg (.arithmetic false (.scan sub sub)) b0 pos)
      (cfg (.arithmetic false (.done carry)) b1 pos) := by
    simpa [b0, b1, r, carry, ready, ModularRowWord.operation] using hAdd
  obtain ⟨te, he, hErase⟩ := recycle_call_to target hcCode false a b1 pos
  have tErase : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) te (cfg (.clear false (.erase 2)) b1 pos)
      (cfg (.clear false .done) b2 pos) := by
    simpa [Bank.set, b2, b1, b0, ready, Counter.marked, BinaryCarry.marked,
      BinaryCompare.marked] using hErase
  obtain ⟨tc, hc, hCopy⟩ := copy_call_to target (haCode true) r b2 pos
  rw [hr] at hc
  simp only [hr] at hCopy
  have tCopy : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) tc (cfg (.arithmetic true (.scan false false)) b2 pos)
      (cfg (.arithmetic true (.done false)) b3 pos) := by
    simpa [b3, b2, b1, b0, ready] using hCopy
  obtain ⟨tr, hrr, hRecycle⟩ := recycle_call_to target hcCode true r b3 pos
  rw [hr] at hrr
  have tRecycle : OperationalTrace.Trace (NativeMicrocode.step target) (NativeMicrocode.Active target) tr (cfg (.clear true (.erase 2)) b3 pos)
      (cfg (.clear true .done) b4 pos) := by
    simpa [Bank.set, b4, b3, b2, b1, b0, ready, Counter.marked, BinaryCarry.marked,
      BinaryCompare.marked] using hRecycle
  have j1 := jump_trace_to target (.arithmetic false (.done carry)) (.clear false (.erase 2)) b1 pos (haDone false carry)
  have j2 := jump_trace_to target (.clear false .done) (.arithmetic true (.scan false false)) b2 pos (hcDone false)
  have j3 := jump_trace_to target (.arithmetic true (.done false)) (.clear true (.erase 2)) b3 pos (haDone true false)
  have j4 := jump_trace_to target (.clear true .done) (.counter 0) b4 pos (hcDone true)
  have whole := NativeCountedLoop.trace_trans tAdd
    (NativeCountedLoop.trace_trans j1 (NativeCountedLoop.trace_trans tErase
      (NativeCountedLoop.trace_trans j2 (NativeCountedLoop.trace_trans tCopy
        (NativeCountedLoop.trace_trans j3 (NativeCountedLoop.trace_trans tRecycle j4))))))
  refine ⟨ta + (1 + (te + (1 + (tc + (1 + (tr + 1)))))), ?_, ?_⟩
  · omega
  · simpa [b4, b3, b2, b1, b0, ready, r] using whole

theorem body_trace (fuel a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ 18 * x.length + 31,
      Trace t (cfg (.counter 11) (ready fuel a x) pos)
        (cfg (.counter 0) (ready fuel (addWord a x) x) pos) := by
  obtain ⟨t, ht, htr⟩ := update_trace_to program arithmetic_code clear_code
    (fun _ _ => rfl) (fun scratch => by cases scratch <;> rfl) false fuel a x h pos
  have j0 := jump_trace (.counter 11) (.arithmetic false (.scan false false)) (ready fuel a x) pos rfl
  exact ⟨1+t, by omega, NativeCountedLoop.trace_trans j0 htr⟩

end TransposeFollowup.RepeatedAdd
