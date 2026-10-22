import TransposeFollowup.RepeatedAddRun

/-! A reusable in-place addition is already present in the proved repeated-
addition machine: choose the one-bit fuel word [true]. Its final all-ones
fuel is again [true], so each future call starts with the same prepared
fuel. The counter work is charged; no free restoration or reload is used. -/

namespace TransposeFollowup.RepeatedAdd

open FixedTapeCompiler
set_option autoImplicit false

theorem single_add_trace (a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ) :
    ∃ t ≤ 18 * x.length + 51,
      Trace t (cfg (.counter 0) (ready [true] a x) pos)
        (cfg (.counter 12) (ready [true] (addWord a x) x) pos) := by
  simpa [budget, Counter.value, repeatWord] using repeated_add_trace [true] a x h pos

theorem single_add_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U)
    (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc) = MicrocodeEmbedding.instruction ports labels (program pc))
    (a x : List Bool) (h : a.length = x.length) (pos : Port → ℤ)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 18 * x.length + 51,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((MicrocodeEmbedding.embed ports labels (cfg (.counter 0) (ready [true] a x) pos)
          outerFrame).denote encoding target inputPos outRev) =
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.counter 12) (ready [true] (addWord a x) x) pos)
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := single_add_trace a x h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame w inputPos outRev hc htr⟩

end TransposeFollowup.RepeatedAdd
