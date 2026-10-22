import TransposeFollowup.BinaryCarryRun
import TransposeFollowup.MicrocodeEmbedding

/-! Callable comparison and carry routines in a larger finite native TM.
The caller supplies actual code equations, distinct tape ports and prepared
operand/result tapes. Other tapes are preserved through the explicit frame.
Return labels can continue computation; no additional halt step is charged. -/

namespace TransposeFollowup.NativeArithmeticCalls

open FixedTapeCompiler
open MicrocodeEmbedding (Frame embed instruction)
set_option autoImplicit false
variable {U J : Type*} {k q : ℕ}

theorem compare (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 2 ↪ U) (labels : BinaryCompare.Label → J) (target : Microcode.Program U J)
    (frame : Frame U) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    (hc : ∀ pc, BinaryCompare.program pc ≠ .halt → BinaryCompare.program pc ≠ .reject →
      target (labels pc) = instruction ports labels (BinaryCompare.program pc))
    (xs ys : List Bool) (h : xs.length = ys.length) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 5 * xs.length + 6,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((embed ports labels
          (BinaryCompare.cfg (.scan .equal) (BinaryCompare.marked xs)
            (BinaryCompare.marked ys) pos).denote frame).denote encoding target inputPos outRev) =
        some ((embed ports labels
          (BinaryCompare.cfg (.done (BinaryCompare.numeric .equal (BinaryCompare.value xs)
            (BinaryCompare.value ys))) (BinaryCompare.marked xs) (BinaryCompare.marked ys)
              pos).denote frame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := BinaryCompare.comparison_trace xs ys h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels BinaryCompare.program target
    frame w inputPos outRev hc htr⟩

theorem arithmetic (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 3 ↪ U) (labels : BinaryCarry.Label → J) (target : Microcode.Program U J)
    (frame : Frame U) (w : List Bool) (inputPos : ℤ) (outRev : List Bool)
    (hc : ∀ pc, BinaryCarry.program pc ≠ .halt → BinaryCarry.program pc ≠ .reject →
      target (labels pc) = instruction ports labels (BinaryCarry.program pc))
    (sub c : Bool) (xs ys : List Bool) (h : xs.length = ys.length) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5 * xs.length + 7,
      Transpose.stepN (NativeMicrocode.machine encoding target) w t
        ((embed ports labels
          (BinaryCarry.cfg (.scan sub c) (BinaryCarry.marked xs) (BinaryCarry.marked ys)
            BinaryCarry.preparedOutput pos).denote frame).denote encoding target inputPos outRev) =
        some ((embed ports labels
          (BinaryCarry.cfg (.done (BinaryCarry.result sub c xs ys).2) (BinaryCarry.marked xs)
            (BinaryCarry.marked ys) (BinaryCarry.marked (BinaryCarry.result sub c xs ys).1)
              pos).denote frame).denote encoding target inputPos outRev) := by
  obtain ⟨t, ht, htr⟩ := BinaryCarry.arithmetic_trace sub c xs ys h pos
  exact ⟨t, ht, MicrocodeEmbedding.native_call encoding ports labels BinaryCarry.program target
    frame w inputPos outRev hc htr⟩

end TransposeFollowup.NativeArithmeticCalls
