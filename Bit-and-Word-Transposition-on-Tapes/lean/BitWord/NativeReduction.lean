import BitWord.NativeReductionRun
import BitWord.NativeReductionCompile

/-! The uniform raw bit-to-word implication in the original fixed-tape model.
The premise allows an arbitrary adaptive bit transposer. All oracle isolation,
replay, arithmetic, descriptors, padding, routing and output are implemented by
the one compiled machine constructed above. -/
namespace BitWord.NativeReductionMachine
open TransposeFollowup
set_option autoImplicit false
noncomputable section

/-- Correct output and actual halting from the original blank initial state. -/
theorem native_transpose (M : Transpose.TM) (C : ℕ) (hM : DyadicBitOracle M C)
    (d : ℕ) (hd : 1≤d) (A : Transpose.Matrix) :
    Transpose.ComputesWithin (nativeMachine M) (Transpose.encode d (Transpose.entryBits d) A)
      (Transpose.encode d (Transpose.entryBits d) (Transpose.transpose A))
      ((200000+208*NativeOracleBatch.suffixConstant M C)*Transpose.inputLength d) := by
  obtain ⟨t,ht,s,pos,htr⟩ := complete_trace M C hM d hd A
  exact computesWithin_of_trace M _ _ t _ ht s pos (Transpose.inputLength d) htr

end
end BitWord.NativeReductionMachine

namespace BitWord
set_option autoImplicit false

/-- Linear-time transposition of dyadic bit squares implies (T), without
assuming that the bit machine has an oblivious schedule or a supplied reset. -/
theorem linearTimeTransposable_of_dyadicBitOracle (M : Transpose.TM) (C : ℕ)
    (hM : DyadicBitOracle M C) : Transpose.LinearTimeTransposable := by
  refine ⟨NativeReductionMachine.nativeMachine M,200000+208*NativeOracleBatch.suffixConstant M C,?_⟩
  intro d hd A
  obtain ⟨t,ht,c,htr,halt,hout⟩ := NativeReductionMachine.native_transpose M C hM d hd A
  refine ⟨t,ht.trans ?_,c,htr,halt,hout⟩
  exact Nat.mul_le_mul_left _ (Nat.le_succ _)

end BitWord
