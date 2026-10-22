import TransposeFollowup.NativeMicrocodeCore
import Transpose.Tape.Run

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeMicrocode
open FixedTapeCompiler
open Microcode (Instruction Program)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem step_denote (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (c : Config T L) :
    Transpose.Tape.Impl.next (machine e p) w (c.denote e p inputPos outRev) =
      (step p c).denote e p inputPos outRev := by
  exact step_denote_core e p w inputPos outRev c

end TransposeFollowup.NativeMicrocode
