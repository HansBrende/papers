import TransposeFollowup.NativeIOCore
import TransposeFollowup.NativeMicrocodeRun

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeIO
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem step_denote (e : Encoding T L k q) (p : Program T L) (w : List Bool) (c : Config T L) :
    Transpose.Tape.Impl.next (machine e p) w (c.denote e p)=(step p w c).denote e p := by
  exact step_denote_core e p w c

end TransposeFollowup.NativeIO
