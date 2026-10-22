import TransposeFollowup.FiniteProgramEncodingCore
import TransposeFollowup.NativeMicrocodeRun

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeMicrocode
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [Fintype L]

theorem finite_program_native_trajectory (p : Microcode.Program T L) (start : L)
    (w : List Bool) (n : ℕ) (t : T) :
    Transpose.Tape.workTraj (machine (initialEncoding start) p) w n
      ((initialEncoding start).port t) = (run p n (blankConfig start)).pos t :=
  native_trajectory (initialEncoding start) p w start (initialEncoding_start start) n t

end TransposeFollowup.NativeMicrocode
