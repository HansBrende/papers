import TransposeFollowup.NativeReadFusionCore
import TransposeFollowup.NativeMicrocodeRun

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeReadFusion
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem step_denote (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (c : NativeMicrocode.Config T L) :
    Transpose.Tape.Impl.next (machine e p selected) w (denote e p selected ip outRev c)=
      denote e p selected ip outRev (step p selected c) := by
  exact step_denote_core e p selected w ip outRev c

theorem run_denote (e : Encoding T L k q) (p : Microcode.Program T L) (selected : L → Bool)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (n : ℕ) (c : NativeMicrocode.Config T L) :
    OperationalTrace.run (Transpose.Tape.Impl.next (machine e p selected) w) n
      (denote e p selected ip outRev c) = denote e p selected ip outRev (run p selected n c) := by
  exact run_denote_core e p selected w ip outRev n c

end TransposeFollowup.NativeReadFusion
