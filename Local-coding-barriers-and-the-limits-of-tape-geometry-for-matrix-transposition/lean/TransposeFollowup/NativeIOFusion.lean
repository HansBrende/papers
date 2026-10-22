import TransposeFollowup.NativeIOFusionCore
import TransposeFollowup.NativeIO
import TransposeFollowup.NativeReadFusion

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
open NativeIO (Program Config workProgram)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem step_denote (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (c : Config T L) :
    Transpose.Tape.Impl.next (machine e p selected) w (denote e p selected c)=
      denote e p selected (step p selected w c) := by
  exact step_denote_core e p selected w c

end TransposeFollowup.NativeIOFusion
