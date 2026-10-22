import TransposeFollowup.NativeIOFusionRunCore
import TransposeFollowup.NativeIOFusion

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
open NativeMicrocode (Encoding symbolCode symbolDecode)
open NativeIO (Program Config workProgram)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem run_denote (e : Encoding T L k q) (p : Program T L) (selected : L → Bool)
    (w : List Bool) (n : ℕ) (c : Config T L) :
    OperationalTrace.run (Transpose.Tape.Impl.next (machine e p selected) w) n (denote e p selected c)=
      denote e p selected (run p selected w n c) := by
  exact run_denote_core e p selected w n c

theorem native_run (e : Encoding T L k q) (p : Program T L) (selected : L → Bool) (w : List Bool)
    (start : L) (hs : e.label start=0) (n : ℕ) :
    Transpose.Tape.run (machine e p selected) w n=
      denote e p selected (run p selected w n ⟨NativeMicrocode.blankConfig start,0,[]⟩) := by
  rw [Transpose.Tape.Impl.run_eq_iterate,← NativeMicrocode.operationalRun_eq_iterate,
    ← blank_denote e p selected start hs,run_denote]

end TransposeFollowup.NativeIOFusion
