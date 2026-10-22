import TransposeFollowup.NativeMicrocodeRunCore
import TransposeFollowup.NativeMicrocode

/-! Compatibility statements in the original paper's run vocabulary.
Reusable computation and its proofs live in the corresponding Core module. -/

namespace TransposeFollowup.NativeMicrocode
open FixedTapeCompiler
open Microcode (Instruction Program)
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem run_denote (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (n : ℕ) (c : Config T L) :
    OperationalTrace.run (Transpose.Tape.Impl.next (machine e p) w) n
      (c.denote e p inputPos outRev) = (run p n c).denote e p inputPos outRev := by
  exact run_denote_core e p w inputPos outRev n c

theorem actual_result_transfers (e : Encoding T L k q) (p : Program T L)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) (n : ℕ)
    (c : Config T L) (d : Microcode.ActualConfig T L)
    (h : Microcode.actualRun p n c.core = d) :
    let v := OperationalTrace.run (Transpose.Tape.Impl.next (machine e p) w) n
      (c.denote e p inputPos outRev)
    v.state = e.label d.pc ∧ v.inPos = inputPos ∧ v.outRev = outRev ∧
      ∀ t z, v.work (e.port t) (v.workPos (e.port t) + z) =
        symbolCode ((d.tapes t).nth z) := by
  exact actual_result_transfers_core e p w inputPos outRev n c d h

theorem native_run (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (start : L) (hs : e.label start = 0) (n : ℕ) :
    Transpose.Tape.run (machine e p) w n =
      (run p n (blankConfig start)).denote e p 0 [] := by
  rw [Transpose.Tape.Impl.run_eq_iterate, ← operationalRun_eq_iterate,
    ← blank_denote e p start hs, run_denote]

theorem native_trajectory (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (start : L) (hs : e.label start = 0) (n : ℕ) (t : T) :
    Transpose.Tape.workTraj (machine e p) w n (e.port t) =
      (run p n (blankConfig start)).pos t := by
  change (Transpose.Tape.run (machine e p) w n).workPos (e.port t) = _
  rw [native_run e p w start hs]
  simp [Config.denote]

end TransposeFollowup.NativeMicrocode
