import TransposeFollowup.NativeIOFusionRunCore

/-! Recover a charged source trace from a successful original-machine
stepN execution. This cannot extend a halted run by frozen iterations. -/
namespace TransposeFollowup.NativeIOFusion
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

theorem trace_of_stepN (e : NativeMicrocode.Encoding T L k q) (p : NativeIO.Program T L)
    (selected : L → Bool) (w : List Bool) (n : ℕ) (c : NativeIO.Config T L)
    (d : Transpose.Config (machine e p selected))
    (h : Transpose.stepN (machine e p selected) w n (denote e p selected c)=some d) :
    OperationalTrace.Trace (step p selected w) (Active p selected) n c (run p selected w n c) := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih =>
    have ha : Active p selected c := by
      by_contra hn
      have hh:=(step_none_iff e p selected w c).mpr hn
      simp only [Transpose.stepN,hh] at h
      contradiction
    rw [Transpose.stepN,step_some_of_active e p selected w c ha] at h
    exact .cons ha (ih (step p selected w c) h)

end TransposeFollowup.NativeIOFusion
