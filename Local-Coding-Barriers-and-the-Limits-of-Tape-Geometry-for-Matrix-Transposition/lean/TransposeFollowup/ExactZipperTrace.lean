import TransposeFollowup.NativeZipper

namespace TransposeFollowup.NativeZipper
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

theorem exact_trace (p : Microcode.Program T L) (n : ℕ) (c : Config T L)
    (ha : ∀ s,s < n → NativeMicrocode.Active p (run p s c).denote) :
    OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c.denote (run p n c).denote := by
  induction n generalizing c with
  | zero => exact .refl _
  | succ n ih =>
    apply OperationalTrace.Trace.cons (ha 0 (by omega))
    rw [← step_denote]
    apply ih
    intro s hs
    exact ha (s+1) (by omega)

end TransposeFollowup.NativeZipper
