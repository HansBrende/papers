import TransposeFollowup.NativeReadFusionCore

namespace TransposeFollowup.NativeReadFusion
open FixedTapeCompiler
set_option autoImplicit false
variable {T L : Type*}

/-- Fusion contracts either one or two original microsteps. It cannot
execute a second read or a newly reached halt prematurely. -/
theorem step_one_or_two (p : Microcode.Program T L) (selected : L → Bool) (c : NativeMicrocode.Config T L) :
    step p selected c=NativeMicrocode.step p c ∨
      step p selected c=NativeMicrocode.step p (NativeMicrocode.step p c) := by
  by_cases hs : selected c.core.pc=true
  · cases hp : p c.core.pc with
    | read t next =>
      cases hn : p (next ((c.core.tapes t).head)) <;>
        simp [step,NativeMicrocode.step,Microcode.actualStep,effective,instruction,hs,hp,hn]
    | _ => simp [step,NativeMicrocode.step,Microcode.actualStep,effective,instruction,hs,hp]
  · left
    apply step_unselected
    exact Bool.eq_false_iff.mpr hs

end TransposeFollowup.NativeReadFusion
