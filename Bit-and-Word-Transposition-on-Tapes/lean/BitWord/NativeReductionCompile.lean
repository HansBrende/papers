import BitWord.NativeReductionLayout

/-! Literal compilation of the assembled raw trace to the original TM model. -/
namespace BitWord.NativeReductionMachine
open FixedTapeCompiler TransposeFollowup CopyMachine NativeExpanderShearFrames
set_option autoImplicit false
noncomputable section

/-- This is a trace-to-machine bridge, not an assumption about an oracle or
an uncharged interface. Its initial state is the original model's blank state. -/
theorem computesWithin_of_trace (M : Transpose.TM) (w out : List Bool) (t T : ℕ)
    (ht : t≤T) (s : Bank M) (pos : Port M → ℤ) (ip : ℤ)
    (htr : Trace M w t (cfg M (start M) (blank M) (fun _ => 0) 0 [])
      (cfg M .done s pos ip out.reverse)) :
    Transpose.ComputesWithin (nativeMachine M) w out T := by
  let final := cfg M .done s pos ip out.reverse
  refine ⟨t,ht,final.denote (nativeEncoding M) (program M),?_,?_,?_⟩
  · have hi : (cfg M (start M) (blank M) (fun _ => 0) 0 []).denote
        (nativeEncoding M) (program M)=Transpose.init (nativeMachine M) :=
      NativeIO.blank_denote (nativeEncoding M) (program M) (start M) (initial_state_zero M)
    rw [←hi]
    exact NativeIO.trace_stepN (nativeEncoding M) (program M) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding M) (program M) w final).mpr
    intro hc
    exact hc.1 rfl
  · change out.reverse.reverse=out
    exact List.reverse_reverse _

theorem fixed_resources (M : Transpose.TM) :
    (nativeMachine M).k=Fintype.card (Port M) ∧ (nativeMachine M).g+1=5 ∧
    (nativeEncoding M).label (start M)=0 :=
  ⟨rfl,rfl,initial_state_zero M⟩

end
end BitWord.NativeReductionMachine
