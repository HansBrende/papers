import TransposeFollowup.InputMeasureCalls

/-! Reuse the work-only suffix of the existing input-measurement controller.
The marked source is supplied on tape; the original input is not accessed.
Tally initialization, measurement, complement copy and tally erasure are paid. -/
namespace TransposeFollowup.InputMeasure
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem work_jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.work (.jump next)) : WorkTrace 1 (workCfg pc s pos) (workCfg next s pos) := by
  have hw : NativeIO.workProgram program pc=.jump next := by simp [NativeIO.workProgram,h]
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,workCfg,hw]
  · have hs : NativeMicrocode.step (NativeIO.workProgram program) (workCfg pc s pos)=workCfg next s pos := by
      simp [NativeMicrocode.step,Microcode.actualStep,workCfg,hw]
    rw [hs];exact .refl _

theorem stored_length_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 32*xs.length+42,WorkTrace t
      (workCfg (.copy false (.init (.erase 0))) (loaded xs) pos)
      (workCfg .done (final xs) pos) := by
  obtain ⟨a,ha,ta⟩:=ones_work_call xs pos
  have ja:=work_jump_trace (.copy false (.seal .done)) (.scan .read) (seeded xs) pos rfl
  obtain ⟨b,hb,tb⟩:=scan_work_call xs pos
  have jb:=work_jump_trace (.scan .done) (.copy true (.init (.erase 0))) (counted xs) pos rfl
  obtain ⟨c,hc,tc⟩:=complement_work_call xs pos
  have jc:=work_jump_trace (.copy true (.seal .done)) (.erase 2) (copied xs) pos rfl
  obtain ⟨d,hd,td⟩:=erase_work_call xs pos
  have jd:=work_jump_trace (.erase 0) .done (final xs) pos rfl
  refine ⟨a+(1+(b+(1+(c+(1+(d+1)))))),by omega,?_⟩
  exact NativeCountedLoop.trace_trans ta (NativeCountedLoop.trace_trans ja
    (NativeCountedLoop.trace_trans tb (NativeCountedLoop.trace_trans jb
      (NativeCountedLoop.trace_trans tc (NativeCountedLoop.trace_trans jc (NativeCountedLoop.trace_trans td jd))))))

end TransposeFollowup.InputMeasure
