import TransposeFollowup.InputMeasureCalls

namespace TransposeFollowup.InputMeasure
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem complete_trace (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ 37*w.length+53, Trace w t (cfg start initial pos 0 outRev)
      (cfg .done (final w) pos w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := load_call w pos outRev
  have ja := jump_trace w (.load .done) (.copy false (.init (.erase 0))) (loaded w) pos w.length outRev rfl
  obtain ⟨b,hb,tb⟩ := ones_call w pos w.length outRev
  have jb := jump_trace w (.copy false (.seal .done)) (.scan .read) (seeded w) pos w.length outRev rfl
  obtain ⟨c,hc,tc⟩ := scan_call w pos w.length outRev
  have jc := jump_trace w (.scan .done) (.copy true (.init (.erase 0))) (counted w) pos w.length outRev rfl
  obtain ⟨d,hd,td⟩ := complement_call w pos w.length outRev
  have jd := jump_trace w (.copy true (.seal .done)) (.erase 2) (copied w) pos w.length outRev rfl
  obtain ⟨e,he,te⟩ := erase_call w pos w.length outRev
  have je := jump_trace w (.erase 0) .done (final w) pos w.length outRev rfl
  refine ⟨a+1+b+1+c+1+d+1+e+1,by omega,?_⟩
  exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta ja) tb) jb) tc) jc) td) jd) te) je

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem native_complete (w : List Bool) : ∃ t ≤ 37*w.length+53,
    Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
      some ((cfg .done (final w) (fun _ => 0) w.length []).denote nativeEncoding program) ∧
    Transpose.step nativeMachine w ((cfg .done (final w) (fun _ => 0) w.length []).denote nativeEncoding program)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace w (fun _ => 0) []
  refine ⟨t,ht,?_,?_⟩
  · have hb : (cfg start initial (fun _ => 0) 0 []).denote nativeEncoding program=Transpose.init nativeMachine :=
      NativeIO.blank_denote nativeEncoding program start (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN nativeEncoding program w htr
  · apply (NativeIO.step_none_iff nativeEncoding program w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program]

theorem native_measure (w : List Bool) :
    ∃ result : List Bool,Counter.value result=w.length ∧ result.length=w.length ∧
    ∃ t ≤ 37*w.length+53,
      Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
        some ((cfg .done (bank (Counter.marked w) ⟨[],[]⟩ (Counter.marked result)) (fun _ => 0) w.length []).denote nativeEncoding program) ∧
      Transpose.step nativeMachine w
        ((cfg .done (bank (Counter.marked w) ⟨[],[]⟩ (Counter.marked result)) (fun _ => 0) w.length []).denote nativeEncoding program)=none :=
  ⟨MeasuredWord.result w.length,MeasuredWord.result_value _,MeasuredWord.result_length _,native_complete w⟩

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.work .halt → program pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program pc))
    (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ 37*w.length+53,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg start initial pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels (cfg .done (final w) pos w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨t,ht,htr⟩ := complete_trace w pos outRev
  exact ⟨t,ht,NativeIOEmbedding.native_call encoding ports labels program target outerFrame w hc htr⟩

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=100 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=100
  decide +kernel

end TransposeFollowup.InputMeasure
