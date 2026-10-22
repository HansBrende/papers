import TransposeFollowup.InputMeasureRun
import TransposeFollowup.NativeTrimRun

/-! A compact length word from the original unprepared input. The paid
three-tape measurement is followed by physical high-zero trimming. -/
namespace TransposeFollowup.CompactInputMeasure
open FixedTapeCompiler CopyMachine
open InputMeasure (Port Bank)
set_option autoImplicit false

def binding : FinitePortBinding Port Port where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros;simp [eq_comm]

inductive Label | load (pc : InputMeasure.Label) | trim (pc : NativeTrim.Label) | done
  deriving DecidableEq,Fintype

def start : Label := .load InputMeasure.start

def program : NativeIO.Program Port Label
  | .load .done => .work (.jump (.trim .scan))
  | .load pc => NativeIOEmbedding.boundInstruction binding Label.load (InputMeasure.program pc)
  | .trim .done => .work (.jump .done)
  | .trim pc => .work ((InputMeasure.singleBinding 2).instruction Label.trim (NativeTrim.program pc))
  | .done => .work .halt

theorem load_code (pc : InputMeasure.Label) (hh : InputMeasure.program pc≠.work .halt)
    (_ : InputMeasure.program pc≠.work .reject) :
    program (.load pc)=NativeIOEmbedding.instruction binding.ports Label.load (InputMeasure.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem trim_code (pc : NativeTrim.Label) (hh : NativeTrim.program pc≠.halt) (_ : NativeTrim.program pc≠.reject) :
    NativeIO.workProgram program (.trim pc)=MicrocodeEmbedding.instruction (InputMeasure.singleBinding 2).ports
      Label.trim (NativeTrim.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port Label :=
  ⟨workCfg pc s pos,ip,outRev⟩
def final (xs ys : List Bool) : Bank := InputMeasure.bank (Counter.marked xs) ⟨[],[]⟩ (Counter.marked ys)

abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem embed_load (pc : InputMeasure.Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool)
    (frame : MicrocodeEmbedding.Frame Port) :
    NativeIOEmbedding.embed binding.ports Label.load (InputMeasure.cfg pc s pos ip outRev) frame=
      cfg (.load pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed InputMeasure.cfg InputMeasure.workCfg cfg workCfg
  simp only [← binding.values_eq_extend]
  rfl

theorem embed_trim (pc : NativeTrim.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (InputMeasure.singleBinding 2).ports Label.trim
      (NativeTrim.cfg pc word (fun _ => pos 2)).denote (InputMeasure.frame s pos)=
      workCfg (.trim pc) (Function.update s 2 word) pos := by
  unfold MicrocodeEmbedding.embed NativeTrim.cfg NativeZipper.Config.denote Microcode.Config.denote
    workCfg InputMeasure.frame
  simp only [← (InputMeasure.singleBinding 2).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> simp [InputMeasure.singleBinding,FinitePortBinding.values]

theorem load_call (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ 37*w.length+53, Trace w t (cfg start InputMeasure.initial pos 0 outRev)
      (cfg (.load .done) (InputMeasure.final w) pos w.length outRev) := by
  obtain ⟨t,ht,htr⟩ := InputMeasure.complete_trace w pos outRev
  have he := NativeIOEmbedding.trace_embed binding.ports Label.load InputMeasure.program program
    (InputMeasure.frame InputMeasure.initial pos) w load_code htr
  exact ⟨t,ht,by simpa only [embed_load,start] using he⟩

theorem trim_call (w : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=w.length ∧ ys.length=w.length.size ∧
    ∃ t ≤ 4*w.length+10, Trace w t (cfg (.trim .scan) (InputMeasure.final w) pos ip outRev)
      (cfg (.trim .done) (final w ys) pos ip outRev) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := NativeTrim.complete_trace (MeasuredWord.result w.length) (fun _ => pos 2)
  have he := MicrocodeEmbedding.trace_embed (InputMeasure.singleBinding 2).ports Label.trim NativeTrim.program
    (NativeIO.workProgram program) (InputMeasure.frame (InputMeasure.final w) pos) trim_code htr
  have hi : Function.update (InputMeasure.final w) 2 (Counter.marked (MeasuredWord.result w.length))=InputMeasure.final w :=
    Function.update_eq_self _ _
  have hf : Function.update (InputMeasure.final w) 2 (Counter.marked ys)=final w ys := by
    funext p;fin_cases p <;> simp [InputMeasure.final,final,InputMeasure.bank]
  refine ⟨ys,hy,?_,?_,t,?_,?_⟩
  · simpa only [MeasuredWord.result_value] using hv
  · simpa only [MeasuredWord.result_value] using hl
  · simpa only [MeasuredWord.result_length] using ht
  · simpa only [embed_trim,hi,hf,cfg] using NativeIO.lift_work_trace program w ip outRev he

theorem jump_trace (w : List Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool)
    (h : program pc=.work (.jump next)) : Trace w 1 (cfg pc s pos ip outRev) (cfg next s pos ip outRev) :=
  NativeIO.jump_trace _ _ _ _ h

theorem complete_trace (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=w.length ∧ ys.length=w.length.size ∧
    ∃ t ≤ 41*w.length+65, Trace w t (cfg start InputMeasure.initial pos 0 outRev)
      (cfg .done (final w ys) pos w.length outRev) := by
  obtain ⟨a,ha,ta⟩ := load_call w pos outRev
  obtain ⟨ys,hy,hv,hl,b,hb,tb⟩ := trim_call w pos w.length outRev
  have ja := jump_trace w (.load .done) (.trim .scan) (InputMeasure.final w) pos w.length outRev rfl
  have jb := jump_trace w (.trim .done) .done (final w ys) pos w.length outRev rfl
  exact ⟨ys,hy,hv,hl,a+1+b+1,by omega,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta ja) tb) jb⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem native_complete (w : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=w.length ∧ ys.length=w.length.size ∧
    ∃ t ≤ 41*w.length+65,
      Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
        some ((cfg .done (final w ys) (fun _ => 0) w.length []).denote nativeEncoding program) ∧
      Transpose.step nativeMachine w ((cfg .done (final w ys) (fun _ => 0) w.length []).denote nativeEncoding program)=none := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace w (fun _ => 0) []
  refine ⟨ys,hy,hv,hl,t,ht,?_,?_⟩
  · have hb : (cfg start InputMeasure.initial (fun _ => 0) 0 []).denote nativeEncoding program=Transpose.init nativeMachine :=
      NativeIO.blank_denote nativeEncoding program start (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN nativeEncoding program w htr
  · apply (NativeIO.step_none_iff nativeEncoding program w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : NativeIO.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.work .halt → program pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program pc))
    (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=w.length ∧ ys.length=w.length.size ∧
    ∃ t ≤ 41*w.length+65,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg start InputMeasure.initial pos 0 outRev) frame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels (cfg .done (final w ys) pos w.length outRev) frame).denote encoding target) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace w pos outRev
  exact ⟨ys,hy,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels program target frame w hc htr⟩

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=115 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=115
  decide +kernel

end TransposeFollowup.CompactInputMeasure
