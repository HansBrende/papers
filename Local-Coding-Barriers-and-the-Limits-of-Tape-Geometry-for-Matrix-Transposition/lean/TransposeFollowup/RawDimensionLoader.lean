import TransposeFollowup.DimensionLoaderRun
import TransposeFollowup.CompactInputMeasure

/-! Uniform dimension loading from the original raw input and entirely blank
work tapes. A payload copy and a short dimension word remain; every other
work tape is blank. The original input is read only. -/
namespace TransposeFollowup.RawDimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | payload | loader (p : DimensionLoader.Port)
  deriving DecidableEq,Fintype
abbrev Bank := Port → Tape Bool

def measurePorts : Fin 3 → Port := ![.payload,.loader .extra,.loader .source]
def measureBinding : FinitePortBinding (Fin 3) Port where
  ports:=⟨measurePorts,by decide +kernel⟩
  decode:=fun p => match p with
    | .payload => some 0 | .loader .extra => some 1 | .loader .source => some 2 | _ => none
  decode_spec:=by decide +kernel

def loaderBinding : FinitePortBinding DimensionLoader.Port Port where
  ports:=⟨Port.loader,by intro p q h;cases h;rfl⟩
  decode:=fun p => match p with | .loader p => some p | _ => none
  decode_spec:=by decide +kernel

inductive Label | measure (pc : CompactInputMeasure.Label) | load (pc : DimensionLoader.Label)
  deriving DecidableEq,Fintype

def start : Label := .measure CompactInputMeasure.start

def program : NativeIO.Program Port Label
  | .measure .done => .work (.jump (.load DimensionLoader.start))
  | .measure pc => NativeIOEmbedding.boundInstruction measureBinding Label.measure (CompactInputMeasure.program pc)
  | .load pc => .work (loaderBinding.instruction Label.load (DimensionLoader.program pc))

theorem measure_code (pc : CompactInputMeasure.Label) (hh : CompactInputMeasure.program pc≠.work .halt)
    (_ : CompactInputMeasure.program pc≠.work .reject) :
    program (.measure pc)=NativeIOEmbedding.instruction measureBinding.ports Label.measure (CompactInputMeasure.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem loader_code (pc : DimensionLoader.Label) (_ : DimensionLoader.program pc≠.halt) (_ : DimensionLoader.program pc≠.reject) :
    NativeIO.workProgram program (.load pc)=MicrocodeEmbedding.instruction loaderBinding.ports Label.load (DimensionLoader.program pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port Label :=
  ⟨workCfg pc s pos,ip,outRev⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
def initial : Bank := fun _ => ⟨[],[]⟩
def liftBank (payload : List Bool) (s : DimensionLoader.Bank) : Bank
  | .payload => Counter.marked payload | .loader p => s p

def loaded (payload xs : List Bool) : Bank := liftBank payload (DimensionLoader.initial xs)
def finalBank (payload ys : List Bool) : Bank := liftBank payload (DimensionLoader.finalBank ys)

abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem embed_measure (pc : CompactInputMeasure.Label) (s : InputMeasure.Bank) (base : Bank) (pos : Port → ℤ)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed measureBinding.ports Label.measure
      (CompactInputMeasure.cfg pc s (fun p => pos (measurePorts p)) ip outRev) (frame base pos)=
      cfg (.measure pc) (measureBinding.values s base) pos ip outRev := by
  unfold NativeIOEmbedding.embed CompactInputMeasure.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed CompactInputMeasure.workCfg workCfg frame
  simp only [← measureBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try (rename_i q;cases q) <;> try (rename_i r;cases r)
  all_goals rfl

theorem measure_call (w : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=w.length ∧ xs.length=w.length.size ∧
    ∃ t ≤ 41*w.length+65, Trace w t (cfg start initial pos 0 outRev)
      (cfg (.measure .done) (loaded w xs) pos w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := CompactInputMeasure.complete_trace w (fun p => pos (measurePorts p)) outRev
  have he := NativeIOEmbedding.trace_embed measureBinding.ports Label.measure CompactInputMeasure.program program
    (frame initial pos) w measure_code htr
  have hi : measureBinding.values InputMeasure.initial initial=initial := by
    funext p;cases p <;> try (rename_i q;cases q) <;> try (rename_i r;cases r)
    all_goals rfl
  have hf : measureBinding.values (CompactInputMeasure.final w xs) initial=loaded w xs := by
    funext p;cases p <;> try (rename_i q;cases q) <;> try (rename_i r;cases r)
    all_goals rfl
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_measure,hi,hf,start] using he⟩

theorem embed_loader (pc : DimensionLoader.Label) (s base : DimensionLoader.Bank) (payload : List Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed loaderBinding.ports Label.load
      (DimensionLoader.cfg pc s (fun p => pos (.loader p))) (frame (liftBank payload base) pos)=
      workCfg (.load pc) (liftBank payload s) pos := by
  unfold MicrocodeEmbedding.embed DimensionLoader.cfg workCfg frame
  simp only [← loaderBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem loader_call (w xs : List Bool) (n : ℕ) (hn : 1≤n) (hx : Counter.value xs=Transpose.inputLength n)
    (hl : xs.length=(Transpose.inputLength n).size) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8100*Transpose.inputLength n, Trace w t (cfg (.load DimensionLoader.start) (loaded w xs) pos ip outRev)
      (cfg (.load .done) (finalBank w ys) pos ip outRev) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := DimensionLoader.complete_trace xs n hn hx hl (fun p => pos (.loader p))
  have he := MicrocodeEmbedding.trace_embed loaderBinding.ports Label.load DimensionLoader.program
    (NativeIO.workProgram program) (frame (loaded w xs) pos) loader_code htr
  refine ⟨ys,hy,hv,hl,t,ht,?_⟩
  simpa only [loaded,embed_loader,cfg,finalBank] using NativeIO.lift_work_trace program w ip outRev he

theorem jump_trace (w xs : List Bool) (pos : Port → ℤ) (outRev : List Bool) :
    Trace w 1 (cfg (.measure .done) (loaded w xs) pos w.length outRev)
      (cfg (.load DimensionLoader.start) (loaded w xs) pos w.length outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

theorem complete_trace (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8300*w.length, Trace w t (cfg start initial pos 0 outRev)
      (cfg (.load .done) (finalBank w ys) pos w.length outRev) := by
  obtain ⟨xs,_,hx,hl,a,ha,ta⟩ := measure_call w pos outRev
  obtain ⟨ys,hy,hv,ly,b,hb,tb⟩ := loader_call w xs n hn (hx.trans hw) (by simpa only [hw] using hl) pos w.length outRev
  have hL : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨ys,hy,hv,ly,a+1+b,?_,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans ta (jump_trace w xs pos outRev)) tb⟩
  rw [← hw] at hb
  omega

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem native_complete (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8300*w.length,
      Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
        some ((cfg (.load .done) (finalBank w ys) (fun _ => 0) w.length []).denote nativeEncoding program) ∧
      Transpose.step nativeMachine w ((cfg (.load .done) (finalBank w ys) (fun _ => 0) w.length []).denote nativeEncoding program)=none := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace w n hn hw (fun _ => 0) []
  refine ⟨ys,hy,hv,hl,t,ht,?_,?_⟩
  · have hb : (cfg start initial (fun _ => 0) 0 []).denote nativeEncoding program=Transpose.init nativeMachine :=
      NativeIO.blank_denote nativeEncoding program start (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN nativeEncoding program w htr
  · apply (NativeIO.step_none_iff nativeEncoding program w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,DimensionLoader.program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.work .halt → program pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program pc))
    (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8300*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg start initial pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels (cfg (.load .done) (finalBank w ys) pos w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace w n hn hw pos outRev
  exact ⟨ys,hy,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels program target outerFrame w hc htr⟩

theorem fixed_resources : nativeMachine.k=15 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=1442 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=15
    decide +kernel
  · change Fintype.card Label-1+1=1442
    decide +kernel

end TransposeFollowup.RawDimensionLoader
