import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.NativeExpanderShearLoad
import TransposeFollowup.NativeExpanderShearGenerate

/-! One fixed raw-input machine loads d and d/2 and executes the existing
rational matching generator at d/2. The original payload and dimension
survive. All loading, enumeration, normalization, deduplication and opcode
writing have actual native traces with a linear bound in the raw length. -/
namespace TransposeFollowup.NativeExpanderShearMetadata
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

inductive Port | generator (p : OpcodeGenerator.Port) | dimension
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def loadPort : NativeExpanderShearLoad.Port → Port
  | .raw p => .generator (RawEnumeration.rawPort p)
  | .dimension => .dimension

def loadBinding : FinitePortBinding NativeExpanderShearLoad.Port Port where
  ports := ⟨loadPort,by decide +kernel⟩
  decode := fun p => match p with
    | .generator p => (RawEnumeration.rawBinding.decode p).map NativeExpanderShearLoad.Port.raw
    | .dimension => some .dimension
  decode_spec := by decide +kernel

def generatorBinding : FinitePortBinding OpcodeGenerator.Port Port where
  ports := ⟨Port.generator,by intro p q h; cases h; rfl⟩
  decode := fun p => match p with | .generator p => some p | _ => none
  decode_spec := by decide +kernel

inductive Label (F : Fin (r+1) → RationalMobius)
  | load (pc : NativeExpanderShearLoad.Label)
  | generate (pc : OpcodeGenerator.Label F)
  deriving DecidableEq, Fintype

def start (F : Fin (r+1) → RationalMobius) : Label F := .load NativeExpanderShearLoad.start

def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .load (.half .done) => .work (.jump (.generate (NativeExpanderShearGenerate.entry F)))
  | .load pc => NativeIOEmbedding.boundInstruction loadBinding Label.load (NativeExpanderShearLoad.program pc)
  | .generate pc => NativeIOEmbedding.boundInstruction generatorBinding Label.generate (OpcodeGenerator.program F pc)

theorem load_code (F : Fin (r+1) → RationalMobius) (pc : NativeExpanderShearLoad.Label)
    (hh : NativeExpanderShearLoad.program pc≠.work .halt)
    (_ : NativeExpanderShearLoad.program pc≠.work .reject) :
    program F (.load pc)=NativeIOEmbedding.instruction loadBinding.ports Label.load (NativeExpanderShearLoad.program pc) := by
  cases pc with
  | half pc => cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem generate_code (F : Fin (r+1) → RationalMobius) (pc : OpcodeGenerator.Label F)
    (_ : OpcodeGenerator.program F pc≠.work .halt) (_ : OpcodeGenerator.program F pc≠.work .reject) :
    program F (.generate pc)=NativeIOEmbedding.instruction generatorBinding.ports Label.generate (OpcodeGenerator.program F pc) := by
  simp only [program,NativeIOEmbedding.bound_instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) :
    NativeMicrocode.Config Port (Label F) := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ)
    (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) := ⟨workCfg pc s pos,ip,outRev⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
def initial : Bank := fun _ => ⟨[],[]⟩
def liftBank (xs : List Bool) (s : OpcodeGenerator.Bank) : Bank
  | .generator p => s p | .dimension => Counter.marked xs

def loaded (w xs ys : List Bool) : Bank := liftBank xs (RawEnumeration.loaded w ys [])
def finalBank (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool) : Bank :=
  liftBank xs (OpcodeGenerator.finalBank F w ys)
def loadedPositions (pos : Port → ℤ) : Port → ℤ :=
  Function.update pos (.generator (.enumeration .source)) (pos (.generator (.enumeration .source))+1)
def finalPositions (F : Fin (r+1) → RationalMobius) (ys : List Bool) (pos : Port → ℤ) : Port → ℤ :=
  generatorBinding.values (OpcodeGenerator.finalPositions F ys (fun p => loadedPositions pos (.generator p))) (loadedPositions pos)

abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem embed_load (F : Fin (r+1) → RationalMobius) (pc : NativeExpanderShearLoad.Label)
    (s : NativeExpanderShearLoad.Bank) (pos : Port → ℤ) (rpos : NativeExpanderShearLoad.Port → ℤ)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed loadBinding.ports (Label.load (F:=F)) (NativeExpanderShearLoad.cfg pc s rpos ip outRev)
      (frame initial pos)=cfg (.load pc) (loadBinding.values s initial) (loadBinding.values rpos pos) ip outRev := by
  exact NativeExpanderShearFrames.embed_io loadBinding (Label.load (F:=F)) pc s initial pos rpos ip outRev

theorem load_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (d : ℕ)
    (hd : 2≤d) (hw : w.length=Transpose.inputLength d) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs ys,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ys ∧ Counter.value ys=d/2 ∧ ys.length=(d/2).size ∧
    ∃ t ≤ 8300*w.length+6*d.size+19, Trace F w t (cfg (start F) initial pos 0 outRev)
      (cfg (.load (.half .done)) (loaded w xs ys) (loadedPositions pos) w.length outRev) := by
  obtain ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,htr⟩ := NativeExpanderShearLoad.complete_trace w d hd hw
    (fun p => pos (loadBinding.ports p)) outRev
  have he := NativeIOEmbedding.trace_embed loadBinding.ports (Label.load (F:=F)) NativeExpanderShearLoad.program
    (program F) (frame initial pos) w (load_code F) htr
  have hi : loadBinding.values NativeExpanderShearLoad.initial initial=initial := by
    funext p; fin_cases p <;> rfl
  have hf : loadBinding.values (NativeExpanderShearLoad.finalBank w xs ys) initial=loaded w xs ys := by
    funext p; fin_cases p <;> rfl
  have hpi : loadBinding.values (fun p => pos (loadBinding.ports p)) pos=pos := by
    funext p; fin_cases p <;> rfl
  have hpf : loadBinding.values (NativeExpanderShearLoad.finalPositions (fun p => pos (loadBinding.ports p))) pos=loadedPositions pos := by
    funext p; fin_cases p <;> rfl
  exact ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,by simpa only [embed_load,hi,hf,hpi,hpf,start] using he⟩

theorem embed_generate (F : Fin (r+1) → RationalMobius) (pc : OpcodeGenerator.Label F)
    (s base : OpcodeGenerator.Bank) (xs : List Bool) (pos : Port → ℤ) (rpos : OpcodeGenerator.Port → ℤ)
    (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed generatorBinding.ports (Label.generate (F:=F)) (OpcodeGenerator.cfg pc s rpos ip outRev)
      (frame (liftBank xs base) pos)=cfg (.generate pc) (liftBank xs s) (generatorBinding.values rpos pos) ip outRev := by
  unfold NativeIOEmbedding.embed OpcodeGenerator.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed OpcodeGenerator.workCfg workCfg frame
  simp only [← generatorBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem generate_call (F : Fin (r+1) → RationalMobius) (w xs ys : List Bool) (n : ℕ)
    (hn : 1≤n) (hv : Counter.value ys=n) (hl : ys.length=n.size) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ t ≤ OpcodeGenerator.coefficient F*Transpose.inputLength n,
      Trace F w t (cfg (.generate (NativeExpanderShearGenerate.entry F)) (loaded w xs ys) (loadedPositions pos) w.length outRev)
        (cfg (.generate (.schedule .done)) (finalBank F w xs ys) (finalPositions F ys pos) w.length outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearGenerate.complete_trace F w ys n hn hv hl
    (fun p => loadedPositions pos (.generator p)) outRev
  have he := NativeIOEmbedding.trace_embed generatorBinding.ports (Label.generate (F:=F)) (OpcodeGenerator.program F)
    (program F) (frame (loaded w xs ys) (loadedPositions pos)) w (generate_code F) htr
  have hpi : generatorBinding.values (fun p => loadedPositions pos (.generator p)) (loadedPositions pos)=loadedPositions pos := by
    funext p; cases p <;> rfl
  exact ⟨t,ht,by simpa only [loaded,embed_generate,hpi,finalBank,finalPositions] using he⟩

def coefficient (F : Fin (r+1) → RationalMobius) := 8326+OpcodeGenerator.coefficient F

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (d : ℕ)
    (hd : 2≤d) (hw : w.length=Transpose.inputLength d) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs ys,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ys ∧ Counter.value ys=d/2 ∧ ys.length=(d/2).size ∧
    ∃ t ≤ coefficient F*w.length, Trace F w t (cfg (start F) initial pos 0 outRev)
      (cfg (.generate (.schedule .done)) (finalBank F w xs ys) (finalPositions F ys pos) w.length outRev) := by
  obtain ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,a,ha,ta⟩ := load_call F w d hd hw pos outRev
  have hm : 1≤d/2 := by omega
  obtain ⟨b,hb,tb⟩ := generate_call F w xs ys (d/2) hm hyv hyl pos outRev
  have tj : Trace F w 1 (cfg (.load (.half .done)) (loaded w xs ys) (loadedPositions pos) w.length outRev)
      (cfg (.generate (NativeExpanderShearGenerate.entry F)) (loaded w xs ys) (loadedPositions pos) w.length outRev) :=
    NativeIO.jump_trace (program F) w _ _ rfl
  have hmono : Transpose.inputLength (d/2)≤w.length := by
    rw [hw]
    exact DimensionCandidate.length_strictMono.monotone (by omega)
  have hsize : d.size≤w.length := by
    have hdsize : d.size≤d := Nat.size_le.mpr Nat.lt_two_pow_self
    have hdL := DimensionCandidate.dimension_le_length d (by omega)
    omega
  have hL : 1≤w.length := by
    have hdL := DimensionCandidate.dimension_le_length d (by omega)
    omega
  refine ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,a+1+b,?_,
    NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb⟩
  unfold coefficient
  have hb' := hb.trans (Nat.mul_le_mul_left (OpcodeGenerator.coefficient F) hmono)
  nlinarith

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (d : ℕ)
    (hd : 2≤d) (hw : w.length=Transpose.inputLength d) :
    ∃ xs ys,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ys ∧ Counter.value ys=d/2 ∧ ys.length=(d/2).size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.generate (.schedule .done)) (finalBank F w xs ys) (finalPositions F ys (fun _ => 0)) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg (.generate (.schedule .done)) (finalBank F w xs ys)
        (finalPositions F ys (fun _ => 0)) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,htr⟩ := complete_trace F w d hd hw (fun _ => 0) []
  refine ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,?_,?_⟩
  · have hi : (cfg (start F) initial (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) :=
      NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,NativeIOEmbedding.boundInstruction,
      OpcodeGenerator.program,FinitePortBinding.instruction,VertexScheduler.program]

end TransposeFollowup.NativeExpanderShearMetadata
