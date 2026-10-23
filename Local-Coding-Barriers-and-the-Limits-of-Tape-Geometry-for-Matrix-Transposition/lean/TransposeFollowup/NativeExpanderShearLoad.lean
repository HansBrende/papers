import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.RawDimensionLoader
import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.NativeExpanderShearHalf

/-! Uniform raw setup for a two-bank shear. The actual raw payload determines
the canonical dimension d. The caller retains a physical copy of d and
replaces the generator dimension by d/2, paying both subroutines and links. -/
namespace TransposeFollowup.NativeExpanderShearLoad
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | raw (p : RawDimensionLoader.Port) | dimension
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def halfPort : Port := .raw (.loader (.work .candidate))

def rawBinding : FinitePortBinding RawDimensionLoader.Port Port where
  ports := ⟨Port.raw,by intro p q h; cases h; rfl⟩
  decode := fun p => match p with | .raw p => some p | _ => none
  decode_spec := by decide +kernel

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![halfPort,.dimension],by decide +kernel⟩
  decode := fun p => if p=halfPort then some 0 else if p=.dimension then some 1 else none
  decode_spec := by decide +kernel

def halfBinding : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => halfPort,by intro p q h; exact Subsingleton.elim _ _⟩
  decode := fun p => if p=halfPort then some 0 else none
  decode_spec := by decide +kernel

inductive Label
  | raw (pc : RawDimensionLoader.Label)
  | copy (pc : NativeMappedCopy.Label)
  | half (pc : NativeExpanderShearHalf.Label)
  deriving DecidableEq, Fintype

def start : Label := .raw RawDimensionLoader.start

def program : NativeIO.Program Port Label
  | .raw (.load .done) => .work (.jump (.copy (.init (.erase 0))))
  | .raw pc => NativeIOEmbedding.boundInstruction rawBinding Label.raw (RawDimensionLoader.program pc)
  | .copy (.seal .done) => .work (.jump (.half .left))
  | .copy pc => .work (copyBinding.instruction Label.copy (NativeMappedCopy.program id pc))
  | .half pc => .work (halfBinding.instruction Label.half (NativeExpanderShearHalf.program pc))

theorem raw_code (pc : RawDimensionLoader.Label)
    (hh : RawDimensionLoader.program pc≠.work .halt)
    (_ : RawDimensionLoader.program pc≠.work .reject) :
    program (.raw pc)=NativeIOEmbedding.instruction rawBinding.ports Label.raw (RawDimensionLoader.program pc) := by
  have h : pc≠.load .done := by intro h; subst pc; exact hh rfl
  cases pc with
  | measure pc => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | load pc =>
    cases pc <;> simp_all [program,NativeIOEmbedding.bound_instruction_eq]

theorem copy_code (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    NativeIO.workProgram program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy
      (NativeMappedCopy.program id pc) := by
  have h : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc with
  | init pc => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]
  | append pc => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]
  | «seal» pc => cases pc <;> simp_all [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

theorem half_code (pc : NativeExpanderShearHalf.Label)
    (_ : NativeExpanderShearHalf.program pc≠.halt) (_ : NativeExpanderShearHalf.program pc≠.reject) :
    NativeIO.workProgram program (.half pc)=MicrocodeEmbedding.instruction halfBinding.ports Label.half
      (NativeExpanderShearHalf.program pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port Label :=
  ⟨workCfg pc s pos,ip,outRev⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩
def initial : Bank := fun _ => ⟨[],[]⟩
def loaded (w xs : List Bool) : Bank
  | .raw p => RawDimensionLoader.finalBank w xs p | .dimension => ⟨[],[]⟩
def copied (w xs : List Bool) : Bank
  | .raw p => RawDimensionLoader.finalBank w xs p | .dimension => Counter.marked xs

def finalBank (w xs ys : List Bool) : Bank
  | .raw p => RawDimensionLoader.finalBank w ys p | .dimension => Counter.marked xs

def finalPositions (pos : Port → ℤ) : Port → ℤ :=
  Function.update pos halfPort (pos halfPort+1)

abbrev Trace (w : List Bool) := OperationalTrace.Trace (NativeIO.step program w) (NativeIO.Active program)

theorem embed_raw (pc : RawDimensionLoader.Label) (s : RawDimensionLoader.Bank)
    (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed rawBinding.ports Label.raw
      (RawDimensionLoader.cfg pc s (fun p => pos (.raw p)) ip outRev) (frame initial pos)=
      cfg (.raw pc) (rawBinding.values s initial) pos ip outRev := by
  exact NativeExpanderShearFrames.embed_io_project rawBinding Label.raw pc s initial pos ip outRev

theorem raw_call (w : List Bool) (d : ℕ) (hd : 1≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
    ∃ t ≤ 8300*w.length, Trace w t (cfg start initial pos 0 outRev)
      (cfg (.raw (.load .done)) (loaded w xs) pos w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := RawDimensionLoader.complete_trace w d hd hw (fun p => pos (.raw p)) outRev
  have he := NativeIOEmbedding.trace_embed rawBinding.ports Label.raw RawDimensionLoader.program program
    (frame initial pos) w raw_code htr
  have hi : rawBinding.values RawDimensionLoader.initial initial=initial := by
    funext p; cases p <;> rfl
  have hf : rawBinding.values (RawDimensionLoader.finalBank w xs) initial=loaded w xs := by
    funext p; cases p <;> rfl
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_raw,hi,hf,start] using he⟩

theorem embed_copy (pc : NativeMappedCopy.Label) (s t : Tape Bool)
    (w xs : List Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc s t (fun p => pos (copyBinding.ports p))) (frame (loaded w xs) pos)=
      workCfg (.copy pc) (copyBinding.values (NativeMappedCopy.bank s t) (loaded w xs)) pos := by
  exact copyBinding.embed_bank_project Label.copy pc (NativeMappedCopy.bank s t) (loaded w xs) pos

theorem copy_call (w xs : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*xs.length+14, Trace w t
      (cfg (.copy (.init (.erase 0))) (loaded w xs) pos ip outRev)
      (cfg (.copy (.seal .done)) (copied w xs) pos ip outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy (NativeMappedCopy.program id)
    (NativeIO.workProgram program) (frame (loaded w xs) pos) copy_code htr
  have hi : copyBinding.values (NativeMappedCopy.bank (Counter.marked xs) ⟨[],[]⟩) (loaded w xs)=loaded w xs := by
    funext p; cases p <;> try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals rfl
  have hf : copyBinding.values (NativeMappedCopy.bank (Counter.marked xs) (Counter.marked (xs.map id))) (loaded w xs)=copied w xs := by
    simp only [List.map_id_fun]
    funext p; cases p <;> try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals rfl
  exact ⟨t,ht,by simpa only [embed_copy,hi,hf,cfg] using NativeIO.lift_work_trace program w ip outRev he⟩

theorem embed_half (pc : NativeExpanderShearHalf.Label) (word : Tape Bool)
    (w xs : List Bool) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed halfBinding.ports Label.half
      (NativeExpanderShearHalf.cfg pc word (fun _ => z)).denote (frame (copied w xs) pos)=
      workCfg (.half pc) (halfBinding.values (fun _ => word) (copied w xs)) (Function.update pos halfPort z) := by
  unfold MicrocodeEmbedding.embed NativeExpanderShearHalf.cfg NativeZipper.Config.denote
    Microcode.Config.denote workCfg frame
  simp only [← halfBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try (rename_i innerPort; cases innerPort)
  all_goals try (rename_i innerPort; cases innerPort)
  all_goals try (rename_i innerPort; cases innerPort)
  all_goals rfl

theorem half_call (w xs : List Bool) (a : Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3, Trace w t (cfg (.half .left) (copied w (a::xs)) pos ip outRev)
      (cfg (.half .done) (finalBank w (a::xs) xs) (finalPositions pos) ip outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearHalf.half_trace a xs (fun _ => pos halfPort)
  have he := MicrocodeEmbedding.trace_embed halfBinding.ports Label.half NativeExpanderShearHalf.program
    (NativeIO.workProgram program) (frame (copied w (a::xs)) pos) half_code htr
  have hi : halfBinding.values (fun _ => Counter.marked (a::xs)) (copied w (a::xs))=copied w (a::xs) := by
    funext p; cases p <;> try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals rfl
  have hf : halfBinding.values (fun _ => Counter.marked xs) (copied w (a::xs))=finalBank w (a::xs) xs := by
    funext p; cases p <;> try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals try (rename_i innerPort; cases innerPort)
    all_goals rfl
  refine ⟨t,ht,?_⟩
  simpa only [embed_half,hi,hf,Function.update_eq_self,finalPositions,cfg] using
    NativeIO.lift_work_trace program w ip outRev he

theorem jump_trace (w : List Bool) (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (ip : ℤ) (outRev : List Bool) (h : program pc=.work (.jump next)) :
    Trace w 1 (cfg pc s pos ip outRev) (cfg next s pos ip outRev) := by
  exact NativeIO.jump_trace program w (cfg pc s pos ip outRev) next h

theorem complete_trace (w : List Bool) (d : ℕ) (hd : 2≤d) (hw : w.length=Transpose.inputLength d)
    (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs ys,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ys ∧ Counter.value ys=d/2 ∧ ys.length=(d/2).size ∧
    ∃ t ≤ 8300*w.length+6*d.size+19, Trace w t (cfg start initial pos 0 outRev)
      (cfg (.half .done) (finalBank w xs ys) (finalPositions pos) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩ := raw_call w d (by omega) hw pos outRev
  obtain ⟨b,hb,tb⟩ := copy_call w xs pos w.length outRev
  have j1 := jump_trace w (.raw (.load .done)) (.copy (.init (.erase 0))) (loaded w xs) pos w.length outRev rfl
  have j2 := jump_trace w (.copy (.seal .done)) (.half .left) (copied w xs) pos w.length outRev rfl
  cases xs with
  | nil => simp [Counter.value] at hv; omega
  | cons bit ys =>
    obtain ⟨c,hc,tc⟩ := half_call w ys bit pos w.length outRev
    have hy := NativeExpanderShearHalf.normalized_tail bit ys hx
    have hyv : Counter.value ys=d/2 := (NativeExpanderShearHalf.half_value bit ys).trans (congrArg (fun n => n/2) hv)
    refine ⟨bit::ys,ys,hx,hv,hl,hy,hyv,?_,a+1+b+1+c,?_,?_⟩
    · simpa only [hyv] using NativeTrim.normalized_length ys hy
    · omega
    · exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
        (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeIO.machine nativeEncoding program

theorem native_complete (w : List Bool) (d : ℕ) (hd : 2≤d) (hw : w.length=Transpose.inputLength d) :
    ∃ xs ys,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ys ∧ Counter.value ys=d/2 ∧ ys.length=(d/2).size ∧
    ∃ t ≤ 8300*w.length+6*d.size+19,
      Transpose.stepN nativeMachine w t (Transpose.init nativeMachine)=
      some ((cfg (.half .done) (finalBank w xs ys) (finalPositions (fun _ => 0)) w.length []).denote nativeEncoding program) ∧
      Transpose.step nativeMachine w
        ((cfg (.half .done) (finalBank w xs ys) (finalPositions (fun _ => 0)) w.length []).denote nativeEncoding program)=none := by
  obtain ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,htr⟩ := complete_trace w d hd hw (fun _ => 0) []
  refine ⟨xs,ys,hx,hv,hl,hy,hyv,hyl,t,ht,?_,?_⟩
  · have hi : (cfg start initial (fun _ => 0) 0 []).denote nativeEncoding program=Transpose.init nativeMachine :=
      NativeIO.blank_denote nativeEncoding program start (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN nativeEncoding program w htr
  · apply (NativeIO.step_none_iff nativeEncoding program w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,NativeExpanderShearHalf.program]

end TransposeFollowup.NativeExpanderShearLoad
