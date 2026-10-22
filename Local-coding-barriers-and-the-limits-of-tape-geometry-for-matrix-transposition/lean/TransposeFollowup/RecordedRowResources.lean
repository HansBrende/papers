import TransposeFollowup.DimensionScaleMeaning
import TransposeFollowup.NativeBatchErase
import TransposeFollowup.NativeUnprepare
import TransposeFollowup.RowConsumerMeaning

/-! Exact word layout for the combined preparation caller. Thresholds
use the implemented scaler; increments use image denominators; initial
crossings are the left increment and zero. This file proves the semantic
interface only. RowPreparationRun implements the copying, initialization
and composition; this definition does not make prepared words free. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler SignedComponents
set_option autoImplicit false

def denominatorStage (side : Bool) : Fin 4 := if side then 3 else 1

def deltaWord (F : RationalMobius) (source iw : List Bool) (side sign : Bool) : List Bool :=
  SourceImages.imageWord F (PaddedWord.word (PaddedWord.commonConstant F) id source)
    iw (denominatorStage side) sign

def words (F : RationalMobius) (source iw : List Bool) : RowCell.Words
  | (.threshold,side,sign) => DimensionScale.output
      (PaddedWord.word (PaddedWord.commonConstant F) id source) (DimensionScale.factor F source iw side sign)
  | (.delta,side,sign) => deltaWord F source iw side sign
  | (.crossing,side,sign) => if side then
      ArithmeticSeed.zeros (PaddedWord.word (PaddedWord.commonConstant F) id source).length
      else deltaWord F source iw false sign

theorem delta_length (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (side sign : Bool) :
    (deltaWord F source iw side sign).length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  apply SourceImages.imageWord_length _ _ _ _ hl
  rw [PaddedWord.word_length]
  unfold PaddedWord.commonConstant
  omega

theorem words_width (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    RowCell.Width (PaddedWord.word (PaddedWord.commonConstant F) id source).length (words F source iw) := by
  rintro ⟨g,side,sign⟩
  cases g with
  | threshold =>
    exact (DimensionScale.output_length _ _).trans
      (DimensionScale.factor_length F source iw hl side sign)
  | delta => exact delta_length F source iw hl side sign
  | crossing =>
    cases side
    · exact delta_length F source iw hl false sign
    · simp [words,ArithmeticSeed.zeros]

theorem delta_pair (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (side : Bool) :
    Pair.mk (Counter.value (deltaWord F source iw side false))
      (Counter.value (deltaWord F source iw side true))=
      if side then (F.componentRow i).deltaRight else (F.componentRow i).deltaLeft := by
  have h := SourceImages.image_values F source i iw hl hv (denominatorStage side)
  cases side <;> simpa [deltaWord,denominatorStage,SourceImages.upper,SourceImages.denominator,
    SourceImages.stage,SignedLinearForm.imageComponent,RationalMobius.componentRow] using h

theorem delta_component (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (side sign : Bool) :
    Counter.value (deltaWord F source iw side sign)=
      RowCell.component (if side then (F.componentRow i).deltaRight else (F.componentRow i).deltaLeft) sign := by
  have h := delta_pair F source i iw hl hv side
  cases sign
  · exact congrArg Pair.positive h
  · exact congrArg Pair.negative h

theorem words_represents (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) :
    RowCell.Represents (PaddedWord.word (PaddedWord.commonConstant F) id source).length
      (words F source iw) (F.componentRow i) 0 := by
  refine ⟨words_width F source iw hl,?_⟩
  rintro ⟨g,side,sign⟩
  rw [← NativeCounter.word_value]
  cases g with
  | threshold => exact DimensionScale.threshold_component F source i iw hl hv side sign
  | delta => exact delta_component F source i iw hl hv side sign
  | crossing =>
    cases side
    · exact delta_component F source i iw hl hv false sign
    · cases sign <;> simp [words,ArithmeticSeed.zeros,PaddedWord.value_zeroes,
        RowCell.expected,RowCell.pairAt,RowCell.component,scan,Pair.zero]

end TransposeFollowup.RowPreparation


/-! A source/image bank, four thresholds, four crossings, and one reusable
temporary counter. After scaling, that counter becomes the second scratch. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

def side (j : Fin 4) := (SourceImages.stage j).1
def sign (j : Fin 4) := (SourceImages.stage j).2
def index (a b : Bool) : Fin 4 := if a then (if b then 3 else 2) else (if b then 1 else 0)

inductive Port | images (p : SourceImages.Port) | threshold (j : Fin 4) | crossing (j : Fin 4) | temp
  deriving DecidableEq, Fintype

@[ext] structure Bank where
  images : SourceImages.Bank
  threshold : Fin 4 → Tape Bool
  crossing : Fin 4 → Tape Bool
  temp : Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .images p => s.images.tapes p | .threshold j => s.threshold j
  | .crossing j => s.crossing j | .temp => s.temp
def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank := match p with
  | .images p => {s with images := s.images.set p w}
  | .threshold j => {s with threshold := Function.update s.threshold j w}
  | .crossing j => {s with crossing := Function.update s.crossing j w}
  | .temp => {s with temp := w}

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q=Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set,Bank.tapes,Function.update]
@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p)=s := by
  cases p <;> simp [Bank.set,Bank.tapes]

def initial (n iw : List Bool) : Bank :=
  ⟨SourceImages.initial n iw,fun _ => ⟨[],[]⟩,fun _ => ⟨[],[]⟩,⟨[],[]⟩⟩
def scaleFactor (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : List Bool :=
  SourceImages.imageWord F n iw (DimensionScale.numeratorStage (side j)) (sign j)
def thresholdWord (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : List Bool :=
  DimensionScale.output n (scaleFactor F n iw j)
def crossingWord (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : List Bool :=
  if side j then ArithmeticSeed.zeros n.length else SourceImages.imageWord F n iw 1 (sign j)

def scaling (F : RationalMobius) (n iw : List Bool) (k : ℕ) : Bank :=
  ⟨SourceImages.final F n iw,fun j => if j.val<k then Counter.marked (thresholdWord F n iw j) else ⟨[],[]⟩,
    fun _ => ⟨[],[]⟩,⟨[],[]⟩⟩
def copying (F : RationalMobius) (n iw : List Bool) (k : ℕ) : Bank :=
  {scaling F n iw 4 with crossing := fun j => if j.val<k then Counter.marked (crossingWord F n iw j) else ⟨[],[]⟩}
def final (F : RationalMobius) (n iw : List Bool) : Bank :=
  {copying F n iw 4 with temp := BinaryCarry.preparedOutput}

def projectScale (j : Fin 4) (s : Bank) : DimensionScale.Bank :=
  ⟨s.images.source.base.dimension,s.images.out (DimensionScale.numeratorStage (side j)) (sign j),
    s.images.source.base.zero,s.images.source.base.scratch,s.temp,s.threshold j⟩
def placeScale (j : Fin 4) (b : DimensionScale.Bank) (s : Bank) : Bank :=
  let base := {s.images.source.base with dimension := b.dimension,zero := b.zero,scratch := b.scratch}
  let source := {s.images.source with base := base}
  let images := {s.images with source := source,out := Function.update s.images.out (DimensionScale.numeratorStage (side j)) (Function.update (s.images.out (DimensionScale.numeratorStage (side j))) (sign j) b.factor)}
  {s with images := images,temp := b.fuel,threshold := Function.update s.threshold j b.out}

theorem placeScale_project (j : Fin 4) (s : Bank) : placeScale j (projectScale j s) s=s := by
  simp [placeScale,projectScale]
theorem placeScale_update (j : Fin 4) (s : Bank) (f o : Tape Bool) :
    placeScale j {projectScale j s with fuel := f,out := o} s=
      {s with temp := f,threshold := Function.update s.threshold j o} := by
  simp [placeScale,projectScale]

theorem images_dimension (F : RationalMobius) (n iw : List Bool) :
    (SourceImages.final F n iw).source.base.dimension=Counter.marked n := by
  cases h0 : SourceEndpoints.negative F false <;> cases h1 : SourceEndpoints.negative F true <;>
    simp [SourceImages.final,SourceImages.afterForm,SourceImages.before,SourceImages.sourceFinal,
      SourceEndpoints.final,SourceEndpoints.place,SourceEndpoints.eraseStage,SourceEndpoints.afterLower,
      EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,EndpointClip.computed,EndpointClip.initial,h0,h1]

theorem factor_length (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) : (scaleFactor F n iw j).length=n.length :=
  SourceImages.imageWord_length F n iw hm hi _ _
theorem crossing_length (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) : (crossingWord F n iw j).length=n.length := by
  unfold crossingWord
  split
  · simp [ArithmeticSeed.zeros]
  · exact SourceImages.imageWord_length F n iw hm hi _ _

theorem projectScale_initial (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    projectScale j (scaling F n iw j.val)=DimensionScale.initial n (scaleFactor F n iw j) := by
  have hs := SourceImages.source_seed F n iw
  have hl := factor_length F n iw hm hi j
  apply DimensionScale.Bank.ext
  · exact images_dimension F n iw
  · exact SourceImages.final_output F n iw _ _
  · simpa only [projectScale,scaling,SourceImages.final_source,DimensionScale.initial,hl] using hs.1
  · exact hs.2.2
  · rfl
  · simp [projectScale,scaling,DimensionScale.initial]

theorem scale_initial (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    placeScale j (DimensionScale.initial n (scaleFactor F n iw j)) (scaling F n iw j.val)=scaling F n iw j.val := by
  rw [← projectScale_initial F n iw hm hi j,placeScale_project]

theorem scale_final (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    placeScale j (DimensionScale.final n (scaleFactor F n iw j)) (scaling F n iw j.val)=scaling F n iw (j.val+1) := by
  have hf : DimensionScale.final n (scaleFactor F n iw j)=
      {projectScale j (scaling F n iw j.val) with fuel := ⟨[],[]⟩,out := Counter.marked (thresholdWord F n iw j)} := by
    rw [projectScale_initial F n iw hm hi j]
    rfl
  rw [hf,placeScale_update]
  apply Bank.ext <;> try rfl
  funext k
  fin_cases j <;> fin_cases k <;> rfl

def crossingSource (j : Fin 4) : Port :=
  if side j then .images (.source (.shared .zero)) else .images (.out 1 (sign j))

theorem crossing_source (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    (copying F n iw j.val).tapes (crossingSource j)=Counter.marked (crossingWord F n iw j) := by
  have hz := (SourceImages.source_seed F n iw).1
  fin_cases j
  all_goals first
    | exact SourceImages.final_output F n iw _ _
    | exact hz

theorem copying_zero (F : RationalMobius) (n iw : List Bool) : copying F n iw 0=scaling F n iw 4 := by
  simp [copying,scaling]
theorem copying_step (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    (copying F n iw j.val).set (.crossing j) (Counter.marked (crossingWord F n iw j))=
      copying F n iw (j.val+1) := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases j <;> fin_cases k <;> rfl

end TransposeFollowup.RowPreparation


/-! A fixed finite caller for source/images, four runtime scalings, four
crossing copies and scratch initialization. Every return is a paid jump. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
set_option autoImplicit false

def imagesBinding : FinitePortBinding SourceImages.Port Port where
  ports := ⟨Port.images,by intro p q h; exact Port.images.inj h⟩
  decode := fun p => match p with | .images q => some q | _ => none
  decode_spec := by
    intro p q
    change (match p with | .images r => some r | _ => none)=some q ↔ Port.images q=p
    cases p <;> simp [eq_comm]

def scalePort (j : Fin 4) : DimensionScale.Port → Port
  | .dimension => .images (.source (.shared .dimension))
  | .factor => .images (.out (DimensionScale.numeratorStage (side j)) (sign j))
  | .zero => .images (.source (.shared .zero))
  | .scratch => .images (.source (.shared .scratch))
  | .fuel => .temp | .out => .threshold j
def scaleBinding (j : Fin 4) : FinitePortBinding DimensionScale.Port Port where
  ports := ⟨scalePort j,by fin_cases j <;> decide +kernel⟩
  decode := fun p => match p with
    | .images (.source (.shared .dimension)) => some .dimension
    | .images (.out k b) => if k=DimensionScale.numeratorStage (side j) ∧ b=sign j then some .factor else none
    | .images (.source (.shared .zero)) => some .zero
    | .images (.source (.shared .scratch)) => some .scratch
    | .temp => some .fuel | .threshold k => if k=j then some .out else none | _ => none
  decode_spec := by fin_cases j <;> decide +kernel

def pairBinding (a b : Port) (hab : a≠b) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![a,b],by intro j k h; fin_cases j <;> fin_cases k <;> simp_all⟩
  decode := fun p => if p=a then some 0 else if p=b then some 1 else none
  decode_spec := by
    intro p j
    change (if p=a then some 0 else if p=b then some 1 else none)=some j ↔ ![a,b] j=p
    fin_cases j <;> by_cases ha : p=a <;> by_cases hb : p=b <;> simp_all [eq_comm]

def copyBinding (j : Fin 4) := pairBinding (crossingSource j) (.crossing j) (by fin_cases j <;> decide)
def prepareBinding : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => .temp,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=.temp then some 0 else none
  decode_spec := by
    intro p q
    change (if p=.temp then some (0 : Fin 1) else none)=some q ↔ Port.temp=p
    fin_cases q
    simp [eq_comm]

inductive Label (F : RationalMobius)
  | images (pc : SourceImages.Label F)
  | scale (saved : Bool) (j : Fin 4) (pc : DimensionScale.Label)
  | copy (saved : Bool) (j : Fin 4) (pc : NativeMappedCopy.Label)
  | prepare (saved : Bool) (pc : NativeBuffer.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F :=
  .images (.source (.lower (.inl (.grid (.init (.erase 0))))))
def afterScale (F : RationalMobius) (saved : Bool) (j : Fin 4) : Label F :=
  if h : j.val<3 then .scale saved ⟨j.val+1,by omega⟩ DimensionScale.start
    else .copy saved 0 (.init (.erase 0))
def afterCopy (F : RationalMobius) (saved : Bool) (j : Fin 4) : Label F :=
  if h : j.val<3 then .copy saved ⟨j.val+1,by omega⟩ (.init (.erase 0))
    else .prepare saved (.erase 0)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .images (.done saved) => .jump (.scale saved 0 DimensionScale.start)
  | .images pc => imagesBinding.instruction Label.images (SourceImages.program F pc)
  | .scale saved j .done => .jump (afterScale F saved j)
  | .scale saved j pc => (scaleBinding j).instruction (Label.scale saved j) (DimensionScale.program pc)
  | .copy saved j (.seal .done) => .jump (afterCopy F saved j)
  | .copy saved j pc => (copyBinding j).instruction (Label.copy saved j) (NativeMappedCopy.program id pc)
  | .prepare saved .done => .jump (.done saved)
  | .prepare saved pc => prepareBinding.instruction (Label.prepare saved) (NativeBuffer.program pc)
  | .done _ => .halt

theorem images_code (F : RationalMobius) (pc : SourceImages.Label F)
    (hh : SourceImages.program F pc≠.halt) (_ : SourceImages.program F pc≠.reject) :
    program F (.images pc)=MicrocodeEmbedding.instruction imagesBinding.ports Label.images (SourceImages.program F pc) := by
  cases pc <;> try exact imagesBinding.instruction_eq _ _
  exact False.elim (hh rfl)
theorem scale_code (F : RationalMobius) (saved : Bool) (j : Fin 4) (pc : DimensionScale.Label)
    (hh : DimensionScale.program pc≠.halt) (_ : DimensionScale.program pc≠.reject) :
    program F (.scale saved j pc)=MicrocodeEmbedding.instruction (scaleBinding j).ports (Label.scale saved j) (DimensionScale.program pc) := by
  cases pc <;> try exact (scaleBinding j).instruction_eq _ _
  exact False.elim (hh rfl)
theorem copy_code (F : RationalMobius) (saved : Bool) (j : Fin 4) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program F (.copy saved j pc)=MicrocodeEmbedding.instruction (copyBinding j).ports (Label.copy saved j) (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]
theorem prepare_code (F : RationalMobius) (saved : Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program F (.prepare saved pc)=MicrocodeEmbedding.instruction prepareBinding.ports (Label.prepare saved) (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s.tapes p).denote⟩,pos⟩
def zipperCfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label F) :=
  ⟨⟨pc,s.tapes⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote,pos⟩

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T := Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

end TransposeFollowup.RowPreparation


/-! Native calls with explicit frame preservation and physical head positions. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_images (F : RationalMobius) (pc : SourceImages.Label F)
    (b : SourceImages.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed imagesBinding.ports (Label.images (F := F))
      (SourceImages.cfg pc b (fun p => pos (imagesBinding.ports p))) (frame s pos)=
      cfg (.images pc) {s with images := b} pos := by
  unfold MicrocodeEmbedding.embed SourceImages.cfg cfg frame
  simp only [← imagesBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_scale (F : RationalMobius) (saved : Bool) (j : Fin 4) (pc : DimensionScale.Label)
    (b : DimensionScale.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (scaleBinding j).ports (Label.scale (F := F) saved j)
      (DimensionScale.cfg pc b (fun p => pos ((scaleBinding j).ports p))) (frame s pos)=
      cfg (.scale saved j pc) (placeScale j b s) pos := by
  unfold MicrocodeEmbedding.embed DimensionScale.cfg cfg frame
  simp only [← (scaleBinding j).values_eq_extend]
  fin_cases j <;> congr 2 <;> funext p
  all_goals cases p with
  | images p => cases p with
    | source p => cases p with
      | shared p => cases p <;> rfl
      | other k => rfl
    | work k => rfl
    | out k b => fin_cases k <;> cases b <;> rfl
  | threshold k => fin_cases k <;> rfl
  | crossing k => rfl
  | temp => rfl

theorem embed_copy (F : RationalMobius) (p q : Port) (hpq : p≠q)
    (labels : NativeMappedCopy.Label → Label F) (pc : NativeMappedCopy.Label)
    (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (pairBinding p q hpq).ports labels
      (NativeMappedCopy.cfg pc a b (fun t => pos ((pairBinding p q hpq).ports t))) (frame s pos)=
      cfg (labels pc) ((s.set p a).set q b) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← (pairBinding p q hpq).values_eq_extend]
  congr 2 <;> funext t
  all_goals
    by_cases ht : t=p
    · subst t
      simp [pairBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,hpq] <;> rfl
    · by_cases hq : t=q
      · subst t
        simp [pairBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,Ne.symm hpq] <;> rfl
      · simp [pairBinding,FinitePortBinding.values,Function.update,ht,hq]

theorem embed_prepare (F : RationalMobius) (saved : Bool) (pc : NativeBuffer.Label)
    (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed prepareBinding.ports (Label.prepare (F := F) saved)
      (NativeBuffer.cfg pc w (fun p => pos (prepareBinding.ports p))).denote (frame s pos)=
      cfg (.prepare saved pc) {s with temp := w} pos := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← prepareBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

abbrev Trace (F : RationalMobius) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem images_call (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t≤SourceImages.budget F n.length, Trace F t
      (cfg (start F) {s with images := SourceImages.initial n iw} pos)
      (cfg (.images (.done (SourceImages.sourceAnswer F n iw))) {s with images := SourceImages.final F n iw} pos) := by
  obtain ⟨t,ht,htr⟩ := SourceImages.complete_trace F n iw hm hi (fun p => pos (imagesBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed imagesBinding.ports (Label.images (F := F))
    (SourceImages.program F) (program F) (frame s pos) (images_code F) htr
  exact ⟨t,ht,by simpa only [embed_images,start] using he⟩

theorem scale_call (F : RationalMobius) (saved : Bool) (j : Fin 4)
    (n x : List Bool) (s : Bank) (pos : Port → ℤ) :
    ∃ t≤DimensionScale.budget n x, Trace F t
      (cfg (.scale saved j DimensionScale.start) (placeScale j (DimensionScale.initial n x) s) pos)
      (cfg (.scale saved j .done) (placeScale j (DimensionScale.final n x) s) pos) := by
  obtain ⟨t,ht,htr⟩ := DimensionScale.complete_trace n x (fun p => pos ((scaleBinding j).ports p))
  have he := MicrocodeEmbedding.trace_embed (scaleBinding j).ports (Label.scale saved j)
    DimensionScale.program (program F) (frame s pos) (scale_code F saved j) htr
  exact ⟨t,ht,by simpa only [embed_scale] using he⟩

theorem copy_call (F : RationalMobius) (saved : Bool) (j : Fin 4)
    (xs : List Bool) (s : Bank) (hs : s.tapes (crossingSource j)=Counter.marked xs)
    (hq : s.tapes (.crossing j)=⟨[],[]⟩) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+14, Trace F t
      (cfg (.copy saved j (.init (.erase 0))) s pos)
      (cfg (.copy saved j (.seal .done)) (s.set (.crossing j) (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun p => pos ((copyBinding j).ports p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding j).ports (Label.copy saved j)
    (NativeMappedCopy.program id) (program F) (frame s pos) (copy_code F saved j) htr
  exact ⟨t,ht,by simpa only [copyBinding,embed_copy,List.map_id,← hs,Bank.set_self,← hq] using he⟩

theorem prepare_call (F : RationalMobius) (saved : Bool) (s : Bank)
    (hs : s.temp=⟨[],[]⟩) (pos : Port → ℤ) :
    ∃ t≤2, Trace F t (cfg (.prepare saved (.erase 0)) s pos)
      (cfg (.prepare saved .done) {s with temp := BinaryCarry.preparedOutput} pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun p => pos (prepareBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed prepareBinding.ports (Label.prepare saved)
    NativeBuffer.program (program F) (frame s pos) (prepare_code F saved) htr
  exact ⟨t,ht,by simpa only [embed_prepare,← hs] using he⟩

end TransposeFollowup.RowPreparation


/-! Stage boundaries include each transfer. Four scalings have the same
bound because all factors have the common width, regardless of their values. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def scaleBudget (n : List Bool) : ℕ := Counter.value n*(18*n.length+39)+20*n.length+44

theorem factor_budget (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    DimensionScale.budget n (scaleFactor F n iw j)=scaleBudget n := by
  rw [DimensionScale.budget_expansion,factor_length F n iw hm hi j]
  unfold scaleBudget
  ring

theorem images_stage (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ) :
    ∃ t≤SourceImages.budget F n.length+1, Trace F t (cfg (start F) (initial n iw) pos)
      (cfg (.scale (SourceImages.sourceAnswer F n iw) 0 DimensionScale.start) (scaling F n iw 0) pos) := by
  obtain ⟨t,ht,htr⟩ := images_call F n iw hm hi (initial n iw) pos
  have h0 : {initial n iw with images := SourceImages.final F n iw}=scaling F n iw 0 := by
    simp [initial,scaling]
  rw [h0] at htr
  have hj := jump_trace F (.images (.done (SourceImages.sourceAnswer F n iw)))
    (.scale (SourceImages.sourceAnswer F n iw) 0 DimensionScale.start) (scaling F n iw 0) pos rfl
  exact ⟨t+1,by omega,trace_trans htr hj⟩

theorem scale_stage (F : RationalMobius) (saved : Bool) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) (pos : Port → ℤ) :
    ∃ t ≤ scaleBudget n+1, Trace F t
      (cfg (.scale saved j DimensionScale.start) (scaling F n iw j.val) pos)
      (cfg (afterScale F saved j) (scaling F n iw (j.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := scale_call F saved j n (scaleFactor F n iw j) (scaling F n iw j.val) pos
  rw [factor_budget F n iw hm hi j] at ht
  rw [scale_initial F n iw hm hi j,scale_final F n iw hm hi j] at htr
  have hj := jump_trace F (.scale saved j .done) (afterScale F saved j) (scaling F n iw (j.val+1)) pos rfl
  exact ⟨t+1,by omega,trace_trans htr hj⟩

theorem copy_stage (F : RationalMobius) (saved : Bool) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) (pos : Port → ℤ) :
    ∃ t≤6*n.length+15, Trace F t
      (cfg (.copy saved j (.init (.erase 0))) (copying F n iw j.val) pos)
      (cfg (afterCopy F saved j) (copying F n iw (j.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := copy_call F saved j (crossingWord F n iw j) (copying F n iw j.val)
    (crossing_source F n iw j) (by simp [copying,Bank.tapes]) pos
  rw [crossing_length F n iw hm hi j] at ht
  rw [copying_step] at htr
  have hj := jump_trace F (.copy saved j (.seal .done)) (afterCopy F saved j) (copying F n iw (j.val+1)) pos rfl
  exact ⟨t+1,by omega,trace_trans htr hj⟩

theorem prepare_stage (F : RationalMobius) (saved : Bool) (n iw : List Bool) (pos : Port → ℤ) :
    ∃ t≤3, Trace F t (cfg (.prepare saved (.erase 0)) (copying F n iw 4) pos)
      (cfg (.done saved) (final F n iw) pos) := by
  obtain ⟨t,ht,htr⟩ := prepare_call F saved (copying F n iw 4) rfl pos
  have hj := jump_trace F (.prepare saved .done) (.done saved) (final F n iw) pos rfl
  exact ⟨t+1,by omega,trace_trans htr hj⟩

end TransposeFollowup.RowPreparation


/-! Source preparation, four scalings, four crossing copies and second
scratch initialization are one native run, with all ten transfers paid. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def budget (F : RationalMobius) (n : List Bool) : ℕ :=
  SourceImages.budget F n.length+4*scaleBudget n+24*n.length+68

theorem complete_trace (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ) :
    ∃ t≤budget F n, Trace F t (cfg (start F) (initial n iw) pos)
      (cfg (.done (SourceImages.sourceAnswer F n iw)) (final F n iw) pos) := by
  let saved := SourceImages.sourceAnswer F n iw
  obtain ⟨a,ha,ta⟩ := images_stage F n iw hm hi pos
  obtain ⟨b,hb,tb⟩ := scale_stage F saved n iw hm hi 0 pos
  obtain ⟨c,hc,tc⟩ := scale_stage F saved n iw hm hi 1 pos
  obtain ⟨d,hd,td⟩ := scale_stage F saved n iw hm hi 2 pos
  obtain ⟨e,he,te⟩ := scale_stage F saved n iw hm hi 3 pos
  obtain ⟨f,hf,tf⟩ := copy_stage F saved n iw hm hi 0 pos
  obtain ⟨g,hg,tg⟩ := copy_stage F saved n iw hm hi 1 pos
  obtain ⟨h,hh,th⟩ := copy_stage F saved n iw hm hi 2 pos
  obtain ⟨i,hi',ti⟩ := copy_stage F saved n iw hm hi 3 pos
  obtain ⟨j,hj,tj⟩ := prepare_stage F saved n iw pos
  simp only [Fin.val_zero,copying_zero] at tf
  refine ⟨a+(b+(c+(d+(e+(f+(g+(h+(i+j)))))))),?_,?_⟩
  · unfold budget
    omega
  · exact trace_trans ta (trace_trans tb (trace_trans tc (trace_trans td (trace_trans te
      (trace_trans tf (trace_trans tg (trace_trans th (trace_trans ti tj))))))))

theorem native_complete (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget F n,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (initial n iw) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg (.done (SourceImages.sourceAnswer F n iw)) (final F n iw) pos).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg (.done (SourceImages.sourceAnswer F n iw)) (final F n iw) pos).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hi pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (n iw : List Bool) (hm : 0<n.length) (hi : iw.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget F n,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (initial n iw) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (SourceImages.sourceAnswer F n iw)) (final F n iw) pos) outerFrame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hi pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RowPreparation


/-! Fixed resources and a paid global budget for all row preparations. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
set_option autoImplicit false

def labelEquiv (F : RationalMobius) : Label F ≃ SourceImages.Label F ⊕
    (Bool × Fin 4 × DimensionScale.Label) ⊕ (Bool × Fin 4 × NativeMappedCopy.Label) ⊕
    (Bool × NativeBuffer.Label) ⊕ Bool where
  toFun
    | .images pc => .inl pc
    | .scale saved j pc => .inr (.inl (saved,j,pc))
    | .copy saved j pc => .inr (.inr (.inl (saved,j,pc)))
    | .prepare saved pc => .inr (.inr (.inr (.inl (saved,pc))))
    | .done saved => .inr (.inr (.inr (.inr saved)))
  invFun
    | .inl pc => .images pc
    | .inr (.inl (saved,j,pc)) => .scale saved j pc
    | .inr (.inr (.inl (saved,j,pc))) => .copy saved j pc
    | .inr (.inr (.inr (.inl (saved,pc)))) => .prepare saved pc
    | .inr (.inr (.inr (.inr saved))) => .done saved
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,j,pc⟩ | ⟨saved,j,pc⟩ | ⟨saved,pc⟩ | saved) <;> rfl

theorem label_card (F : RationalMobius) : Fintype.card (Label F)=
    198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
    396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+8619 := by
  have h := Fintype.card_congr (labelEquiv F)
  have hs : Fintype.card DimensionScale.Label=156 := by decide +kernel
  have hc : Fintype.card NativeMappedCopy.Label=24 := by decide +kernel
  have hp : Fintype.card NativeBuffer.Label=10 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    hs,hc,hp,SourceImages.label_card] at h
  exact h.trans (by ring)

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=37 ∧
    (nativeMachine F).g+1=5 ∧ (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+8619 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=37
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [label_card]
    omega

theorem budget_expansion (F : RationalMobius) (n : List Bool) :
    budget F n=4*Counter.value n*(18*n.length+39)+540*n.length+1349+
      2*(SourceImages.sourceSum F+SourceImages.coefficientSum F)*(18*n.length+52) := by
  unfold budget scaleBudget
  rw [SourceImages.budget_expansion]
  ring

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1≤N) (hv : Counter.value source=N) (hl : source.length≤(N+1).size) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    N*budget F (PaddedWord.word (PaddedWord.commonConstant F) id source) ≤
      ((1224+72*T)*(F.integerOperandConstant^2).size+15250+928*T)*Transpose.inputLength N := by
  dsimp only
  let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
  let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
  have he : budget F (PaddedWord.word (PaddedWord.commonConstant F) id source)=
      N*(72*m+156)+((540+36*T)*m+1349+104*T) := by
    rw [budget_expansion,PaddedWord.common_value,hv]
    dsimp [m,T]
    ring
  have htail : (540+36*T)*m+1349+104*T≤N*((540+36*T)*m+1349+104*T) :=
    Nat.le_mul_of_pos_left _ hN
  have hb : budget F (PaddedWord.word (PaddedWord.commonConstant F) id source)≤
      N*((612+36*T)*m+1505+104*T) := by
    rw [he]
    calc
      _ ≤ N*(72*m+156)+N*((540+36*T)*m+1349+104*T) := Nat.add_le_add_left htail _
      _ = _ := by ring
  have hd := dense_scan_budget ((612+36*T)*PaddedWord.commonConstant F+1505+104*T)
    (1224+72*T) N hN
  have hc : 2*((612+36*T)*PaddedWord.commonConstant F+1505+104*T+3*(1224+72*T))=
      (1224+72*T)*(F.integerOperandConstant^2).size+15250+928*T := by
    unfold PaddedWord.commonConstant
    ring
  calc
    _ ≤ N*(N*((612+36*T)*m+1505+104*T)) := Nat.mul_le_mul_left _ hb
    _ ≤ N*(N*(((612+36*T)*PaddedWord.commonConstant F+1505+104*T)+(1224+72*T)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      have he' : (612+36*T)*m+1505+104*T=
          ((612+36*T)*PaddedWord.commonConstant F+1505+104*T)+(1224+72*T)*source.length := by
        dsimp [m]
        rw [PaddedWord.word_length]
        ring
      rw [he']
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by simpa only [hc] using hd

end TransposeFollowup.RowPreparation


/-! The complete native preparation returns exactly the bank required by
the existing row controller, together with the exact source-open flag. -/

namespace TransposeFollowup.RowPreparation
open FixedTapeCompiler
set_option autoImplicit false

def cellPort : RowCell.Port → Port
  | .word (.threshold,a,b) => .threshold (index a b)
  | .word (.crossing,a,b) => .crossing (index a b)
  | .word (.delta,a,b) => .images (.out (denominatorStage a) b)
  | .fuel => .images (.source (.shared .fuel))
  | .zero => .images (.source (.shared .zero))
  | .scratch false => .images (.source (.shared .scratch))
  | .scratch true => .temp

def cellBinding : FinitePortBinding RowCell.Port Port where
  ports := ⟨cellPort,by decide +kernel⟩
  decode := fun p => match p with
    | .threshold j => some (.word (.threshold,side j,sign j))
    | .crossing j => some (.word (.crossing,side j,sign j))
    | .images (.out j b) => if j=1 then some (.word (.delta,false,b)) else
        if j=3 then some (.word (.delta,true,b)) else none
    | .images (.source (.shared .fuel)) => some .fuel
    | .images (.source (.shared .zero)) => some .zero
    | .images (.source (.shared .scratch)) => some (.scratch false)
    | .temp => some (.scratch true) | _ => none
  decode_spec := by decide +kernel

def projectRow (s : Bank) : RowCell.Bank := fun p => s.tapes (cellPort p)

theorem final_images (F : RationalMobius) (n iw : List Bool) :
    (final F n iw).images=SourceImages.final F n iw := rfl
theorem final_threshold (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    (final F n iw).threshold j=Counter.marked (thresholdWord F n iw j) := by
  simp [final,copying,scaling]
theorem final_crossing (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    (final F n iw).crossing j=Counter.marked (crossingWord F n iw j) := by
  simp [final,copying]

theorem final_ready (F : RationalMobius) (source iw : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    projectRow (final F n iw)=RowCell.ready n.length (words F source iw) := by
  dsimp only
  have hs := SourceImages.source_seed F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw
  funext p
  cases p with
  | word p =>
    rcases p with ⟨g,a,b⟩
    cases g <;> cases a <;> cases b <;>
      simp [projectRow,cellPort,Bank.tapes,RowCell.ready,final_images,final_threshold,final_crossing,
        words,thresholdWord,scaleFactor,crossingWord,DimensionScale.factor,deltaWord,index,side,sign,
        SourceImages.stage,SourceImages.Bank.tapes,SourceImages.final_output,denominatorStage] <;> rfl
  | fuel => exact hs.2.1
  | zero => exact hs.1
  | scratch b =>
    cases b
    · exact hs.2.2
    · rfl

theorem rational_complete_trace (F : RationalMobius) (source : List Bool)
    (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t≤budget F n,
      Trace F t (cfg (start F) (initial n iw) pos)
        (cfg (.done ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight)) (final F n iw) pos) ∧
      projectRow (final F n iw)=RowCell.ready n.length (words F source iw) ∧
      RowCell.Represents n.length (words F source iw) (F.componentRow i) 0 := by
  dsimp only
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := by
    dsimp [n]
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hl pos
  have ha : SourceImages.sourceAnswer F n iw=(F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight :=
    SourceEndpoints.answer_rational F source i iw hl hv
  rw [ha] at htr
  exact ⟨t,ht,htr,final_ready F source iw,words_represents F source i iw hl hv⟩

end TransposeFollowup.RowPreparation


/-! A fixed native caller from prepared dimension/index/seed resources to
one closed overlap row. All preparation, counter/stream setup, row writes,
counter erasure and five return transfers are part of its program. -/

namespace TransposeFollowup.RowExecution
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | prep (p : RowPreparation.Port) | counter | stream
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def prepBinding : FinitePortBinding RowPreparation.Port Port where
  ports := ⟨Port.prep,by intro p q h; exact Port.prep.inj h⟩
  decode := fun p => match p with | .prep q => some q | _ => none
  decode_spec := by
    intro p q
    change (match p with | .prep r => some r | _ => none)=some q ↔ Port.prep q=p
    cases p <;> simp [eq_comm]

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun q => if q=p then some 0 else none
  decode_spec := by
    intro q j
    change (if q=p then some (0 : Fin 1) else none)=some j ↔ p=q
    fin_cases j
    simp [eq_comm]

def dimension : Port := .prep (.images (.source (.shared .dimension)))
def copyBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![dimension,.counter],by intro j k h; fin_cases j <;> fin_cases k <;> simp_all [dimension]⟩
  decode := fun p => if p=dimension then some 0 else if p=.counter then some 1 else none
  decode_spec := by
    intro p j
    fin_cases j <;> by_cases h : p=dimension <;> by_cases h' : p=.counter <;> simp_all [dimension,eq_comm]

def rowPort : RowStream.Port → Port
  | .cell p => .prep (RowPreparation.cellBinding.ports p)
  | .counter => .counter | .stream => .stream

def rowBinding : FinitePortBinding RowStream.Port Port where
  ports := ⟨rowPort,by
    intro p q h
    cases p <;> cases q <;> simp_all [rowPort]
    ⟩
  decode := fun p => match p with
    | .prep q => (RowPreparation.cellBinding.decode q).map RowStream.Port.cell
    | .counter => some .counter | .stream => some .stream
  decode_spec := by
    intro p q
    change (match p with
      | .prep r => (RowPreparation.cellBinding.decode r).map RowStream.Port.cell
      | .counter => some .counter | .stream => some .stream)=some q ↔ rowPort q=p
    cases p with
    | prep p =>
      cases q <;> simp [rowPort,RowPreparation.cellBinding.decode_spec,eq_comm]
    | counter => cases q <;> simp [rowPort]
    | stream => cases q <;> simp [rowPort]

inductive Label (F : RationalMobius)
  | prep (pc : RowPreparation.Label F)
  | copy (saved : Bool) (pc : NativeMappedCopy.Label)
  | init (saved : Bool) (pc : NativeBuffer.Label)
  | row (pc : RowStream.Label)
  | erase (saved : Bool) (pc : NativeErase.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F := .prep (RowPreparation.start F)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .prep (.done saved) => .jump (.copy saved (.init (.erase 0)))
  | .prep pc => prepBinding.instruction Label.prep (RowPreparation.program F pc)
  | .copy saved (.seal .done) => .jump (.init saved (.erase 0))
  | .copy saved pc => copyBinding.instruction (Label.copy saved) (NativeMappedCopy.program id pc)
  | .init saved .done => .jump (.row (.counter saved 0))
  | .init saved pc => (singleBinding .stream).instruction (Label.init saved) (NativeBuffer.program pc)
  | .row (.done saved) => .jump (.erase saved 2)
  | .row pc => rowBinding.instruction Label.row (RowStream.program pc)
  | .erase saved pc => if pc=0 then .jump (.done saved) else
      (singleBinding .counter).instruction (Label.erase saved) (NativeErase.program pc)
  | .done _ => .halt

theorem prep_code (F : RationalMobius) (pc : RowPreparation.Label F)
    (hh : RowPreparation.program F pc≠.halt) (_ : RowPreparation.program F pc≠.reject) :
    program F (.prep pc)=MicrocodeEmbedding.instruction prepBinding.ports Label.prep (RowPreparation.program F pc) := by
  cases pc <;> try exact prepBinding.instruction_eq _ _
  exact False.elim (hh rfl)
theorem copy_code (F : RationalMobius) (saved : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program F (.copy saved pc)=MicrocodeEmbedding.instruction copyBinding.ports (Label.copy saved) (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]
theorem init_code (F : RationalMobius) (saved : Bool) (pc : NativeBuffer.Label)
    (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program F (.init saved pc)=MicrocodeEmbedding.instruction (singleBinding .stream).ports (Label.init saved) (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]
theorem row_code (F : RationalMobius) (pc : RowStream.Label)
    (hh : RowStream.program pc≠.halt) (_ : RowStream.program pc≠.reject) :
    program F (.row pc)=MicrocodeEmbedding.instruction rowBinding.ports Label.row (RowStream.program pc) := by
  cases pc <;> simp_all [program,RowStream.program,FinitePortBinding.instruction_eq]
theorem erase_code (F : RationalMobius) (saved : Bool) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program F (.erase saved pc)=MicrocodeEmbedding.instruction (singleBinding .counter).ports (Label.erase saved) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def zipperCfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label F) :=
  ⟨⟨pc,s⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩
def prepBank (b : RowPreparation.Bank) : Bank
  | .prep p => b.tapes p | _ => ⟨[],[]⟩
def initial (n iw : List Bool) := prepBank (RowPreparation.initial n iw)
def prepared (F : RationalMobius) (n iw : List Bool) := prepBank (RowPreparation.final F n iw)
def fueled (F : RationalMobius) (n iw : List Bool) :=
  Function.update (prepared F n iw) .counter (Counter.marked n)
def ready (F : RationalMobius) (n iw : List Bool) :=
  Function.update (fueled F n iw) .stream BinaryCarry.preparedOutput

def rowBank {m : ℕ} (closed : Bool) (fuel : List Bool) (s : RowStream.State m) (base : Bank) : Bank :=
  rowBinding.values (RowStream.bank closed fuel s) base

def positions (pos : Port → ℤ) (written : List Bool) : Port → ℤ :=
  Function.update pos .stream (pos .stream+written.length)

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T := Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

end TransposeFollowup.RowExecution


/-! Framed native calls for the prepared-input row caller. The stream head
is allowed to advance; every other head retains its original position. -/
namespace TransposeFollowup.RowExecution
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

abbrev Trace (F : RationalMobius) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem embed_prep (F : RationalMobius) (pc : RowPreparation.Label F)
    (b s : RowPreparation.Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed prepBinding.ports (Label.prep (F := F))
      (RowPreparation.cfg pc b (fun p => pos (.prep p))) (frame (prepBank s) pos)=
      cfg (.prep pc) (prepBank b) pos := by
  unfold MicrocodeEmbedding.embed RowPreparation.cfg cfg frame
  simp only [← prepBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_copy (F : RationalMobius) (saved : Bool) (pc : NativeMappedCopy.Label)
    (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports (Label.copy (F := F) saved)
      (NativeMappedCopy.cfg pc a b (fun p => pos (copyBinding.ports p))) (frame s pos)=
      cfg (.copy saved pc) (Function.update (Function.update s dimension a) .counter b) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p
  all_goals
    by_cases h : p=dimension
    · subst p
      simp [copyBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,dimension]
    · by_cases h' : p=.counter
      · subst p
        simp [copyBinding,FinitePortBinding.values,NativeMappedCopy.bank,Function.update,dimension]
      · simp [copyBinding,FinitePortBinding.values,Function.update,h,h']

theorem embed_one {L : Type} (F : RationalMobius) (p : Port) (labels : L → Label F)
    (pc : L) (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding p).ports labels
      ⟨⟨pc,fun _ => w.denote⟩,fun _ => pos p⟩ (frame s pos)=
      cfg (labels pc) (Function.update s p w) pos := by
  unfold MicrocodeEmbedding.embed cfg frame
  simp only [← (singleBinding p).values_eq_extend]
  congr 2 <;> funext q <;> by_cases h : q=p <;>
    simp [singleBinding,FinitePortBinding.values,h,Function.update]

theorem embed_row (F : RationalMobius) {m : ℕ} (closed : Bool) (pc : RowStream.Label)
    (fuel : List Bool) (s : RowStream.State m) (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed rowBinding.ports (Label.row (F := F))
      (RowStream.config closed pc fuel s (fun p => pos (rowPort p))) (frame base pos)=
      cfg (.row pc) (rowBank closed fuel s base) (positions pos s.written) := by
  unfold MicrocodeEmbedding.embed RowStream.config cfg frame
  simp only [← rowBinding.values_eq_extend]
  congr 2
  · funext p
    cases h : rowBinding.decode p <;> simp [FinitePortBinding.values,rowBank,h]
  · funext p
    cases h : rowBinding.decode p with
    | none =>
      have hp : p≠.stream := by intro hp; subst p; simp [rowBinding] at h
      simp [FinitePortBinding.values,h,positions,hp]
    | some q =>
      have hp := (rowBinding.decode_spec p q).mp h
      change rowPort q=p at hp
      rw [← hp]
      have h' : rowBinding.decode (rowPort q)=some q := by simpa only [hp] using h
      simp only [FinitePortBinding.values,h']
      cases q <;> simp [RowStream.positions,positions,rowPort]

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem prep_call (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ) :
    ∃ t≤RowPreparation.budget F n, Trace F t
      (cfg (start F) (initial n iw) pos)
      (cfg (.prep (.done (SourceImages.sourceAnswer F n iw))) (prepared F n iw) pos) := by
  obtain ⟨t,ht,htr⟩ := RowPreparation.complete_trace F n iw hm hi (fun p => pos (.prep p))
  have he := MicrocodeEmbedding.trace_embed prepBinding.ports (Label.prep (F := F))
    (RowPreparation.program F) (program F) (frame (initial n iw) pos) (prep_code F) htr
  exact ⟨t,ht,by simpa only [initial,embed_prep,start,prepared] using he⟩

theorem copy_call (F : RationalMobius) (saved : Bool) (xs : List Bool) (s : Bank)
    (hs : s dimension=Counter.marked xs) (hq : s .counter=⟨[],[]⟩) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+14, Trace F t
      (cfg (.copy saved (.init (.erase 0))) s pos)
      (cfg (.copy saved (.seal .done)) (Function.update s .counter (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports (Label.copy saved)
    (NativeMappedCopy.program id) (program F) (frame s pos) (copy_code F saved) htr
  exact ⟨t,ht,by simpa only [embed_copy,List.map_id,← hs,Function.update_eq_self,← hq] using he⟩

theorem init_call (F : RationalMobius) (saved : Bool) (s : Bank)
    (hs : s .stream=⟨[],[]⟩) (pos : Port → ℤ) :
    ∃ t≤2, Trace F t (cfg (.init saved (.erase 0)) s pos)
      (cfg (.init saved .done) (Function.update s .stream BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos .stream)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .stream).ports (Label.init saved)
    NativeBuffer.program (program F) (frame s pos) (init_code F saved) htr
  have heq (pc : NativeBuffer.Label) (w : Tape Bool) :
      (NativeBuffer.cfg pc w (fun _ => pos .stream)).denote=
        (⟨⟨pc,fun _ => w.denote⟩,fun _ => pos .stream⟩ : NativeMicrocode.Config (Fin 1) NativeBuffer.Label) := by
    unfold NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus
    congr 2
    funext j
    fin_cases j
    rfl
  simp only [heq,embed_one,← hs,Function.update_eq_self] at he
  exact ⟨t,ht,he⟩

theorem row_call (F : RationalMobius) {m : ℕ} (guard : Bool) (fuel : List Bool)
    (s : RowStream.State m) (base : Bank) (pos : Port → ℤ) :
    ∃ t≤RowStream.budget m fuel, Trace F t
      (cfg (.row (.counter guard 0)) (rowBank false fuel s base) (positions pos s.written))
      (cfg (.row (.done guard)) (rowBank true (List.replicate fuel.length true)
        (RowStream.process guard (Counter.value fuel) s) base)
        (positions pos (RowStream.process guard (Counter.value fuel) s).written)) := by
  obtain ⟨t,ht,htr⟩ := RowStream.row_trace guard fuel s (fun p => pos (rowPort p))
  have he := MicrocodeEmbedding.trace_embed rowBinding.ports (Label.row (F := F))
    RowStream.program (program F) (frame base pos) (row_code F) htr
  exact ⟨t,ht,by simpa only [embed_row] using he⟩

theorem erase_call (F : RationalMobius) (saved : Bool) (xs : List Bool)
    (s : Bank) (hs : s .counter=Counter.marked xs) (pos : Port → ℤ) :
    ∃ t≤4*xs.length+4, Trace F t (cfg (.erase saved 2) s pos)
      (cfg (.erase saved 0) (Function.update s .counter ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos .counter)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .counter).ports (Label.erase saved)
    NativeErase.program (program F) (frame s pos) (erase_code F saved) htr
  have heq (pc : NativeErase.Label) (w : Tape Bool) :
      (NativeErase.cfg pc w (fun _ => pos .counter)).denote=
        (⟨⟨pc,fun _ => w.denote⟩,fun _ => pos .counter⟩ : NativeMicrocode.Config (Fin 1) NativeErase.Label) := by
    unfold NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus
    congr 2
    funext j
    fin_cases j
    rfl
  simp only [heq,embed_one,← hs,Function.update_eq_self] at he
  exact ⟨t,ht,he⟩

end TransposeFollowup.RowExecution


/-! Compose all five actual calls. Dimension/index and seed resources are
explicit input tapes; the 33 remaining work/output tapes initially are blank.
The output stream advances by the dimension, while its physical counter is
returned blank. Stored preparation work is retained, not silently discarded. -/
namespace TransposeFollowup.RowExecution
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem rowBank_at {m : ℕ} (closed : Bool) (fuel : List Bool) (s : RowStream.State m)
    (base : Bank) (p : RowStream.Port) :
    rowBank closed fuel s base (rowPort p)=RowStream.bank closed fuel s p := by
  have h : rowBinding.decode (rowPort p)=some p :=
    (rowBinding.decode_spec _ p).mpr rfl
  simp [rowBank,FinitePortBinding.values,h]

theorem rowBank_outside {m : ℕ} (closed : Bool) (fuel : List Bool) (s : RowStream.State m)
    (base : Bank) (p : Port) (hp : rowBinding.decode p=none) :
    rowBank closed fuel s base p=base p := by simp [rowBank,FinitePortBinding.values,hp]

theorem rowBank_eq {m : ℕ} (closed : Bool) (fuel : List Bool) (s : RowStream.State m)
    (base : Bank) (h : ∀ p,base (rowPort p)=RowStream.bank closed fuel s p) :
    rowBank closed fuel s base=base := by
  funext p
  cases hp : rowBinding.decode p with
  | none => exact rowBank_outside closed fuel s base p hp
  | some q =>
    have hq : rowPort q=p := (rowBinding.decode_spec _ q).mp hp
    rw [← hq,rowBank_at,h]

def state (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    RowStream.State (PaddedWord.word (PaddedWord.commonConstant F) id source).length :=
  ⟨RowPreparation.words F source iw,RowPreparation.words_width F source iw hl,[]⟩

def result (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  RowStream.process (SourceImages.sourceAnswer F n iw) (Counter.value n) (state F source iw hl)

def completed (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) : Bank :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  Function.update (rowBank true (List.replicate n.length true) (result F source iw hl) (ready F n iw))
    .counter ⟨[],[]⟩

theorem ready_rowBank (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    rowBank false n (state F source iw hl) (ready F n iw)=ready F n iw := by
  apply rowBank_eq
  intro p
  cases p with
  | cell p =>
    change (RowPreparation.final F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw).tapes
      (RowPreparation.cellPort p) = RowCell.ready _ (RowPreparation.words F source iw) p
    exact congrFun (RowPreparation.final_ready F source iw) p
  | counter => rfl
  | stream => rfl

theorem positions_nil (pos : Port → ℤ) : positions pos []=pos := by
  simp [positions]

def budget (F : RationalMobius) (n : List Bool) :=
  RowPreparation.budget F n+RowStream.budget n.length n+10*n.length+25

theorem complete_trace (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t≤budget F n, Trace F t (cfg (start F) (initial n iw) pos)
      (cfg (.done (SourceImages.sourceAnswer F n iw)) (completed F source iw hl)
        (positions pos (result F source iw hl).written)) := by
  dsimp only
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  let saved := SourceImages.sourceAnswer F n iw
  have hm : 0<n.length := by
    dsimp [n]
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨a,ha,ta⟩ := prep_call F n iw hm hl pos
  have ja := jump_trace F (.prep (.done saved)) (.copy saved (.init (.erase 0))) (prepared F n iw) pos rfl
  have hs : prepared F n iw dimension=Counter.marked n :=
    RowPreparation.images_dimension F n iw
  obtain ⟨b,hb,tb⟩ := copy_call F saved n (prepared F n iw) hs rfl pos
  have jb := jump_trace F (.copy saved (.seal .done)) (.init saved (.erase 0)) (fueled F n iw) pos rfl
  obtain ⟨c,hc,tc⟩ := init_call F saved (fueled F n iw) rfl pos
  have jc := jump_trace F (.init saved .done) (.row (.counter saved 0)) (ready F n iw) pos rfl
  obtain ⟨d,hd,td⟩ := row_call F saved n (state F source iw hl) (ready F n iw) pos
  have hr : rowBank false n (state F source iw hl) (ready F n iw)=ready F n iw :=
    ready_rowBank F source iw hl
  rw [hr] at td
  have hnil : (state F source iw hl).written=[] := rfl
  simp only [hnil,positions_nil] at td
  change d≤RowStream.budget n.length n at hd
  let out := rowBank true (List.replicate n.length true) (result F source iw hl) (ready F n iw)
  let endpos := positions pos (result F source iw hl).written
  have jd := jump_trace F (.row (.done saved)) (.erase saved 2) out endpos rfl
  have hcounter : out .counter=Counter.marked (List.replicate n.length true) :=
    rowBank_at true _ _ _ .counter
  obtain ⟨e,he,te⟩ := erase_call F saved (List.replicate n.length true) out hcounter endpos
  have je := jump_trace F (.erase saved 0) (.done saved) (Function.update out .counter ⟨[],[]⟩) endpos rfl
  refine ⟨a+1+b+1+c+1+d+1+e+1,?_,?_⟩
  · change a+1+b+1+c+1+d+1+e+1≤budget F n
    unfold budget
    simp only [List.length_replicate] at he
    omega
  · exact trace_trans (trace_trans (trace_trans (trace_trans (trace_trans
      (trace_trans (trace_trans (trace_trans (trace_trans ta ja) tb) jb) tc) jc) td) jd) te) je

theorem native_complete (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t≤budget F n,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (initial n iw) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg (.done (SourceImages.sourceAnswer F n iw)) (completed F source iw hl)
          (positions pos (result F source iw hl).written)).denote
            (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg (.done (SourceImages.sourceAnswer F n iw)) (completed F source iw hl)
          (positions pos (result F source iw hl).written)).denote
            (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t≤budget F n,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (initial n iw) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (SourceImages.sourceAnswer F n iw)) (completed F source iw hl)
            (positions pos (result F source iw hl).written)) outerFrame).denote
              encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RowExecution


/-! Exact rational output of the complete caller, with physical counter
cleanup, framed preparation storage and the output head displacement. -/
namespace TransposeFollowup.RowExecution
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem result_rational (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) :
    result F source iw hl=RowStream.process (RowStream.rowGuard F i) (Counter.value source)
      (state F source iw hl) := by
  have ha : SourceImages.sourceAnswer F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw=
      RowStream.rowGuard F i := SourceEndpoints.answer_rational F source i iw hl hv
  simp only [result,ha,PaddedWord.common_value]

theorem result_written (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) : (result F source iw hl).written=F.denseRow i := by
  rw [result_rational F source i iw hl hv]
  have h := RowStream.process_row_written_wide F (PaddedWord.common_width_sufficient F source)
    i (state F source iw hl) (RowPreparation.words_represents F source i iw hl hv)
  simpa only [state,List.nil_append] using h

theorem result_represents (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) :
    RowCell.Represents (PaddedWord.word (PaddedWord.commonConstant F) id source).length
      (result F source iw hl).words (F.componentRow i) (Counter.value source) := by
  rw [result_rational F source i iw hl hv]
  simpa only [Nat.zero_add] using RowStream.process_represents_wide F
    (PaddedWord.common_width_sufficient F source) i (Counter.value source) 0 (by omega)
    (state F source iw hl) (RowPreparation.words_represents F source i iw hl hv)

theorem result_length (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    (result F source iw hl).written.length=Counter.value source := by
  simp only [result,RowStream.process_length,state,List.length_nil,Nat.zero_add,PaddedWord.common_value]

theorem final_stream (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    completed F source iw hl .stream=RowStream.closedTape (result F source iw hl).written := by
  unfold completed
  rw [Function.update_of_ne (by decide : Port.stream≠.counter)]
  exact rowBank_at true _ _ _ .stream

theorem final_counter (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    completed F source iw hl .counter=⟨[],[]⟩ := by simp [completed]

theorem final_cell (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (p : RowCell.Port) :
    completed F source iw hl (rowPort (.cell p))=
      RowCell.ready (PaddedWord.word (PaddedWord.commonConstant F) id source).length (result F source iw hl).words p := by
  unfold completed
  rw [Function.update_of_ne (by simp [rowPort])]
  exact rowBank_at true _ _ _ (.cell p)

theorem final_framed (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (p : Port) (hp : rowBinding.decode p=none) :
    completed F source iw hl p=prepared F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw p := by
  have hc : p≠.counter := by intro h; subst p; simp [rowBinding] at hp
  have hs : p≠.stream := by intro h; subst p; simp [rowBinding] at hp
  simp only [completed,Function.update_of_ne hc,rowBank_outside _ _ _ _ _ hp,
    ready,fueled,Function.update_of_ne hs]

theorem process_fixed_word {m : ℕ} (guard : Bool) (k : ℕ) (s : RowStream.State m)
    (g : RowCell.Group) (i : RowCell.Index) (hg : g≠.crossing) :
    (RowStream.process guard k s).words (g,i)=s.words (g,i) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [RowStream.process,ih]
    change RowCell.updateAll s.words (g,i)=s.words (g,i)
    simp [RowCell.updateAll_apply,hg]

theorem final_fixed_word (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (g : RowCell.Group) (i : RowCell.Index) (hg : g≠.crossing) :
    completed F source iw hl (rowPort (.cell (.word (g,i))))=
      Counter.marked (RowPreparation.words F source iw (g,i)) := by
  rw [final_cell]
  change Counter.marked ((result F source iw hl).words (g,i))=_
  rw [result,process_fixed_word _ _ _ _ _ hg]
  rfl

theorem final_positions (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ) :
    positions pos (result F source iw hl).written .stream=pos .stream+Counter.value source ∧
    ∀ p, p≠.stream → positions pos (result F source iw hl).written p=pos p := by
  constructor
  · simp [positions,result_length]
  · intro p hp
    simp [positions,hp]

theorem rational_complete_trace (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t≤budget F n, Trace F t (cfg (start F) (initial n iw) pos)
      (cfg (.done (RowStream.rowGuard F i)) (completed F source iw hl) (positions pos (F.denseRow i))) ∧
      completed F source iw hl .stream=RowStream.closedTape (F.denseRow i) ∧
      RowCell.Represents n.length (result F source iw hl).words (F.componentRow i) (Counter.value source) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  have ha : SourceImages.sourceAnswer F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw=
      RowStream.rowGuard F i := SourceEndpoints.answer_rational F source i iw hl hv
  rw [ha,result_written F source i iw hl hv] at htr
  exact ⟨t,ht,htr,by rw [final_stream,result_written F source i iw hl hv],result_represents F source i iw hl hv⟩

end TransposeFollowup.RowExecution


/-! Fixed machine size and the global allowance for the complete row calls.
The sum bound alone does not implement storage reuse between rows. -/
namespace TransposeFollowup.RowExecution
open FixedTapeCompiler
set_option autoImplicit false

def labelEquiv (F : RationalMobius) : Label F ≃ RowPreparation.Label F ⊕
    (Bool × NativeMappedCopy.Label) ⊕ (Bool × NativeBuffer.Label) ⊕ RowStream.Label ⊕
    (Bool × NativeErase.Label) ⊕ Bool where
  toFun
    | .prep pc => .inl pc
    | .copy saved pc => .inr (.inl (saved,pc))
    | .init saved pc => .inr (.inr (.inl (saved,pc)))
    | .row pc => .inr (.inr (.inr (.inl pc)))
    | .erase saved pc => .inr (.inr (.inr (.inr (.inl (saved,pc)))))
    | .done saved => .inr (.inr (.inr (.inr (.inr saved))))
  invFun
    | .inl pc => .prep pc
    | .inr (.inl (saved,pc)) => .copy saved pc
    | .inr (.inr (.inl (saved,pc))) => .init saved pc
    | .inr (.inr (.inr (.inl pc))) => .row pc
    | .inr (.inr (.inr (.inr (.inl (saved,pc))))) => .erase saved pc
    | .inr (.inr (.inr (.inr (.inr saved)))) => .done saved
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,pc⟩ | ⟨saved,pc⟩ | pc | ⟨saved,pc⟩ | saved) <;> rfl

theorem label_card (F : RationalMobius) : Fintype.card (Label F)=
    198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
    396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+11581 := by
  have h := Fintype.card_congr (labelEquiv F)
  have hc : Fintype.card NativeMappedCopy.Label=24 := by decide +kernel
  have hp : Fintype.card NativeBuffer.Label=10 := by decide +kernel
  have hr : Fintype.card RowStream.Label=2876 := by decide +kernel
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hc,hp,hr,he,RowPreparation.label_card] at h
  exact h.trans (by ring)

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=39 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+11581 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=39
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [label_card]
    omega

theorem budget_expansion (F : RationalMobius) (n : List Bool) :
    budget F n=Counter.value n*(190*n.length+451)+
      (554+36*(SourceImages.sourceSum F+SourceImages.coefficientSum F))*n.length+
      1383+104*(SourceImages.sourceSum F+SourceImages.coefficientSum F) := by
  unfold budget RowStream.budget
  rw [RowPreparation.budget_expansion]
  ring

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1≤N) (hv : Counter.value source=N) (hl : source.length≤(N+1).size) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    N*budget F (PaddedWord.word (PaddedWord.commonConstant F) id source) ≤
      ((1488+72*T)*(F.integerOperandConstant^2).size+18548+928*T)*Transpose.inputLength N := by
  dsimp only
  let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
  let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
  have he : budget F (PaddedWord.word (PaddedWord.commonConstant F) id source)=
      N*(190*m+451)+((554+36*T)*m+1383+104*T) := by
    rw [budget_expansion,PaddedWord.common_value,hv]
    dsimp [m,T]
    ring
  have htail : (554+36*T)*m+1383+104*T≤N*((554+36*T)*m+1383+104*T) :=
    Nat.le_mul_of_pos_left _ hN
  have hb : budget F (PaddedWord.word (PaddedWord.commonConstant F) id source)≤
      N*((744+36*T)*m+1834+104*T) := by
    rw [he]
    calc
      _ ≤ N*(190*m+451)+N*((554+36*T)*m+1383+104*T) := Nat.add_le_add_left htail _
      _ = _ := by ring
  have hd := dense_scan_budget ((744+36*T)*PaddedWord.commonConstant F+1834+104*T)
    (1488+72*T) N hN
  have hc : 2*((744+36*T)*PaddedWord.commonConstant F+1834+104*T+3*(1488+72*T))=
      (1488+72*T)*(F.integerOperandConstant^2).size+18548+928*T := by
    unfold PaddedWord.commonConstant
    ring
  calc
    _ ≤ N*(N*((744+36*T)*m+1834+104*T)) := Nat.mul_le_mul_left _ hb
    _ ≤ N*(N*(((744+36*T)*PaddedWord.commonConstant F+1834+104*T)+(1488+72*T)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      have he' : (744+36*T)*m+1834+104*T=
          ((744+36*T)*PaddedWord.commonConstant F+1834+104*T)+(1488+72*T)*source.length := by
        dsimp [m]
        rw [PaddedWord.word_length]
        ring
      rw [he']
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by simpa only [hc] using hd

end TransposeFollowup.RowExecution


/-! Explicit inventory of the thirty marked words left by a complete row.
The inventory and all word lengths are derived from the actual returned
bank. Six seed/input tapes, the stream and counter are kept separate. -/
namespace TransposeFollowup.RowCleanup
open FixedTapeCompiler CopyMachine
open RowExecution (Port)
set_option autoImplicit false

inductive Work
  | grid | sourceWork (j : Fin 4) | sourceFraction (upper : Bool) (j : Fin 3)
  | imageWork (j : Fin 3) | image (j : Fin 4) (sign : Bool)
  | threshold (j : Fin 4) | crossing (j : Fin 4)
  deriving DecidableEq, Fintype

def workPort : Work → Port
  | .grid => .prep (.images (.source (.shared .grid)))
  | .sourceWork j => .prep (.images (.source (.shared (.work j))))
  | .sourceFraction false j => .prep (.images (.source (.shared (.out j))))
  | .sourceFraction true j => .prep (.images (.source (.other j)))
  | .imageWork j => .prep (.images (.work j))
  | .image j b => .prep (.images (.out j b))
  | .threshold j => .prep (.threshold j)
  | .crossing j => .prep (.crossing j)

def workAt : Fin 30 → Work := ![
  .grid,.sourceWork 0,.sourceWork 1,.sourceWork 2,.sourceWork 3,
  .sourceFraction false 0,.sourceFraction false 1,.sourceFraction false 2,
  .sourceFraction true 0,.sourceFraction true 1,.sourceFraction true 2,
  .imageWork 0,.imageWork 1,.imageWork 2,
  .image 0 false,.image 0 true,.image 1 false,.image 1 true,
  .image 2 false,.image 2 true,.image 3 false,.image 3 true,
  .threshold 0,.threshold 1,.threshold 2,.threshold 3,
  .crossing 0,.crossing 1,.crossing 2,.crossing 3]

def workIndex : Work → Fin 30
  | .grid => 0
  | .sourceWork j => ⟨j.val+1,by omega⟩
  | .sourceFraction false j => ⟨j.val+5,by omega⟩
  | .sourceFraction true j => ⟨j.val+8,by omega⟩
  | .imageWork j => ⟨j.val+11,by omega⟩
  | .image j false => ⟨2*j.val+14,by omega⟩
  | .image j true => ⟨2*j.val+15,by omega⟩
  | .threshold j => ⟨j.val+22,by omega⟩
  | .crossing j => ⟨j.val+26,by omega⟩

theorem workAt_index : ∀ w,workAt (workIndex w)=w := by decide +kernel

def dirtyPorts : Fin 30 ↪ Port := ⟨workPort ∘ workAt,by decide +kernel⟩

def seedPort : Fin 6 → Port := ![
  .prep (.images (.source (.shared .dimension))),.prep (.images (.source (.shared .index))),
  .prep (.images (.source (.shared .unit))),.prep (.images (.source (.shared .zero))),
  .prep (.images (.source (.shared .fuel))),.prep (.images (.source (.shared .scratch)))]

theorem port_partition : ∀ p : Port,
    (∃ j,dirtyPorts j=p) ∨ (∃ j,seedPort j=p) ∨ p=.prep .temp ∨ p=.counter ∨ p=.stream := by
  decide +kernel

theorem dirty_not_seed : ∀ j k,dirtyPorts j≠seedPort k := by decide +kernel
theorem dirty_not_temp : ∀ j,dirtyPorts j≠.prep .temp := by decide +kernel
theorem dirty_not_counter : ∀ j,dirtyPorts j≠.counter := by decide +kernel
theorem dirty_not_stream : ∀ j,dirtyPorts j≠.stream := by decide +kernel

def sourceProduct (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : List Bool :=
  if SourceEndpoints.negative F true then
    EndpointClip.workWord (SourceEndpoints.magnitude F true) (SourceEndpoints.denominator F true) true n iw j
  else EndpointGuard.adjustedWord (SourceEndpoints.magnitude F true) (SourceEndpoints.denominator F true) true n iw j

def word (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) : Work → List Bool :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  fun w => match w with
  | .grid => EndpointClip.gridWord true n iw
  | .sourceWork j => sourceProduct F n iw j
  | .sourceFraction upper j => SourceEndpoints.outputWords (SourceEndpoints.magnitude F)
      (SourceEndpoints.denominator F) (SourceEndpoints.negative F) n iw upper j
  | .imageWork j => SourceImages.product F n iw 3 j
  | .image j b => SourceImages.imageWord F n iw j b
  | .threshold j => (RowExecution.result F source iw hl).words
      (.threshold,RowPreparation.side j,RowPreparation.sign j)
  | .crossing j => (RowExecution.result F source iw hl).words
      (.crossing,RowPreparation.side j,RowPreparation.sign j)

theorem word_length (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (w : Work) :
    (word F source iw hl w).length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := by
    dsimp [n]
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  cases w with
  | grid => exact EndpointClip.gridWord_length true n iw hm hl
  | sourceWork j =>
    change (sourceProduct F n iw j).length=n.length
    unfold sourceProduct
    split
    · exact EndpointClip.workWord_length _ _ _ _ _ _ hm hl
    · exact EndpointGuard.adjustedWord_length _ _ _ _ _ hm hl _
  | sourceFraction upper j => exact SourceEndpoints.outputWords_length _ _ _ _ _ hm hl _ _
  | imageWork j => exact SourceImages.product_length F n iw hm hl _ _
  | image j b => exact SourceImages.imageWord_length F n iw hm hl _ _
  | threshold j => exact (RowExecution.result F source iw hl).width _
  | crossing j => exact (RowExecution.result F source iw hl).width _

theorem completed_word (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (w : Work) :
    RowExecution.completed F source iw hl (workPort w)=Counter.marked (word F source iw hl w) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  cases w with
  | grid =>
    rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    change (SourceImages.sourceFinal F n iw).base.grid=Counter.marked (EndpointClip.gridWord true n iw)
    cases hn : SourceEndpoints.negative F true <;>
      simp [SourceImages.sourceFinal,SourceEndpoints.final,SourceEndpoints.place,
        EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,EndpointClip.computed,hn]
  | sourceWork j =>
    rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    change (SourceImages.sourceFinal F n iw).base.work j=Counter.marked (sourceProduct F n iw j)
    cases hn : SourceEndpoints.negative F true <;>
      simp [sourceProduct,SourceImages.sourceFinal,SourceEndpoints.final,SourceEndpoints.place,
        EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,EndpointClip.computed,hn]
  | sourceFraction upper j =>
    have hu : RowExecution.rowBinding.decode (workPort (.sourceFraction upper j))=none := by cases upper <;> rfl
    rw [RowExecution.final_framed F source iw hl _ hu]
    cases upper
    · exact SourceImages.source_words F n iw false j
    · exact SourceImages.source_words F n iw true j
  | imageWork j =>
    rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    rfl
  | image j b =>
    fin_cases j
    · rw [RowExecution.final_framed F source iw hl _ (by rfl)]
      exact SourceImages.final_output F n iw 0 b
    · have h := RowExecution.final_fixed_word F source iw hl .delta (false,b) (by decide)
      exact h
    · rw [RowExecution.final_framed F source iw hl _ (by rfl)]
      exact SourceImages.final_output F n iw 2 b
    · have h := RowExecution.final_fixed_word F source iw hl .delta (true,b) (by decide)
      exact h
  | threshold j =>
    have h := RowExecution.final_cell F source iw hl (.word (.threshold,RowPreparation.side j,RowPreparation.sign j))
    fin_cases j <;> exact h
  | crossing j =>
    have h := RowExecution.final_cell F source iw hl (.word (.crossing,RowPreparation.side j,RowPreparation.sign j))
    fin_cases j <;> exact h

theorem completed_temp (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    RowExecution.completed F source iw hl (.prep .temp)=BinaryCarry.preparedOutput :=
  RowExecution.final_cell F source iw hl (.scratch true)

theorem completed_seed (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (j : Fin 6) :
    RowExecution.completed F source iw hl (seedPort j)=
      RowExecution.initial (PaddedWord.word (PaddedWord.commonConstant F) id source) iw (seedPort j) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  fin_cases j
  · rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    exact RowPreparation.images_dimension F n iw
  · rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    change (SourceImages.sourceFinal F n iw).base.index=Counter.marked iw
    cases hn : SourceEndpoints.negative F true <;>
      simp [SourceImages.sourceFinal,SourceEndpoints.final,SourceEndpoints.place,
        EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,EndpointClip.computed,EndpointClip.initial,hn]
  · rw [RowExecution.final_framed F source iw hl _ (by rfl)]
    change (SourceImages.sourceFinal F n iw).base.unit=Counter.marked (ArithmeticSeed.one n.length)
    cases hn : SourceEndpoints.negative F true <;>
      simp [SourceImages.sourceFinal,SourceEndpoints.final,SourceEndpoints.place,
        EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,EndpointClip.computed,EndpointClip.initial,hn]
  · exact RowExecution.final_cell F source iw hl .zero
  · exact RowExecution.final_cell F source iw hl .fuel
  · exact RowExecution.final_cell F source iw hl (.scratch false)

theorem initial_work_blank (n iw : List Bool) (j : Fin 30) :
    RowExecution.initial n iw (dirtyPorts j)=⟨[],[]⟩ := by
  fin_cases j <;> rfl

end TransposeFollowup.RowCleanup


/-! Cleanup preserves the closed overlap stream. The thirty actual eraser
calls are followed by two transitions removing the second scratch marker.
Both outer return transfers are paid. -/
namespace TransposeFollowup.RowCleanup
open FixedTapeCompiler CopyMachine
open RowExecution (Port Bank)
set_option autoImplicit false

def identityBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p q; simp [eq_comm]

inductive Label | batch (pc : NativeBatchErase.Label 30) | clear (pc : NativeUnprepare.Label) | done
  deriving DecidableEq, Fintype

def start : Label := .batch (NativeBatchErase.entry 30 0)

def program : Microcode.Program Port Label
  | .batch .done => .jump (.clear 0)
  | .batch pc => identityBinding.instruction Label.batch (NativeBatchErase.program dirtyPorts pc)
  | .clear pc => if pc=2 then .jump .done else
      (RowExecution.singleBinding (.prep .temp)).instruction Label.clear (NativeUnprepare.program pc)
  | .done => .halt

theorem batch_code (pc : NativeBatchErase.Label 30)
    (hh : NativeBatchErase.program dirtyPorts pc≠.halt) (_ : NativeBatchErase.program dirtyPorts pc≠.reject) :
    program (.batch pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.batch
      (NativeBatchErase.program dirtyPorts pc) := by
  cases pc <;> try exact identityBinding.instruction_eq _ _
  exact False.elim (hh rfl)
theorem clear_code (pc : NativeUnprepare.Label)
    (hh : NativeUnprepare.program pc≠.halt) (_ : NativeUnprepare.program pc≠.reject) :
    program (.clear pc)=MicrocodeEmbedding.instruction (RowExecution.singleBinding (.prep .temp)).ports
      Label.clear (NativeUnprepare.program pc) := by
  have hp : pc≠2 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def zipperCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc,s⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

def eraseWork (s : Bank) : Bank := NativeBatchErase.stage dirtyPorts s 30

def cleared (s : Bank) : Bank := Function.update (eraseWork s) (.prep .temp) ⟨[],[]⟩

def retainedRow (n iw : List Bool) (stream : Tape Bool) : Bank :=
  Function.update (RowExecution.initial n iw) .stream stream

theorem clear_restores (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    cleared (RowExecution.completed F source iw hl)=
      retainedRow (PaddedWord.word (PaddedWord.commonConstant F) id source) iw
        (RowStream.closedTape (RowExecution.result F source iw hl).written) := by
  have hs := RowExecution.final_stream F source iw hl
  rw [← hs]
  funext p
  rcases port_partition p with (⟨j,rfl⟩ | ⟨j,rfl⟩ | rfl | rfl | rfl)
  · simp only [cleared,retainedRow,Function.update_of_ne (dirty_not_temp j),
      Function.update_of_ne (dirty_not_stream j),eraseWork,NativeBatchErase.final_at,initial_work_blank]
  · have hn : ¬∃ k,dirtyPorts k=seedPort j := by rintro ⟨k,h⟩; exact dirty_not_seed k j h
    have ht : seedPort j≠.prep .temp := by fin_cases j <;> decide
    have hq : seedPort j≠.stream := by fin_cases j <;> decide
    simp only [cleared,retainedRow,Function.update_of_ne ht,Function.update_of_ne hq,
      eraseWork,NativeBatchErase.stage_outside _ _ _ _ hn,completed_seed]
  · simp only [cleared,retainedRow,Function.update_self,
      Function.update_of_ne (by decide : Port.prep .temp≠.stream)]
    rfl
  · have hn : ¬∃ j,dirtyPorts j=Port.counter := by rintro ⟨j,h⟩; exact dirty_not_counter j h
    simp only [cleared,retainedRow,Function.update_of_ne (by decide : Port.counter≠.prep .temp),
      Function.update_of_ne (by decide : Port.counter≠.stream),eraseWork,
      NativeBatchErase.stage_outside _ _ _ _ hn,RowExecution.final_counter]
    rfl
  · have hn : ¬∃ j,dirtyPorts j=Port.stream := by rintro ⟨j,h⟩; exact dirty_not_stream j h
    simp only [cleared,retainedRow,Function.update_of_ne (by decide : Port.stream≠.prep .temp),
      Function.update_self,eraseWork,NativeBatchErase.stage_outside _ _ _ _ hn]

theorem eraseWork_temp (s : Bank) : eraseWork s (.prep .temp)=s (.prep .temp) := by
  apply NativeBatchErase.stage_outside
  rintro ⟨j,h⟩
  exact dirty_not_temp j h

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=39 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=245 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=39
    decide +kernel
  · change Fintype.card Label-1+1=245
    decide +kernel

end TransposeFollowup.RowCleanup


/-! Paid reset of all row-preparation workspace, retaining the output row
and its current absolute head position. Stream consumption is separate. -/
namespace TransposeFollowup.RowCleanup
open FixedTapeCompiler CopyMachine
open RowExecution (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem embed_batch (pc : NativeBatchErase.Label 30) (s base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed identityBinding.ports Label.batch (NativeBatchErase.cfg pc s pos) (frame base pos)=
      cfg (.batch pc) s pos := by
  unfold MicrocodeEmbedding.embed NativeBatchErase.cfg cfg frame
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem embed_clear (pc : NativeUnprepare.Label) (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (RowExecution.singleBinding (.prep .temp)).ports Label.clear
      (NativeUnprepare.cfg pc w (fun _ => pos (.prep .temp))).denote (frame s pos)=
      cfg (.clear pc) (Function.update s (.prep .temp) w) pos := by
  unfold MicrocodeEmbedding.embed NativeUnprepare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (RowExecution.singleBinding (.prep .temp)).values_eq_extend]
  congr 2 <;> funext p <;> by_cases h : p=.prep .temp
  all_goals simp [RowExecution.singleBinding,FinitePortBinding.values,Function.update,h]

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem batch_call (words : Fin 30 → List Bool) (m : ℕ) (hw : ∀ j,(words j).length=m)
    (s : Bank) (hs : ∀ j,s (dirtyPorts j)=Counter.marked (words j)) (pos : Port → ℤ) :
    ∃ t ≤ 30*(4*m+5), Trace t (cfg start s pos) (cfg (.batch .done) (eraseWork s) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBatchErase.common_width_trace dirtyPorts words m hw s hs pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports Label.batch
    (NativeBatchErase.program dirtyPorts) program (frame s pos) batch_code htr
  exact ⟨t,ht,by simpa only [embed_batch,start,eraseWork] using he⟩

theorem clear_call (s : Bank) (hs : s (.prep .temp)=BinaryCarry.preparedOutput) (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace t (cfg (.clear 0) s pos)
      (cfg (.clear 2) (Function.update s (.prep .temp) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeUnprepare.complete_trace (fun _ => pos (.prep .temp))
  have he := MicrocodeEmbedding.trace_embed (RowExecution.singleBinding (.prep .temp)).ports Label.clear
    NativeUnprepare.program program (frame s pos) clear_code htr
  exact ⟨t,ht,by simpa only [embed_clear,← hs,Function.update_eq_self] using he⟩

def budget (m : ℕ) := 120*m+154

theorem complete_trace (words : Fin 30 → List Bool) (m : ℕ) (hw : ∀ j,(words j).length=m)
    (s : Bank) (hs : ∀ j,s (dirtyPorts j)=Counter.marked (words j))
    (htemp : s (.prep .temp)=BinaryCarry.preparedOutput) (pos : Port → ℤ) :
    ∃ t ≤ budget m, Trace t (cfg start s pos) (cfg .done (cleared s) pos) := by
  obtain ⟨a,ha,ta⟩ := batch_call words m hw s hs pos
  have ja := jump_trace (.batch .done) (.clear 0) (eraseWork s) pos rfl
  obtain ⟨b,hb,tb⟩ := clear_call (eraseWork s) ((eraseWork_temp s).trans htemp) pos
  have jb := jump_trace (.clear 2) .done (cleared s) pos rfl
  refine ⟨a+1+b+1,by unfold budget; omega,?_⟩
  exact trace_trans (trace_trans (trace_trans ta ja) tb) jb

theorem row_trace (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget n.length, Trace t (cfg start (RowExecution.completed F source iw hl) pos)
      (cfg .done (retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written)) pos) := by
  obtain ⟨t,ht,htr⟩ := complete_trace (fun j => word F source iw hl (workAt j)) _
    (fun j => word_length F source iw hl (workAt j)) (RowExecution.completed F source iw hl)
    (fun j => completed_word F source iw hl (workAt j)) (completed_temp F source iw hl) pos
  exact ⟨t,ht,by simpa only [clear_restores] using htr⟩

theorem native_row (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget n.length,
      Transpose.stepN nativeMachine input t
        ((cfg start (RowExecution.completed F source iw hl) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done (retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written)) pos).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written)) pos).denote
          nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := row_trace F source iw hl pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget n.length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (RowExecution.completed F source iw hl) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written)) pos) outerFrame).denote
            encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := row_trace F source iw hl pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

theorem rational_row_trace (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget n.length, Trace t
      (cfg start (RowExecution.completed F source iw hl) (RowExecution.positions pos (F.denseRow i)))
      (cfg .done (retainedRow n iw (RowStream.closedTape (F.denseRow i))) (RowExecution.positions pos (F.denseRow i))) := by
  simpa only [RowExecution.result_written F source i iw hl hv] using
    row_trace F source iw hl (RowExecution.positions pos (F.denseRow i))

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1 ≤ N) (hl : source.length ≤ (N+1).size) :
    N*budget (PaddedWord.word (PaddedWord.commonConstant F) id source).length ≤
      (240*(F.integerOperandConstant^2).size+2708)*Transpose.inputLength N := by
  have h := dense_scan_budget (120*PaddedWord.commonConstant F+154) 240 N hN
  have hm : budget (PaddedWord.word (PaddedWord.commonConstant F) id source).length ≤
      (120*PaddedWord.commonConstant F+154)+240*(N+1).size := by
    unfold budget
    rw [PaddedWord.word_length]
    nlinarith
  have hc : 2*(120*PaddedWord.commonConstant F+154+3*240)=
      240*(F.integerOperandConstant^2).size+2708 := by unfold PaddedWord.commonConstant; ring
  calc
    _ ≤ N*((120*PaddedWord.commonConstant F+154)+240*(N+1).size) := Nat.mul_le_mul_left _ hm
    _ ≤ N*(N*((120*PaddedWord.commonConstant F+154)+240*(N+1).size)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hN)
    _ ≤ _ := by simpa only [hc] using h

end TransposeFollowup.RowCleanup


/-! One actual caller computes a row and clears its preparation workspace.
The closed stream is retained at its advanced head; a future consumer must
still process and reset it before the next call. -/
namespace TransposeFollowup.ReusableRow
open FixedTapeCompiler CopyMachine
open RowExecution (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

inductive Label (F : RationalMobius)
  | run (pc : RowExecution.Label F)
  | cleanup (saved : Bool) (pc : RowCleanup.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F := .run (RowExecution.start F)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .run (.done saved) => .jump (.cleanup saved RowCleanup.start)
  | .run pc => RowCleanup.identityBinding.instruction Label.run (RowExecution.program F pc)
  | .cleanup saved .done => .jump (.done saved)
  | .cleanup saved pc => RowCleanup.identityBinding.instruction (Label.cleanup saved) (RowCleanup.program pc)
  | .done _ => .halt

theorem run_code (F : RationalMobius) (pc : RowExecution.Label F)
    (hh : RowExecution.program F pc≠.halt) (_ : RowExecution.program F pc≠.reject) :
    program F (.run pc)=MicrocodeEmbedding.instruction RowCleanup.identityBinding.ports Label.run
      (RowExecution.program F pc) := by
  cases pc <;> try exact RowCleanup.identityBinding.instruction_eq _ _
  exact False.elim (hh rfl)
theorem cleanup_code (F : RationalMobius) (saved : Bool) (pc : RowCleanup.Label)
    (hh : RowCleanup.program pc≠.halt) (_ : RowCleanup.program pc≠.reject) :
    program F (.cleanup saved pc)=MicrocodeEmbedding.instruction RowCleanup.identityBinding.ports (Label.cleanup saved)
      (RowCleanup.program pc) := by
  cases pc <;> try exact RowCleanup.identityBinding.instruction_eq _ _
  exact False.elim (hh rfl)

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def zipperCfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label F) :=
  ⟨⟨pc,s⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

abbrev Trace (F : RationalMobius) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem embed_run (F : RationalMobius) (pc : RowExecution.Label F) (s base : Bank) (pos basePos : Port → ℤ) :
    MicrocodeEmbedding.embed RowCleanup.identityBinding.ports (Label.run (F := F))
      (RowExecution.cfg pc s pos) (frame base basePos)=cfg (.run pc) s pos := by
  unfold MicrocodeEmbedding.embed RowExecution.cfg cfg frame
  simp only [← RowCleanup.identityBinding.values_eq_extend]
  rfl

theorem embed_cleanup (F : RationalMobius) (saved : Bool) (pc : RowCleanup.Label)
    (s base : Bank) (pos basePos : Port → ℤ) :
    MicrocodeEmbedding.embed RowCleanup.identityBinding.ports (Label.cleanup (F := F) saved)
      (RowCleanup.cfg pc s pos) (frame base basePos)=cfg (.cleanup saved pc) s pos := by
  unfold MicrocodeEmbedding.embed RowCleanup.cfg cfg frame
  simp only [← RowCleanup.identityBinding.values_eq_extend]
  rfl

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

def budget (F : RationalMobius) (n : List Bool) := RowExecution.budget F n+RowCleanup.budget n.length+2

theorem complete_trace (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n, Trace F t (cfg (start F) (RowExecution.initial n iw) pos)
      (cfg (.done (SourceImages.sourceAnswer F n iw))
        (RowCleanup.retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written))
        (RowExecution.positions pos (RowExecution.result F source iw hl).written)) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  let saved := SourceImages.sourceAnswer F n iw
  let out := RowExecution.completed F source iw hl
  let endpos := RowExecution.positions pos (RowExecution.result F source iw hl).written
  let final := RowCleanup.retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written)
  obtain ⟨a,ha,ta⟩ := RowExecution.complete_trace F source iw hl pos
  have ea := MicrocodeEmbedding.trace_embed RowCleanup.identityBinding.ports (Label.run (F := F))
    (RowExecution.program F) (program F) (frame (RowExecution.initial n iw) pos) (run_code F) ta
  have ea' : Trace F a (cfg (start F) (RowExecution.initial n iw) pos) (cfg (.run (.done saved)) out endpos) := by
    simpa only [embed_run,start] using ea
  have ja := jump_trace F (.run (.done saved)) (.cleanup saved RowCleanup.start) out endpos rfl
  obtain ⟨b,hb,tb⟩ := RowCleanup.row_trace F source iw hl endpos
  have eb := MicrocodeEmbedding.trace_embed RowCleanup.identityBinding.ports (Label.cleanup saved)
    RowCleanup.program (program F) (frame out endpos) (cleanup_code F saved) tb
  have eb' : Trace F b (cfg (.cleanup saved RowCleanup.start) out endpos) (cfg (.cleanup saved .done) final endpos) := by
    simpa only [embed_cleanup] using eb
  have jb := jump_trace F (.cleanup saved .done) (.done saved) final endpos rfl
  refine ⟨a+1+b+1,?_,trace_trans (trace_trans (trace_trans ea' ja) eb') jb⟩
  dsimp only [budget]
  omega

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T := Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

theorem native_complete (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (RowExecution.initial n iw) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg (.done (SourceImages.sourceAnswer F n iw))
          (RowCleanup.retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written))
          (RowExecution.positions pos (RowExecution.result F source iw hl).written)).denote
            (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg (.done (SourceImages.sourceAnswer F n iw))
          (RowCleanup.retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written))
          (RowExecution.positions pos (RowExecution.result F source iw hl).written)).denote
            (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (RowExecution.initial n iw) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (SourceImages.sourceAnswer F n iw))
            (RowCleanup.retainedRow n iw (RowStream.closedTape (RowExecution.result F source iw hl).written))
            (RowExecution.positions pos (RowExecution.result F source iw hl).written)) outerFrame).denote
              encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

theorem rational_trace (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n, Trace F t (cfg (start F) (RowExecution.initial n iw) pos)
      (cfg (.done (RowStream.rowGuard F i)) (RowCleanup.retainedRow n iw (RowStream.closedTape (F.denseRow i)))
        (RowExecution.positions pos (F.denseRow i))) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source iw hl pos
  have ha : SourceImages.sourceAnswer F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw=
      RowStream.rowGuard F i := SourceEndpoints.answer_rational F source i iw hl hv
  exact ⟨t,ht,by simpa only [ha,RowExecution.result_written F source i iw hl hv] using htr⟩

def labelEquiv (F : RationalMobius) : Label F ≃ RowExecution.Label F ⊕ (Bool × RowCleanup.Label) ⊕ Bool where
  toFun | .run pc => .inl pc | .cleanup saved pc => .inr (.inl (saved,pc)) | .done saved => .inr (.inr saved)
  invFun | .inl pc => .run pc | .inr (.inl (saved,pc)) => .cleanup saved pc | .inr (.inr saved) => .done saved
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,pc⟩ | saved) <;> rfl

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=39 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+12073 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=39
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hc : Fintype.card RowCleanup.Label=245 := by decide +kernel
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hc,RowExecution.label_card]
    omega

theorem budget_expansion (F : RationalMobius) (n : List Bool) :
    budget F n=Counter.value n*(190*n.length+451)+
      (674+36*(SourceImages.sourceSum F+SourceImages.coefficientSum F))*n.length+
      1539+104*(SourceImages.sourceSum F+SourceImages.coefficientSum F) := by
  unfold budget RowCleanup.budget
  rw [RowExecution.budget_expansion]
  ring

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1 ≤ N) (hv : Counter.value source=N) (hl : source.length ≤ (N+1).size) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    N*budget F (PaddedWord.word (PaddedWord.commonConstant F) id source) ≤
      ((1728+72*T)*(F.integerOperandConstant^2).size+21260+928*T)*Transpose.inputLength N := by
  dsimp only
  have hr := RowExecution.total_budget F N source hN hv hl
  have hc := RowCleanup.total_budget F N source hN hl
  have hd := dense_scan_budget 1 0 N hN
  have hn : N ≤ 2*Transpose.inputLength N := by
    have hnn : N ≤ N*N := Nat.le_mul_of_pos_left _ hN
    norm_num at hd
    exact hnn.trans hd
  unfold budget
  dsimp only at hr
  nlinarith

end TransposeFollowup.ReusableRow


namespace TransposeFollowup.RecordedRow
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | row (p : RowExecution.Port) | output
  deriving DecidableEq, Fintype

def rowBinding : FinitePortBinding RowExecution.Port Port where
  ports := ⟨Port.row,fun _ _ h => Port.row.inj h⟩
  decode := fun p => match p with | .row t => some t | .output => none
  decode_spec := by
    intro p t
    change (match p with | .row u => some u | .output => none)=some t ↔ Port.row t=p
    cases p <;> simp [eq_comm]

def consumerPort : RowConsumer.Port → Port
  | .stream => .row .stream | .index => .row .counter
  | .rowIndex => .row (.prep (.images (.source (.shared .index))))
  | .unit => .row (.prep (.images (.source (.shared .unit))))
  | .zero => .row (.prep (.images (.source (.shared .zero))))
  | .fuel => .row (.prep (.images (.source (.shared .fuel))))
  | .scratch => .row (.prep (.images (.source (.shared .scratch))))
  | .output => .output

def consumerBinding : FinitePortBinding RowConsumer.Port Port where
  ports := ⟨consumerPort,by decide +kernel⟩
  decode := fun p => match p with
    | .row .stream => some .stream | .row .counter => some .index
    | .row (.prep (.images (.source (.shared .index)))) => some .rowIndex
    | .row (.prep (.images (.source (.shared .unit)))) => some .unit
    | .row (.prep (.images (.source (.shared .zero)))) => some .zero
    | .row (.prep (.images (.source (.shared .fuel)))) => some .fuel
    | .row (.prep (.images (.source (.shared .scratch)))) => some .scratch
    | .output => some .output | _ => none
  decode_spec := by decide +kernel

inductive Label (F : RationalMobius)
  | row (pc : ReusableRow.Label F)
  | consume (saved : Bool) (pc : RowConsumer.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F := .row (ReusableRow.start F)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .row (.done saved) => .jump (.consume saved RowConsumer.start)
  | .row pc => rowBinding.instruction Label.row (ReusableRow.program F pc)
  | .consume saved .done => .jump (.done saved)
  | .consume saved pc => consumerBinding.instruction (Label.consume saved) (RowConsumer.program pc)
  | .done _ => .halt

theorem row_code (F : RationalMobius) (pc : ReusableRow.Label F)
    (hh : ReusableRow.program F pc≠.halt) (_ : ReusableRow.program F pc≠.reject) :
    program F (.row pc)=MicrocodeEmbedding.instruction rowBinding.ports Label.row (ReusableRow.program F pc) := by
  cases pc <;> try exact rowBinding.instruction_eq _ _
  exact False.elim (hh rfl)

theorem consumer_code (F : RationalMobius) (saved : Bool) (pc : RowConsumer.Label)
    (hh : RowConsumer.program pc≠.halt) (_ : RowConsumer.program pc≠.reject) :
    program F (.consume saved pc)=MicrocodeEmbedding.instruction consumerBinding.ports
      (Label.consume saved) (RowConsumer.program pc) := by
  cases pc <;> simp_all only [program,FinitePortBinding.instruction_eq,RowConsumer.program]
  exact False.elim (hh rfl)


abbrev Bank := Port → Tape Bool

def liftBank (b : RowExecution.Bank) (pre : List (Sym Bool)) : Bank
  | .row p => b p | .output => ⟨pre,[]⟩

def initial (n iw : List Bool) (pre : List (Sym Bool)) := liftBank (RowExecution.initial n iw) pre

def consumerBank (n iw : List Bool) (w : RowConsumer.Work) : Bank :=
  consumerBinding.values (RowConsumer.bank iw (ArithmeticSeed.one n.length) w) (initial n iw w.pre)

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩

def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

def rowPositions (pos : Port → ℤ) (flags : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.row .stream then (flags.length : ℤ) else 0

def finalPositions (pos : Port → ℤ) (bits : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.output then (bits.length : ℤ) else 0

abbrev Trace (F : RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem consumer_initial (n iw flags : List Bool) (hm : 0<n.length) (pre : List (Sym Bool)) :
    consumerBank n iw (RowConsumer.initial flags pre)=
      liftBank (RowCleanup.retainedRow n iw (RowStream.closedTape flags)) pre := by
  funext p
  fin_cases p <;>
    simp only [consumerBank,consumerBinding,FinitePortBinding.values,RowConsumer.bank,RowConsumer.initial,
      initial,liftBank,RowCleanup.retainedRow,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      ArithmeticSeed.one_length _ hm,ArithmeticSeed.zeros,Function.update] <;> rfl

theorem consumer_final (n iw : List Bool) (hm : 0<n.length) (pre : List (Sym Bool)) :
    consumerBank n iw (RowConsumer.final pre)=initial n iw pre := by
  funext p
  fin_cases p <;>
    simp only [consumerBank,consumerBinding,FinitePortBinding.values,RowConsumer.bank,RowConsumer.final,
      initial,liftBank,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      ArithmeticSeed.one_length _ hm,ArithmeticSeed.zeros] <;> rfl

end TransposeFollowup.RecordedRow


namespace TransposeFollowup.RecordedRow
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem embed_row (F : RationalMobius) (pc : ReusableRow.Label F)
    (s base : RowExecution.Bank) (pre : List (Sym Bool)) (rpos : RowExecution.Port → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed rowBinding.ports (Label.row (F:=F)) (ReusableRow.cfg pc s rpos)
      (frame (liftBank base pre) pos)=
      cfg (.row pc) (liftBank s pre) (rowBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed ReusableRow.cfg cfg frame
  simp only [← rowBinding.values_eq_extend]
  congr 2
  funext p; cases p <;> rfl

theorem embed_consumer (F : RationalMobius) (saved : Bool) (pc : RowConsumer.Label)
    (n iw : List Bool) (w : RowConsumer.Work) (pre : List (Sym Bool))
    (cpos : RowConsumer.Port → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed consumerBinding.ports (Label.consume (F:=F) saved)
      (RowConsumer.cfg pc iw (ArithmeticSeed.one n.length) w cpos)
      (frame (initial n iw pre) pos)=
      cfg (.consume saved pc) (consumerBank n iw w) (consumerBinding.values cpos pos) := by
  unfold MicrocodeEmbedding.embed RowConsumer.cfg cfg frame consumerBank
  simp only [← consumerBinding.values_eq_extend]
  congr 2
  funext p; fin_cases p <;> rfl

theorem row_positions_initial (pos : Port → ℤ) :
    rowBinding.values (fun p => pos (.row p)) pos=pos := by
  funext p; cases p <;> rfl

theorem row_positions_final (pos : Port → ℤ) (flags : List Bool) :
    rowBinding.values (RowExecution.positions (fun p => pos (.row p)) flags) pos=rowPositions pos flags := by
  funext p
  cases p with
  | row p => cases p <;> simp [rowBinding,FinitePortBinding.values,RowExecution.positions,rowPositions]
  | output => simp [rowBinding,FinitePortBinding.values,rowPositions]

theorem consumer_positions_initial (pos : Port → ℤ) :
    consumerBinding.values (fun p => pos (consumerPort p)) pos=pos := by
  funext p; fin_cases p <;> rfl

theorem consumer_positions_final (pos : Port → ℤ) (flags bits : List Bool) :
    consumerBinding.values
      (RowConsumer.positions (fun p => rowPositions pos flags (consumerPort p))
        (-(flags.length : ℤ)) bits.length) (rowPositions pos flags)=finalPositions pos bits := by
  funext p
  fin_cases p <;>
    dsimp only [Port.proxyTypeEquiv,RowExecution.Port.proxyTypeEquiv,RowPreparation.Port.proxyTypeEquiv,
      SourceImages.Port.proxyTypeEquiv,SourceEndpoints.Port.proxyTypeEquiv,EndpointClip.Port.proxyTypeEquiv] <;>
    simp [consumerBinding,consumerPort,FinitePortBinding.values,RowConsumer.positions,rowPositions,finalPositions]

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

def records (n iw flags : List Bool) : List Bool := RowConsumer.output iw (ArithmeticSeed.one n.length) flags

def budget (F : RationalMobius) (n flags : List Bool) : ℕ :=
  ReusableRow.budget F n+RowConsumer.budget n.length flags+2

theorem consumer_call (F : RationalMobius) (saved : Bool) (n iw flags : List Bool)
    (hm : 0<n.length) (hl : iw.length=n.length) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ RowConsumer.budget n.length flags, Trace F t
      (cfg (.consume saved RowConsumer.start)
        (liftBank (RowCleanup.retainedRow n iw (RowStream.closedTape flags)) pre) (rowPositions pos flags))
      (cfg (.consume saved .done) (initial n iw ((symbols (records n iw flags)).reverse++pre))
        (finalPositions pos (records n iw flags))) := by
  have hu := ArithmeticSeed.one_length n.length hm
  obtain ⟨t,ht,htr⟩ := RowConsumer.complete_trace iw (ArithmeticSeed.one n.length) flags
    (hl.trans hu.symm) pre (fun p => rowPositions pos flags (consumerPort p))
  have he := MicrocodeEmbedding.trace_embed consumerBinding.ports (Label.consume (F:=F) saved)
    RowConsumer.program (program F) (frame (initial n iw pre) (rowPositions pos flags)) (consumer_code F saved) htr
  refine ⟨t,by simpa only [hu] using ht,?_⟩
  simpa only [embed_consumer,consumer_initial n iw flags hm,consumer_final n iw hm,
    consumer_positions_initial,consumer_positions_final,records] using he

theorem rational_trace (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n (F.denseRow i), Trace F t (cfg (start F) (initial n iw pre) pos)
      (cfg (.done (RowStream.rowGuard F i))
        (initial n iw ((symbols (records n iw (F.denseRow i))).reverse++pre))
        (finalPositions pos (records n iw (F.denseRow i)))) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := by dsimp [n]; rw [PaddedWord.word_length]; unfold PaddedWord.commonConstant; omega
  let saved := RowStream.rowGuard F i
  let mid := liftBank (RowCleanup.retainedRow n iw (RowStream.closedTape (F.denseRow i))) pre
  let midpos := rowPositions pos (F.denseRow i)
  let out := initial n iw ((symbols (records n iw (F.denseRow i))).reverse++pre)
  let outpos := finalPositions pos (records n iw (F.denseRow i))
  obtain ⟨a,ha,ta⟩ := ReusableRow.rational_trace F source i iw hl hv (fun p => pos (.row p))
  have ea := MicrocodeEmbedding.trace_embed rowBinding.ports (Label.row (F:=F))
    (ReusableRow.program F) (program F) (frame (initial n iw pre) pos) (row_code F) ta
  have ea' : Trace F a (cfg (start F) (initial n iw pre) pos) (cfg (.row (.done saved)) mid midpos) := by
    simpa only [initial,embed_row,row_positions_initial,row_positions_final,start] using ea
  have ja := jump_trace F (.row (.done saved)) (.consume saved RowConsumer.start) mid midpos rfl
  obtain ⟨b,hb,tb⟩ := consumer_call F saved n iw (F.denseRow i) hm hl pre pos
  have jb := jump_trace F (.consume saved .done) (.done saved) out outpos rfl
  refine ⟨a+1+b+1,?_,trace_trans (trace_trans (trace_trans ea' ja) tb) jb⟩
  change a+1+b+1 ≤ ReusableRow.budget F n+RowConsumer.budget n.length (F.denseRow i)+2
  change a ≤ ReusableRow.budget F n at ha
  omega

end TransposeFollowup.RecordedRow


namespace TransposeFollowup.RecordedRow
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

theorem native_row (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pre : List (Sym Bool)) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n (F.denseRow i),
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (initial n iw pre) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg (.done (RowStream.rowGuard F i))
          (initial n iw ((symbols (records n iw (F.denseRow i))).reverse++pre))
          (finalPositions pos (records n iw (F.denseRow i)))).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg (.done (RowStream.rowGuard F i))
          (initial n iw ((symbols (records n iw (F.denseRow i))).reverse++pre))
          (finalPositions pos (records n iw (F.denseRow i)))).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := rational_trace F source i iw hl hv pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (source : List Bool) (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pre : List (Sym Bool)) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ budget F n (F.denseRow i),
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (initial n iw pre) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (RowStream.rowGuard F i))
            (initial n iw ((symbols (records n iw (F.denseRow i))).reverse++pre))
            (finalPositions pos (records n iw (F.denseRow i)))) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := rational_trace F source i iw hl hv pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

def labelEquiv (F : RationalMobius) : Label F ≃ ReusableRow.Label F ⊕ (Bool × RowConsumer.Label) ⊕ Bool where
  toFun | .row pc => .inl pc | .consume saved pc => .inr (.inl (saved,pc)) | .done saved => .inr (.inr saved)
  invFun | .inl pc => .row pc | .inr (.inl (saved,pc)) => .consume saved pc | .inr (.inr saved) => .done saved
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,pc⟩ | saved) <;> rfl

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=40 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+12405 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=40
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hc : Fintype.card RowConsumer.Label=165 := by decide +kernel
    have hr : Fintype.card (ReusableRow.Label F)=
        198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
        396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+12073 := by
      rw [Fintype.card_congr (ReusableRow.labelEquiv F)]
      have hk : Fintype.card RowCleanup.Label=245 := by decide +kernel
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hk,RowExecution.label_card]
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,hc,hr]
    omega

theorem budget_expansion (F : RationalMobius) (n flags : List Bool) (hf : flags.length=Counter.value n) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    budget F n flags=flags.length*(208*n.length+509)+flags.count true*(8*n.length+12)+
      (684+36*T)*n.length+1571+104*T := by
  unfold budget
  rw [ReusableRow.budget_expansion,← hf]
  unfold RowConsumer.budget
  dsimp only
  ring

theorem budget_le (F : RationalMobius) (n flags : List Bool) (hf : flags.length=Counter.value n) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    budget F n flags ≤ flags.length*(216*n.length+521)+(684+36*T)*n.length+1571+104*T := by
  rw [budget_expansion F n flags hf]
  have h := List.count_le_length (l:=flags) (a:=true)
  dsimp only
  nlinarith

theorem records_length (n iw flags : List Bool) (hm : 0<n.length) (hl : iw.length=n.length) :
    (records n iw flags).length=2*n.length*(flags.count true) := by
  have hu := ArithmeticSeed.one_length n.length hm
  simpa only [records,hu] using RowConsumer.output_length iw (ArithmeticSeed.one n.length) flags (hl.trans hu.symm)

theorem total_budget (F : RationalMobius) (N : ℕ) (source flags : List Bool)
    (hN : 1 ≤ N) (hv : Counter.value source=N) (hl : source.length ≤ (N+1).size) (hf : flags.length=N) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    N*budget F (PaddedWord.word (PaddedWord.commonConstant F) id source) flags ≤
      ((1800+72*T)*(F.integerOperandConstant^2).size+22184+928*T)*Transpose.inputLength N := by
  have hr := ReusableRow.total_budget F N source hN hv hl
  have hc := RowConsumer.total_budget F N source flags hN hl hf
  have hd := dense_scan_budget 1 0 N hN
  have hn : N ≤ 2*Transpose.inputLength N := by
    have hnn : N ≤ N*N := Nat.le_mul_of_pos_left _ hN
    norm_num at hd
    exact hnn.trans hd
  unfold budget
  dsimp only at hr ⊢
  nlinarith

end TransposeFollowup.RecordedRow
