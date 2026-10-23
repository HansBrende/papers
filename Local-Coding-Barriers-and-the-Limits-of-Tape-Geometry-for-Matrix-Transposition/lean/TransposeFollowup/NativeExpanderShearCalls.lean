import TransposeFollowup.NativeExpanderShearMachine
import TransposeFollowup.NativeExpanderShearMetadataInterface

/-! Actual calls in the raw shear controller, with all untouched metadata kept
in the caller's frame. -/
namespace TransposeFollowup.NativeExpanderShearMachine
open FixedTapeCompiler CopyMachine
open NativeExpanderShearFrames ExpanderShearOpcodeBridge
set_option autoImplicit false
variable {r : ℕ}

def metadataBank (F : Fin (r+1) → RationalMobius) (w xs ms : List Bool) : Bank (rationalPageCount F) :=
  metaBinding.values (NativeExpanderShearMetadata.finalBank F w xs ms) blank

def metadataPos (F : Fin (r+1) → RationalMobius) (ms : List Bool) : Port (rationalPageCount F) → ℤ :=
  metaBinding.values (NativeExpanderShearMetadata.finalPositions F ms (fun _ => 0)) (fun _ => 0)

def preparedBank (F : Fin (r+1) → RationalMobius) (w xs ms : List Bool) (m : ℕ) : Bank (rationalPageCount F) :=
  prepareBinding.values (NativeExpanderShearPrepare.final xs ms (sourceRows F m) (targetRows F m))
    (metadataBank F w xs ms)

def preparedPos (F : Fin (r+1) → RationalMobius) (ms : List Bool) (m : ℕ) : Port (rationalPageCount F) → ℤ :=
  prepareBinding.values (NativeExpanderShearPrepare.finalPos
    (fun p => metadataPos F ms (preparePort p)) m) (metadataPos F ms)

theorem metadata_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (d : ℕ)
    (hd : 2≤d) (hw : w.length=Transpose.inputLength d) :
    ∃ xs ms,NativeTrim.Normalized xs ∧ Counter.value xs=d ∧ xs.length=d.size ∧
      NativeTrim.Normalized ms ∧ Counter.value ms=d/2 ∧ ms.length=(d/2).size ∧
    ∃ t ≤ NativeExpanderShearMetadata.coefficient F*w.length,
      Trace F w t (cfg (start F) blank (fun _ => 0) 0 [])
      (cfg (.metadata (.generate (.schedule .done))) (metadataBank F w xs ms) (metadataPos F ms) w.length []) := by
  obtain ⟨xs,ms,hx,hv,hl,hy,hyv,hyl,t,ht,htr⟩ := NativeExpanderShearMetadata.complete_trace F w d hd hw (fun _ => 0) []
  have he := NativeIOEmbedding.trace_embed metaBinding.ports (Label.metadata (F:=F))
    (NativeExpanderShearMetadata.program F) (program F) (frame blank (fun _ => 0)) w (meta_code F) htr
  have hi : (metaBinding (q:=rationalPageCount F)).values NativeExpanderShearMetadata.initial blank=blank := by
    funext p; cases p <;> rfl
  have hp : (metaBinding (q:=rationalPageCount F)).values (fun _ => (0:ℤ)) (fun _ => 0)=(fun _ => 0) := by
    funext p; cases p <;> rfl
  refine ⟨xs,ms,hx,hv,hl,hy,hyv,hyl,t,ht,?_⟩
  change Trace F w t
    (NativeIOEmbedding.embed metaBinding.ports Label.metadata
      (cfg (NativeExpanderShearMetadata.start F) NativeExpanderShearMetadata.initial (fun _ => 0) 0 []) (frame blank (fun _ => 0)))
    (NativeIOEmbedding.embed metaBinding.ports Label.metadata
      (cfg (.generate (.schedule .done)) (NativeExpanderShearMetadata.finalBank F w xs ms)
        (NativeExpanderShearMetadata.finalPositions F ms (fun _ => 0)) w.length []) (frame blank (fun _ => 0))) at he
  simpa only [embed_io,hi,hp,start,metadataBank,metadataPos] using he

theorem prepare_projection (F : Fin (r+1) → RationalMobius) (w xs ms : List Bool) (m : ℕ)
    (hv : Counter.value ms=m) :
    (fun p => metadataBank F w xs ms (preparePort p))=
      NativeExpanderShearPrepare.initial xs ms (NativeMatchingXorMasks.encode (sourceRows F m++targetRows F m)) := by
  funext p
  cases p with
  | inl p => cases p <;>
      simp [metadataBank,metaBinding,FinitePortBinding.values,preparePort,blank,
        NativeExpanderShearPrepare.initial,RadiusBuilder.initial]
  | inr p => cases p with
    | opcode => exact NativeExpanderShearMetadataInterface.opcode_tape F w xs ms m hv
    | _ => simp [metadataBank,metaBinding,FinitePortBinding.values,preparePort,blank,
        NativeExpanderShearPrepare.initial]

theorem prepare_call (F : Fin (r+1) → RationalMobius) (w xs ms : List Bool) (m : ℕ)
    (hx : 0<Counter.value xs) (hv : Counter.value ms=m) :
    ∃ t ≤ NativeExpanderShearPrepare.budget (rationalPageCount F) xs ms
        (NativeMatchingXorMasks.encode (sourceRows F m++targetRows F m)) m,
      Trace F w t
      (cfg (.prep NativeExpanderShearPrepare.start) (metadataBank F w xs ms) (metadataPos F ms) w.length [])
      (cfg (.prep .done) (preparedBank F w xs ms m) (preparedPos F ms m) w.length []) := by
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearPrepare.complete_trace (pivot F)
    (sourceRows F m) (targetRows F m) (sourceRows_width F m) (targetRows_width F m)
    (by simp) xs ms hx (by simpa using hv) (fun p => metadataPos F ms (preparePort p))
  have he := MicrocodeEmbedding.trace_embed prepareBinding.ports (Label.prep (F:=F))
    (NativeExpanderShearPrepare.program (pivot F)) (NativeIO.workProgram (program F))
    (frame (metadataBank F w xs ms) (metadataPos F ms)) (prepare_code F) htr
  change OperationalTrace.Trace (NativeMicrocode.step (NativeIO.workProgram (program F)))
    (NativeMicrocode.Active (NativeIO.workProgram (program F))) t
    (MicrocodeEmbedding.embed prepareBinding.ports Label.prep
      (workCfg NativeExpanderShearPrepare.start
        (NativeExpanderShearPrepare.initial xs ms (NativeMatchingXorMasks.encode (sourceRows F m++targetRows F m)))
        (fun p => metadataPos F ms (preparePort p)))
      (frame (metadataBank F w xs ms) (metadataPos F ms)))
    (MicrocodeEmbedding.embed prepareBinding.ports Label.prep
      (workCfg .done (NativeExpanderShearPrepare.final xs ms (sourceRows F m) (targetRows F m))
        (NativeExpanderShearPrepare.finalPos (fun p => metadataPos F ms (preparePort p)) (sourceRows F m).length))
      (frame (metadataBank F w xs ms) (metadataPos F ms))) at he
  rw [embed_work,embed_work,sourceRows_length] at he
  have hi : prepareBinding.values
      (NativeExpanderShearPrepare.initial xs ms (NativeMatchingXorMasks.encode (sourceRows F m++targetRows F m)))
      (metadataBank F w xs ms)=metadataBank F w xs ms := by
    rw [←prepare_projection F w xs ms m hv]; exact prepareBinding.values_project _
  have hp : prepareBinding.values (fun p => metadataPos F ms (preparePort p)) (metadataPos F ms)=metadataPos F ms :=
    prepareBinding.values_project _
  rw [hi,hp] at he
  exact ⟨t,by simpa using ht,NativeIO.lift_work_trace (program F) w w.length [] he⟩



def dataFinal (F : Fin (r+1) → RationalMobius) (base : Bank (rationalPageCount F))
    (A B : List Bool) (a b : Fin (rationalPageCount F) → List Bool) : Bank (rationalPageCount F) :=
  dataBinding.values (NativeMatchingXorPages.bank (Counter.marked (A++B))
    (NativeClosedStream.word (A++NativeMatchingXorPages.output A B a b (rationalPageCount F))) a b) base

def dataFinalPos (F : Fin (r+1) → RationalMobius) (pos : Port (rationalPageCount F) → ℤ)
    (N : ℕ) : Port (rationalPageCount F) → ℤ :=
  dataBinding.values (NativeMatchingXorData.positioned (fun p => pos (dataPort p)) (2*N)) pos

theorem data_call (F : Fin (r+1) → RationalMobius) (w : List Bool)
    (s : Bank (rationalPageCount F)) (pos : Port (rationalPageCount F) → ℤ)
    (A B : List Bool) (a b : Fin (rationalPageCount F) → List Bool)
    (hB : B.length=A.length) (hvalid : NativeMatchingXorPages.ValidTags A.length a b)
    (hproject : (fun p => s (dataPort p))=NativeMatchingXorPages.bank (Counter.marked (A++B)) ⟨[],[]⟩ a b) :
    ∃ t ≤ rationalPageCount F*(8*A.length+8)+24*A.length+28,
      Trace F w t (cfg (.data (NativeMatchingXorData.start (rationalPageCount F))) s pos w.length [])
        (cfg (.data (.emit .done)) (dataFinal F s A B a b) (dataFinalPos F pos A.length) w.length
          (A++NativeMatchingXorPages.output A B a b (rationalPageCount F)).reverse) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorData.data_trace (pivot F) A B a b hB hvalid
    (fun p => pos (dataPort p)) w w.length []
  have he := NativeIOEmbedding.trace_embed dataBinding.ports (Label.data (F:=F))
    (NativeMatchingXorData.program (pivot F)) (program F) (frame s pos) w (data_code F) htr
  change Trace F w t
    (NativeIOEmbedding.embed dataBinding.ports Label.data
      (cfg (NativeMatchingXorData.start (rationalPageCount F))
        (NativeMatchingXorPages.bank (Counter.marked (A++B)) ⟨[],[]⟩ a b)
        (fun p => pos (dataPort p)) w.length []) (frame s pos))
    (NativeIOEmbedding.embed dataBinding.ports Label.data
      (cfg (.emit .done) (NativeMatchingXorPages.bank (Counter.marked (A++B))
        (NativeClosedStream.word (A++NativeMatchingXorPages.output A B a b (rationalPageCount F))) a b)
        (NativeMatchingXorData.positioned (fun p => pos (dataPort p)) (2*A.length)) w.length
        ((A++NativeMatchingXorPages.output A B a b (rationalPageCount F)).reverse++[])) (frame s pos)) at he
  have hsi : dataBinding.values (fun p => s (dataPort p)) s=s := dataBinding.values_project _
  have hpi : dataBinding.values (fun p => pos (dataPort p)) pos=pos := dataBinding.values_project _
  rw [embed_io,embed_io,←hproject,hsi,hpi,List.append_nil] at he
  exact ⟨t,ht,he⟩

def sourceTags (F : Fin (r+1) → RationalMobius) (m W : ℕ) (p : Fin (rationalPageCount F)) : List Bool :=
  NativeExpanderShearSemantics.tagBits W (fun i : Fin m => rationalOutgoingOn F i p)
def targetTags (F : Fin (r+1) → RationalMobius) (m W : ℕ) (p : Fin (rationalPageCount F)) : List Bool :=
  NativeExpanderShearSemantics.tagBits W (fun i : Fin m => rationalIncomingOn F i p)

theorem prepared_data_projection (F : Fin (r+1) → RationalMobius) (A B xs ms : List Bool) (m W : ℕ)
    (hW : (ExpanderShearClock.word xs).length=W) :
    (fun p => preparedBank F (A++B) xs ms m (dataPort p))=
      NativeMatchingXorPages.bank (Counter.marked (A++B)) ⟨[],[]⟩ (sourceTags F m W) (targetTags F m W) := by
  funext p
  cases p with
  | source =>
    simp [preparedBank,metadataBank,prepareBinding,FinitePortBinding.values,metaBinding,
      dataPort,NativeMatchingXorPages.bank,VertexScheduler.outputPort,SchedulerSeed.pagePort,RawEnumeration.sharedPort]
  | target => rfl
  | tagA p =>
    change NativeExpanderShearPrepare.final xs ms (sourceRows F m) (targetRows F m) (.inr (.tag false p))=_
    rw [NativeExpanderShearPrepare.final_tag,hW]
    simp only [NativeExpanderShearPrepare.flags,Bool.false_eq_true,ite_false,
      flags_source,NativeExpanderShearSemantics.tagBits_expanded]
    rfl
  | tagB p =>
    change NativeExpanderShearPrepare.final xs ms (sourceRows F m) (targetRows F m) (.inr (.tag true p))=_
    rw [NativeExpanderShearPrepare.final_tag,hW]
    simp only [NativeExpanderShearPrepare.flags,ite_true,
      flags_target_reverse,NativeExpanderShearSemantics.tagBits_expanded]
    rfl

end TransposeFollowup.NativeExpanderShearMachine
