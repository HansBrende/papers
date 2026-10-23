import TransposeFollowup.NativeExpanderShearMetadata
import TransposeFollowup.NativeExpanderShearPrepare
import TransposeFollowup.NativeMatchingXorData
import TransposeFollowup.NativeExpanderShearSemantics
import TransposeFollowup.NativeExpanderShearFrames

/-! Fixed wiring of the raw loader, matching preparation, and complete data
executor. Tape and control types depend only on the fixed rational family. -/
namespace TransposeFollowup.NativeExpanderShearMachine
open FixedTapeCompiler CopyMachine
open NativeExpanderShearFrames
set_option autoImplicit false
variable {r q : ℕ}

inductive Port (q : ℕ)
  | metadata (p : NativeExpanderShearMetadata.Port)
  | prep (p : NativeExpanderShearPrepare.Port q)
  | target
  deriving DecidableEq, Fintype
abbrev Bank (q : ℕ) := Port q → Tape Bool

def metaBinding : FinitePortBinding NativeExpanderShearMetadata.Port (Port q) where
  ports := ⟨Port.metadata,by intro a b h; cases h; rfl⟩
  decode := fun p => match p with | .metadata p => some p | _ => none
  decode_spec := by
    intro p t
    change _ ↔ Port.metadata t=p
    cases p <;> simp [eq_comm]

def preparePort : NativeExpanderShearPrepare.Port q → Port q
  | .inl .source => .metadata .dimension
  | .inr .half => .metadata (.generator (.enumeration .source))
  | .inr .opcode => .metadata (.generator VertexScheduler.outputPort)
  | p => .prep p

def prepareBinding : FinitePortBinding (NativeExpanderShearPrepare.Port q) (Port q) where
  ports := ⟨preparePort,by
    intro a b h
    have hne : (RawEnumeration.Port.enumeration .source)≠VertexScheduler.outputPort := by decide +kernel
    cases a <;> cases b <;> rename_i a b <;> cases a <;> cases b <;>
      simp_all [preparePort]⟩
  decode := fun p => match p with
    | .metadata .dimension => some (.inl .source)
    | .metadata (.generator p) => if p=(.enumeration .source) then some (.inr .half)
        else if p=VertexScheduler.outputPort then some (.inr .opcode) else none
    | .prep p => match p with
        | .inl .source => none | .inr .half => none | .inr .opcode => none
        | p => some p
    | .target => none
  decode_spec := by
    intro p t
    change _ ↔ preparePort t=p
    cases p with
    | target => cases t <;> rename_i t <;> cases t <;> simp [preparePort]
    | prep p =>
      cases p <;> cases t <;> rename_i p t <;> cases p <;> cases t <;> simp [preparePort,eq_comm]
    | metadata p =>
      cases p with
      | dimension => cases t <;> rename_i t <;> cases t <;> simp [preparePort]
      | generator p =>
        have hne : (RawEnumeration.Port.enumeration .source)≠VertexScheduler.outputPort := by decide +kernel
        by_cases hps : p=RawEnumeration.Port.enumeration .source
        · subst p; cases t <;> rename_i t <;> cases t <;> simp [preparePort,hne,Ne.symm hne]
        · by_cases hpo : p=VertexScheduler.outputPort
          · subst p; cases t <;> rename_i t <;> cases t <;> simp [preparePort,hps,hne]
          · cases t <;> rename_i t <;> cases t <;> simp [preparePort,hps,hpo,eq_comm]

def dataPort : NativeMatchingXorPages.Port q → Port q
  | .source => .metadata (.generator .payload)
  | .target => .target
  | .tagA p => .prep (.inr (.tag false p))
  | .tagB p => .prep (.inr (.tag true p))
def dataBinding : FinitePortBinding (NativeMatchingXorPages.Port q) (Port q) where
  ports := ⟨dataPort,by intro a b h; cases a <;> cases b <;> simp_all [dataPort]⟩
  decode := fun p => match p with
    | .metadata (.generator .payload) => some .source
    | .target => some .target
    | .prep (.inr (.tag false p)) => some (.tagA p)
    | .prep (.inr (.tag true p)) => some (.tagB p)
    | _ => none
  decode_spec := by
    intro p t
    change _ ↔ dataPort t=p
    cases p with
    | target => cases t <;> simp [dataPort]
    | metadata p => cases p with
      | dimension => cases t <;> simp [dataPort]
      | generator p => cases p <;> cases t <;> simp [dataPort]
    | prep p => cases p with
      | inl p => cases t <;> simp [dataPort]
      | inr p => cases p with
        | tag side j => cases side <;> cases t <;> simp [dataPort,eq_comm]
        | _ => cases t <;> simp [dataPort]

inductive Label (F : Fin (r+1) → RationalMobius)
  | metadata (pc : NativeExpanderShearMetadata.Label F)
  | prep (pc : NativeExpanderShearPrepare.Label (rationalPageCount F))
  | data (pc : NativeMatchingXorData.Label (rationalPageCount F))
  deriving DecidableEq, Fintype

def pivot (F : Fin (r+1) → RationalMobius) : Fin (rationalPageCount F) :=
  ⟨0,by unfold rationalPageCount; positivity⟩
def start (F : Fin (r+1) → RationalMobius) : Label F := .metadata (NativeExpanderShearMetadata.start F)

def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program (Port (rationalPageCount F)) (Label F)
  | .metadata (.generate (.schedule .done)) => .work (.jump (.prep NativeExpanderShearPrepare.start))
  | .metadata pc => NativeIOEmbedding.boundInstruction metaBinding Label.metadata (NativeExpanderShearMetadata.program F pc)
  | .prep .done => .work (.jump (.data (NativeMatchingXorData.start (rationalPageCount F))))
  | .prep pc => .work (prepareBinding.instruction Label.prep (NativeExpanderShearPrepare.program (pivot F) pc))
  | .data pc => NativeIOEmbedding.boundInstruction dataBinding Label.data (NativeMatchingXorData.program (pivot F) pc)

theorem meta_code (F : Fin (r+1) → RationalMobius) (pc : NativeExpanderShearMetadata.Label F)
    (hh : NativeExpanderShearMetadata.program F pc≠.work .halt)
    (_ : NativeExpanderShearMetadata.program F pc≠.work .reject) :
    program F (.metadata pc)=NativeIOEmbedding.instruction metaBinding.ports Label.metadata (NativeExpanderShearMetadata.program F pc) := by
  cases pc with
  | load pc => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | generate pc => cases pc with
    | prepare pc => simp only [program,NativeIOEmbedding.bound_instruction_eq]
    | schedule pc => cases pc with
      | done => exact False.elim (hh rfl)
      | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem prepare_code (F : Fin (r+1) → RationalMobius) (pc : NativeExpanderShearPrepare.Label (rationalPageCount F))
    (hh : NativeExpanderShearPrepare.program (pivot F) pc≠.halt)
    (_ : NativeExpanderShearPrepare.program (pivot F) pc≠.reject) :
    NativeIO.workProgram (program F) (.prep pc)=MicrocodeEmbedding.instruction prepareBinding.ports Label.prep
      (NativeExpanderShearPrepare.program (pivot F) pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

theorem data_code (F : Fin (r+1) → RationalMobius) (pc : NativeMatchingXorData.Label (rationalPageCount F))
    (_ : NativeMatchingXorData.program (pivot F) pc≠.work .halt)
    (_ : NativeMatchingXorData.program (pivot F) pc≠.work .reject) :
    program F (.data pc)=NativeIOEmbedding.instruction dataBinding.ports Label.data (NativeMatchingXorData.program (pivot F) pc) := by
  exact NativeIOEmbedding.bound_instruction_eq _ _ _

def blank : Bank q := fun _ => ⟨[],[]⟩
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

end TransposeFollowup.NativeExpanderShearMachine
