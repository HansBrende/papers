import BitWord.NativeGateRun

/-! Thirteen fixed slots, each read from its own physical opcode and parameter
words. One common execution workspace is restored between calls. -/
namespace BitWord.NativeStages
open FixedTapeCompiler TransposeFollowup CopyMachine
open NativeExpanderShearFrames NativeBankCalls
set_option autoImplicit false
noncomputable section
abbrev DataPort (M : Transpose.TM) := NativeGate.Port M
abbrev Slot := Bool × Fin 13
abbrev Port (M : Transpose.TM) := DataPort M ⊕ Slot
abbrev Bank (M : Transpose.TM) := Port M → Tape Bool
def parameter (M : Transpose.TM) : DataPort M := .inl (NativeSuffixPowered.parameter M)
def opcode (M : Transpose.TM) : DataPort M := NativeGate.opcode M
@[simp] theorem parameter_ne_opcode (M : Transpose.TM) : parameter M≠opcode M := by
  simp [parameter,opcode,NativeGate.opcode]
@[simp] theorem opcode_ne_parameter (M : Transpose.TM) : opcode M≠parameter M :=
  Ne.symm (parameter_ne_opcode M)
def stagePorts (M : Transpose.TM) (i : Fin 13) (p : DataPort M) : Port M :=
  if p=parameter M then .inr (false,i) else if p=opcode M then .inr (true,i) else .inl p
def stageDecode (M : Transpose.TM) (i : Fin 13) : Port M → Option (DataPort M)
  | .inl p => if p=parameter M then none else if p=opcode M then none else some p
  | .inr (b,j) => if j=i then some (if b then opcode M else parameter M) else none

def stageBinding (M : Transpose.TM) (i : Fin 13) : FinitePortBinding (DataPort M) (Port M) where
  ports := ⟨stagePorts M i,by
    intro a b h
    by_cases ha : a=parameter M <;> by_cases hb : b=parameter M <;>
      by_cases hc : a=opcode M <;> by_cases hd : b=opcode M <;>
      simp_all [stagePorts]⟩
  decode := stageDecode M i
  decode_spec := by
    intro p j
    change stageDecode M i p=some j ↔ stagePorts M i j=p
    cases p with
    | inl p =>
      by_cases hp : p=parameter M <;> by_cases ho : p=opcode M <;>
        by_cases hj : j=parameter M <;> by_cases hk : j=opcode M <;>
        simp_all [stageDecode,stagePorts,eq_comm]
    | inr s =>
      rcases s with ⟨b,k⟩
      cases b <;> by_cases hi : k=i <;> by_cases hj : j=parameter M <;>
        by_cases hk : j=opcode M <;> simp_all [stageDecode,stagePorts,eq_comm]
inductive Label (M : Transpose.TM)
  | stage (i : Fin 13) (pc : NativeGate.Label M)
  | done
  deriving Fintype
noncomputable instance (M : Transpose.TM) : DecidableEq (Label M) := Classical.decEq _
def entry (M : Transpose.TM) (n : ℕ) : Label M :=
  if hn : n<13 then .stage ⟨n,hn⟩ (NativeGate.start M) else .done
def start (M : Transpose.TM) := entry M 0
def program (M : Transpose.TM) : Microcode.Program (Port M) (Label M)
  | .stage i .done => .jump (entry M (i.val+1))
  | .stage i pc => (stageBinding M i).instruction (Label.stage i) (NativeGate.program M pc)
  | .done => .halt
abbrev Trace (M : Transpose.TM) := OperationalTrace.Trace (NativeMicrocode.step (program M))
  (NativeMicrocode.Active (program M))
abbrev cfg (M : Transpose.TM) := workCfg (T:=Port M) (L:=Label M)
theorem stage_code (M : Transpose.TM) (i : Fin 13) (pc : NativeGate.Label M)
    (hh : NativeGate.program M pc≠.halt) (_ : NativeGate.program M pc≠.reject) :
    program M (.stage i pc)=MicrocodeEmbedding.instruction (stageBinding M i).ports
      (Label.stage i) (NativeGate.program M pc) := by
  cases pc <;> simp_all [program,NativeGate.program,FinitePortBinding.instruction_eq]

def bank (M : Transpose.TM) (raw fs : List Bool) (params codes : Fin 13 → List Bool) : Bank M :=
  Sum.elim (fun p => if p=parameter M ∨ p=opcode M then ⟨[],[]⟩ else NativeGate.bank M raw [] [] fs p)
    (fun s => Counter.marked (if s.1 then codes s.2 else params s.2))

theorem stage_projection (M : Transpose.TM) (i : Fin 13) (raw fs : List Bool)
    (params codes : Fin 13 → List Bool) :
    (fun p => bank M raw fs params codes ((stageBinding M i).ports p))=
      NativeGate.bank M raw (params i) (codes i) fs := by
  funext p
  change bank M raw fs params codes (stagePorts M i p)=_
  by_cases hp : p=parameter M
  · subst p; simp [stagePorts,bank,parameter,NativeGate.bank,NativeSuffixPowered.bank,
      NativeSuffixPowered.layout,NativeSuffixPowered.parameter]
  by_cases ho : p=opcode M
  · subst p; simp [stagePorts,bank,opcode,parameter,NativeGate.opcode,NativeGate.bank]
  simp only [stagePorts,hp,ho,ite_false,bank,Sum.elim_inl,or_self]
  cases p with
  | inr p => fin_cases p <;> simp_all [opcode,NativeGate.opcode,NativeGate.bank,parameter,NativeSuffixPowered.parameter]
  | inl p => cases p with
    | inr p => fin_cases p <;> simp_all [parameter,NativeSuffixPowered.parameter,NativeGate.bank,
        NativeSuffixPowered.bank,NativeSuffixPowered.layout]
    | inl p => rfl

theorem stage_values (M : Transpose.TM) (i : Fin 13) (raw out fs : List Bool)
    (params codes : Fin 13 → List Bool) :
    (stageBinding M i).values (NativeGate.bank M out (params i) (codes i) fs)
      (bank M raw fs params codes)=bank M out fs params codes := by
  funext p
  cases p with
  | inr s =>
    rcases s with ⟨b,j⟩
    cases b <;> by_cases hj : j=i <;>
      simp_all [FinitePortBinding.values,stageBinding,stageDecode,bank,opcode,parameter,
        NativeGate.bank,NativeGate.opcode,NativeSuffixPowered.bank,NativeSuffixPowered.layout,
        NativeSuffixPowered.parameter]
  | inl p =>
    by_cases hp : p=parameter M
    · subst p; simp [FinitePortBinding.values,stageBinding,stageDecode,bank,parameter,
        NativeGate.bank,NativeSuffixPowered.bank,NativeSuffixPowered.layout,NativeSuffixPowered.parameter]
    by_cases ho : p=opcode M
    · subst p; simp [FinitePortBinding.values,stageBinding,stageDecode,bank,opcode,NativeGate.opcode,NativeGate.bank]
    simp only [FinitePortBinding.values,stageBinding,stageDecode,hp,ho,ite_false,bank,Sum.elim_inl,or_self]
    cases p with
    | inr p => fin_cases p <;> simp_all [opcode,NativeGate.opcode,NativeGate.bank,parameter,NativeSuffixPowered.parameter]
    | inl p => cases p with
      | inr p => fin_cases p <;> simp_all [parameter,NativeSuffixPowered.parameter,NativeGate.bank,
          NativeSuffixPowered.bank,NativeSuffixPowered.layout]
      | inl p => rfl
end
end BitWord.NativeStages
