import TransposeFollowup.NormalizedBatchBudget
import TransposeFollowup.FamilyReaderRun

/-! A finite controller normalizes every map batch to the same field width.
The map index is finite control; dimension and record count remain on tape. -/
namespace TransposeFollowup.FamilyNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def common (F : Fin c → RationalMobius) : ℕ := Finset.univ.sup (fun i => PaddedWord.commonConstant (F i))
theorem le_common (F : Fin c → RationalMobius) (i : Fin c) : PaddedWord.commonConstant (F i)≤common F :=
  Finset.le_sup (f:=fun i => PaddedWord.commonConstant (F i)) (Finset.mem_univ i)
def padding (F : Fin c → RationalMobius) (i : Fin c) := common F-PaddedWord.commonConstant (F i)
def records (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) := RowEnumeration.rowsRecords (F i) xs (Counter.value xs) 0
def inputBatch (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) := NormalizedBatch.inputBatch (records F xs i)
def outputBatch (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) := NormalizedBatch.outputBatch (padding F i) (records F xs i)

inductive Label (F : Fin c → RationalMobius)
  | phase (i : Fin c) (pc : NormalizedBatch.Label (PaddedWord.commonConstant (F i)) (padding F i))
  | done
  deriving DecidableEq,Fintype

def identityBinding : FinitePortBinding (Fin 6) (Fin 6) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p j;simp [eq_comm]
def entry (F : Fin c → RationalMobius) (k : ℕ) : Label F :=
  if h : k<c then .phase ⟨k,h⟩ (NormalizedBatch.start (PaddedWord.commonConstant (F ⟨k,h⟩)) (padding F ⟨k,h⟩)) else .done
def program (F : Fin c → RationalMobius) : Microcode.Program (Fin 6) (Label F)
  | .phase i .done => .jump (entry F (i.val+1))
  | .phase i pc => identityBinding.instruction (Label.phase i) (NormalizedBatch.program (PaddedWord.commonConstant (F i)) (padding F i) pc)
  | .done => .halt

theorem phase_code (F : Fin c → RationalMobius) (i : Fin c)
    (pc : NormalizedBatch.Label (PaddedWord.commonConstant (F i)) (padding F i))
    (hh : NormalizedBatch.program (PaddedWord.commonConstant (F i)) (padding F i) pc≠.halt)
    (_ : NormalizedBatch.program (PaddedWord.commonConstant (F i)) (padding F i) pc≠.reject) :
    program F (.phase i pc)=MicrocodeEmbedding.instruction identityBinding.ports (Label.phase i)
      (NormalizedBatch.program (PaddedWord.commonConstant (F i)) (padding F i) pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg {F : Fin c → RationalMobius} (pc : Label F) (s : NormalizedBatch.Bank) (pos : Fin 6 → ℤ) : NativeMicrocode.Config (Fin 6) (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
abbrev Trace (F : Fin c → RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem embed_phase (F : Fin c → RationalMobius) (i : Fin c)
    (pc : NormalizedBatch.Label (PaddedWord.commonConstant (F i)) (padding F i))
    (s : NormalizedBatch.Bank) (pos : Fin 6 → ℤ) (frame : MicrocodeEmbedding.Frame (Fin 6)) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.phase i) (NormalizedBatch.cfg pc s pos) frame=cfg (.phase i pc) s pos := by
  unfold MicrocodeEmbedding.embed NormalizedBatch.cfg cfg
  simp only [← identityBinding.values_eq_extend]
  rfl

def unitCoefficient (F : Fin c → RationalMobius) := 74*common F+648

theorem phase_call (F : Fin c → RationalMobius) (i : Fin c) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ unitCoefficient F*Transpose.inputLength (Counter.value xs),Trace F t
      (cfg (.phase i (NormalizedBatch.start (PaddedWord.commonConstant (F i)) (padding F i)))
        (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch F xs i++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg (.phase i .done) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch F xs i).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(outputBatch F xs i).reverse++out,[]⟩) (NormalizedBatch.advance pos (inputBatch F xs i).length (outputBatch F xs i).length)) := by
  have hp : 0<2*xs.length+PaddedWord.commonConstant (F i) := by
    simpa only [PaddedWord.word_length] using RowEnumeration.common_positive (F i) xs
  have hw := RowEnumeration.rows_records_width (F i) xs (Counter.value xs) 0
  simp only [PaddedWord.word_length] at hw
  obtain ⟨t,ht,htr⟩ := NormalizedBatch.batch_trace (PaddedWord.commonConstant (F i)) (padding F i) xs hp (records F xs i) hw pre suffix out pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports (Label.phase i)
    (NormalizedBatch.program (PaddedWord.commonConstant (F i)) (padding F i)) (program F)
    (NormalizedBatch.frame (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch F xs i++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
    (phase_code F i) htr
  refine ⟨t,ht.trans (NormalizedBatch.map_linear_budget (F i) (common F) (le_common F i) xs hn hx),?_⟩
  simpa only [embed_phase,inputBatch,outputBatch] using he

theorem phase_trace (F : Fin c → RationalMobius) (i : Fin c) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ unitCoefficient F*Transpose.inputLength (Counter.value xs)+1,Trace F t
      (cfg (entry F i.val) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputBatch F xs i++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg (entry F (i.val+1)) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputBatch F xs i).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(outputBatch F xs i).reverse++out,[]⟩) (NormalizedBatch.advance pos (inputBatch F xs i).length (outputBatch F xs i).length)) := by
  obtain ⟨t,ht,htr⟩ := phase_call F i xs hn hx pre suffix out pos
  have hi : entry F i.val=.phase i (NormalizedBatch.start (PaddedWord.commonConstant (F i)) (padding F i)) := by
    simp only [entry,dite_eq_left i.isLt]
  rw [hi]
  refine ⟨t+1,by omega,NativeCountedLoop.trace_trans htr ?_⟩
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,program]
  · exact .refl _

end TransposeFollowup.FamilyNormalization


namespace TransposeFollowup.FamilyNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def segments (V : Fin c → List (Sym Bool)) : ℕ → ℕ → List (Sym Bool)
  | _,0 => []
  | k,q+1 => if h : k<c then V ⟨k,h⟩++segments V (k+1) q else []

theorem segments_ofFn (V : Fin c → List (Sym Bool)) (q k : ℕ) (hk : k+q≤c) :
    segments V k q=(List.ofFn (fun j : Fin q => V ⟨k+j.val,by omega⟩)).flatten := by
  induction q generalizing k with
  | zero => simp [segments]
  | succ q ih =>
    have hkc : k<c := by omega
    simp only [segments,hkc,↓reduceDIte,List.ofFn_succ,List.flatten_cons]
    rw [ih (k+1) (by omega)]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext j
    congr 2
    simp only [Fin.val_succ]
    omega

def inputStream (F : Fin c → RationalMobius) (xs : List Bool) := segments (inputBatch F xs) 0 c
def outputStream (F : Fin c → RationalMobius) (xs : List Bool) := segments (outputBatch F xs) 0 c

theorem input_batch_eq (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) :
    inputBatch F xs i=FamilyEnumeration.batch (F i) xs := by
  simp only [inputBatch,NormalizedBatch.inputBatch,NormalizedBatch.inputBits,records,FamilyEnumeration.batch,RowEnumeration.rows_encoding]

theorem input_stream_eq {r : ℕ} (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    inputStream F xs=FamilyEnumeration.stream F xs := by
  rw [inputStream,segments_ofFn _ _ _ (by omega),FamilyEnumeration.stream_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simpa only [Nat.zero_add] using input_batch_eq F xs i

theorem rest_trace (F : Fin c → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (q k : ℕ) (hk : k+q=c) (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ q*(unitCoefficient F*Transpose.inputLength (Counter.value xs)+1),Trace F t
      (cfg (entry F k) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,segments (inputBatch F xs) k q++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg .done (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(segments (inputBatch F xs) k q).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(segments (outputBatch F xs) k q).reverse++out,[]⟩)
        (NormalizedBatch.advance pos (segments (inputBatch F xs) k q).length (segments (outputBatch F xs) k q).length)) := by
  induction q generalizing k pre out pos with
  | zero =>
    have he : k=c := by omega
    subst k
    refine ⟨0,by simp,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,segments,List.nil_append,List.reverse_nil,List.length_nil,NormalizedBatch.advance_zero]
    exact .refl _
  | succ q ih =>
    have hkc : k<c := by omega
    let i : Fin c := ⟨k,hkc⟩
    obtain ⟨a,ha,ta⟩ := phase_trace F i xs hn hx pre (segments (inputBatch F xs) (k+1) q++suffix) out pos
    obtain ⟨b,hb,tb⟩ := ih (k+1) (by omega) ((inputBatch F xs i).reverse++pre) ((outputBatch F xs i).reverse++out)
      (NormalizedBatch.advance pos (inputBatch F xs i).length (outputBatch F xs i).length)
    refine ⟨a+b,?_,?_⟩
    · rw [Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [segments,hkc,↓reduceDIte,List.append_assoc,List.reverse_append,NormalizedBatch.advance_add,List.length_append]
        using NativeCountedLoop.trace_trans ta tb

def coefficient (F : Fin c → RationalMobius) := c*(unitCoefficient F+1)

theorem complete_trace (F : Fin c → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) :
    ∃ t ≤ coefficient F*Transpose.inputLength (Counter.value xs),Trace F t
      (cfg (entry F 0) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputStream F xs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos)
      (cfg .done (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputStream F xs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
        ⟨(outputStream F xs).reverse++out,[]⟩) (NormalizedBatch.advance pos (inputStream F xs).length (outputStream F xs).length)) := by
  obtain ⟨t,ht,htr⟩ := rest_trace F xs hn hx c 0 (by omega) pre suffix out pos
  have hL : 1≤Transpose.inputLength (Counter.value xs) := hn.trans (DimensionCandidate.dimension_le_length _ hn)
  refine ⟨t,ht.trans ?_,htr⟩
  unfold coefficient
  calc
    _ ≤ c*((unitCoefficient F+1)*Transpose.inputLength (Counter.value xs)) := Nat.mul_le_mul_left c (by nlinarith)
    _ = _ := by ring

end TransposeFollowup.FamilyNormalization


namespace TransposeFollowup.FamilyNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

noncomputable def nativeEncoding (F : Fin c → RationalMobius) := NativeMicrocode.initialEncoding (T:=Fin 6) (entry F 0)
noncomputable def nativeMachine (F : Fin c → RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

def labelEquiv (F : Fin c → RationalMobius) : Label F ≃ (Σ i : Fin c,NormalizedBatch.Label (PaddedWord.commonConstant (F i)) (padding F i)) ⊕ Unit where
  toFun | .phase i pc => .inl ⟨i,pc⟩ | .done => .inr ()
  invFun | .inl ⟨i,pc⟩ => .phase i pc | .inr _ => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨i,pc⟩|⟨⟩) <;> rfl

theorem batch_label_card (small pad : ℕ) : Fintype.card (NormalizedBatch.Label small pad)=small+2*pad+197 := by
  have h:=(NormalizedBatch.fixed_resources small pad).2.2.1
  change Fintype.card (NormalizedBatch.Label small pad)-1+1=_ at h
  have hp : 0<Fintype.card (NormalizedBatch.Label small pad) := Fintype.card_pos_iff.mpr ⟨.done⟩
  omega

theorem fixed_resources (F : Fin c → RationalMobius) : (nativeMachine F).k=6 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1+∑ i : Fin c,(PaddedWord.commonConstant (F i)+2*padding F i+197) ∧
    (nativeEncoding F).label (entry F 0)=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F)-1+1=_
  rw [Fintype.card_congr (labelEquiv F)]
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_unit,batch_label_card]
  omega

theorem native_complete (F : Fin c → RationalMobius) (xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Fin 6 → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ coefficient F*Transpose.inputLength (Counter.value xs),
      Transpose.stepN (nativeMachine F) input t
        ((cfg (entry F 0) (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,inputStream F xs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩) pos).denote
          (nativeEncoding F) (program F) ip outRev)=
        some ((cfg .done (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputStream F xs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
          ⟨(outputStream F xs).reverse++out,[]⟩) (NormalizedBatch.advance pos (inputStream F xs).length (outputStream F xs).length)).denote
          (nativeEncoding F) (program F) ip outRev) ∧
      Transpose.step (nativeMachine F) input ((cfg .done (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨(inputStream F xs).reverse++pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩
          ⟨(outputStream F xs).reverse++out,[]⟩) (NormalizedBatch.advance pos (inputStream F xs).length (outputStream F xs).length)).denote
          (nativeEncoding F) (program F) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F xs hn hx pre suffix out pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

def normalizedRecords (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) :=
  NormalizedBatch.normalizedRecords (padding F i) (records F xs i)

theorem output_encoding (F : Fin c → RationalMobius) (xs : List Bool) :
    outputStream F xs=(List.ofFn (fun i : Fin c => symbols ((normalizedRecords F xs i).flatMap (fun p => p.1++p.2))++[.stop])).flatten := by
  rw [outputStream,segments_ofFn _ _ _ (by omega)]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [outputBatch,NormalizedBatch.outputBatch,NormalizedBatch.output_encoding,NormalizedBatch.inputBits,normalizedRecords,Nat.zero_add]

theorem normalized_values (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) :
    (normalizedRecords F xs i).map RowEnumeration.decodePair=(records F xs i).map RowEnumeration.decodePair := by
  change (NormalizedBatch.normalizedRecords (padding F i) (records F xs i)).map (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2))=
    (records F xs i).map (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2))
  simpa only [NativeCounter.word_value] using
    NormalizedBatch.values_preserved (padding F i) (records F xs i)

theorem normalized_width (F : Fin c → RationalMobius) (xs : List Bool) (i : Fin c) :
    ∀ p ∈ normalizedRecords F xs i,p.1.length=2*xs.length+common F ∧ p.2.length=2*xs.length+common F := by
  apply NormalizedBatch.normalized_width _ _ (le_common F i) xs (records F xs i)
  simpa only [PaddedWord.word_length,records] using RowEnumeration.rows_records_width (F i) xs (Counter.value xs) 0

end TransposeFollowup.FamilyNormalization


/-! Raw input, family generation, rewind, and common-width normalization
share forty-two work tapes. The original raw stream remains stored. -/
namespace TransposeFollowup.RawNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

abbrev Port := RawEnumeration.Port
abbrev Bank := RawEnumeration.Bank
abbrev rawOutput := FamilyReader.output
def output : Port := RawEnumeration.sharedPort .grid
def normPort : Fin 6 → Port :=
  ![.enumeration .source,RawEnumeration.sharedPort .dimension,rawOutput,
    RawEnumeration.sharedPort .index,RawEnumeration.sharedPort .zero,output]
def normBinding : FinitePortBinding (Fin 6) Port where
  ports:=⟨normPort,by decide +kernel⟩
  decode:=fun p => if p=normPort 0 then some 0 else if p=normPort 1 then some 1 else if p=normPort 2 then some 2 else
    if p=normPort 3 then some 3 else if p=normPort 4 then some 4 else if p=normPort 5 then some 5 else none
  decode_spec:=by decide +kernel

inductive Label (F : Fin (r+1) → RationalMobius)
  | generate (pc : FamilyReader.Label F)
  | normalize (pc : FamilyNormalization.Label F)
  deriving DecidableEq,Fintype

def start (F : Fin (r+1) → RationalMobius) : Label F := .generate (FamilyReader.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .generate (.rewind .done) => .work (.jump (.normalize (FamilyNormalization.entry F 0)))
  | .generate pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.generate (FamilyReader.program F pc)
  | .normalize pc => .work (normBinding.instruction Label.normalize (FamilyNormalization.program F pc))

theorem generate_code (F : Fin (r+1) → RationalMobius) (pc : FamilyReader.Label F)
    (hh : FamilyReader.program F pc≠.work .halt) (_ : FamilyReader.program F pc≠.work .reject) :
    program F (.generate pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.generate (FamilyReader.program F pc) := by
  cases pc with
  | rewind pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem normalize_code (F : Fin (r+1) → RationalMobius) (pc : FamilyNormalization.Label F)
    (_ : FamilyNormalization.program F pc≠.halt) (_ : FamilyNormalization.program F pc≠.reject) :
    NativeIO.workProgram (program F) (.normalize pc)=MicrocodeEmbedding.instruction normBinding.ports Label.normalize (FamilyNormalization.program F pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def liftBank (w : List Bool) (s : NormalizedBatch.Bank) : Bank := normBinding.values s (RawEnumeration.loaded w [] [])
def bank (w xs : List Bool) (raw out : Tape Bool) : Bank :=
  liftBank w (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ raw ⟨[],[]⟩ ⟨[],[]⟩ out)
def advance (pos : Port → ℤ) (read written : ℕ) : Port → ℤ :=
  fun p => pos p+(if p=rawOutput then (read : ℤ) else 0)+(if p=output then (written : ℤ) else 0)
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem bank_ready (w xs : List Bool) (syms : List (Sym Bool)) :
    bank w xs ⟨[],syms⟩ ⟨[],[]⟩=FamilyReader.readBank w xs syms := by
  funext p;fin_cases p <;> rfl

theorem embed_generate (F : Fin (r+1) → RationalMobius) (pc : FamilyReader.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F)) (FamilyReader.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.generate pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed FamilyReader.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed FamilyReader.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem embed_normalize (F : Fin (r+1) → RationalMobius) (pc : FamilyNormalization.Label F)
    (w : List Bool) (s base : NormalizedBatch.Bank) (rpos : Fin 6 → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed normBinding.ports (Label.normalize (F:=F)) (FamilyNormalization.cfg pc s rpos)
      (RawEnumeration.frame (liftBank w base) pos)=workCfg (.normalize pc) (liftBank w s) (normBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed FamilyNormalization.cfg workCfg RawEnumeration.frame
  simp only [← normBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem norm_positions (pos : Port → ℤ) : normBinding.values (fun p => pos (normPort p)) pos=pos := by
  funext p;fin_cases p <;> rfl

theorem norm_final_positions (pos : Port → ℤ) (a b : ℕ) :
    normBinding.values (NormalizedBatch.advance (fun p => pos (normPort p)) a b) pos=advance pos a b := by
  funext p
  rw [normBinding.values_eq_extend]
  by_cases hp : ∃ q,normBinding.ports q=p
  · obtain ⟨q,rfl⟩:=hp
    rw [MicrocodeEmbedding.extend_at]
    have hr : normBinding.ports q=rawOutput ↔ q=2 := by
      change normBinding.ports q=normBinding.ports (2 : Fin 6) ↔ q=2
      exact normBinding.ports.injective.eq_iff
    have ho : normBinding.ports q=output ↔ q=5 := by
      change normBinding.ports q=normBinding.ports (5 : Fin 6) ↔ q=5
      exact normBinding.ports.injective.eq_iff
    simp only [NormalizedBatch.advance,advance,hr,ho]
    rfl
  · rw [MicrocodeEmbedding.extend_outside _ _ hp]
    have hr : p≠rawOutput := by intro h;exact hp ⟨2,h.symm⟩
    have ho : p≠output := by intro h;exact hp ⟨5,h.symm⟩
    simp [advance,hr,ho]

end TransposeFollowup.RawNormalization


namespace TransposeFollowup.RawNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem generate_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ FamilyReader.coefficient F*w.length,Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.generate (.rewind .done)) (bank w xs ⟨[],FamilyEnumeration.stream F xs⟩ ⟨[],[]⟩) pos w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := FamilyReader.complete_trace F w n hn hw pos outRev
  have he := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F))
    (FamilyReader.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (generate_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_generate,bank_ready,start] using he⟩

theorem normalize_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ FamilyNormalization.coefficient F*Transpose.inputLength (Counter.value xs),Trace F w t
      (cfg (.normalize (FamilyNormalization.entry F 0)) (bank w xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨out,[]⟩) pos ip outRev)
      (cfg (.normalize .done) (bank w xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩
        ⟨(FamilyNormalization.outputStream F xs).reverse++out,[]⟩)
        (advance pos (FamilyNormalization.inputStream F xs).length (FamilyNormalization.outputStream F xs).length) ip outRev) := by
  obtain ⟨t,ht,htr⟩ := FamilyNormalization.complete_trace F xs hn hx pre suffix out (fun p => pos (normPort p))
  have he := MicrocodeEmbedding.trace_embed normBinding.ports (Label.normalize (F:=F)) (FamilyNormalization.program F)
    (NativeIO.workProgram (program F))
    (RawEnumeration.frame (liftBank w (NormalizedBatch.bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩ ⟨out,[]⟩)) pos)
    (normalize_code F) htr
  simp only [embed_normalize,norm_positions,norm_final_positions] at he
  exact ⟨t,ht,by simpa only [cfg,bank] using NativeIO.lift_work_trace (program F) w ip outRev he⟩

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.generate (.rewind .done)) s pos ip outRev) (cfg (.normalize (FamilyNormalization.entry F 0)) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.RawNormalization


namespace TransposeFollowup.RawNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := FamilyReader.coefficient F+FamilyNormalization.coefficient F+1

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.normalize .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
        (advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩ := generate_call F w n hn hw pos outRev
  have hnx : 1≤Counter.value xs := by omega
  have hxs : xs.length≤(Counter.value xs+1).size := by rw [hl,hv];exact Nat.size_le_size (Nat.le_succ n)
  obtain ⟨b,hb,tb⟩ := normalize_call F w xs hnx hxs [] [] [] pos w.length outRev
  simp only [List.append_nil,FamilyNormalization.input_stream_eq] at tb
  rw [hv,← hw] at hb
  have tj:=transfer_trace F w (bank w xs ⟨[],FamilyEnumeration.stream F xs⟩ ⟨[],[]⟩) pos w.length outRev
  have hL : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨xs,hx,hv,hl,a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb⟩
  unfold coefficient
  nlinarith

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.normalize .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
          (advance (fun _ => 0) (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length []).denote
          (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.normalize .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
          (advance (fun _ => 0) (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length []).denote
          (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw (fun _ => 0) []
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hi : (cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) := by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,FamilyNormalization.program]

theorem native_call {U J : Type*} {k q : ℕ} (F : Fin (r+1) → RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label F → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.work .halt → program F pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program F pc))
    (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg (start F) (RawEnumeration.initial []) pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels
          (cfg (.normalize .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
            (advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev)
          outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ FamilyReader.Label F ⊕ FamilyNormalization.Label F where
  toFun | .generate pc => .inl pc | .normalize pc => .inr pc
  invFun | .inl pc => .generate pc | .inr pc => .normalize pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1448+(∑ i : Fin (r+1),FamilyEnumeration.seedStates (F i))+
      (∑ i : Fin (r+1),(PaddedWord.commonConstant (F i)+2*FamilyNormalization.padding F i+197)) ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum]
    have hr:=(FamilyReader.fixed_resources F).2.2.1
    change Fintype.card (FamilyReader.Label F)-1+1=_ at hr
    have hp : 0<Fintype.card (FamilyReader.Label F) := Fintype.card_pos_iff.mpr ⟨FamilyReader.start F⟩
    have hn':=(FamilyNormalization.fixed_resources F).2.2.1
    change Fintype.card (FamilyNormalization.Label F)-1+1=_ at hn'
    have hq : 0<Fintype.card (FamilyNormalization.Label F) := Fintype.card_pos_iff.mpr ⟨.done⟩
    omega

end TransposeFollowup.RawNormalization


namespace TransposeFollowup.RawNormalization
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem bank_payload (w xs : List Bool) (raw out : Tape Bool) : bank w xs raw out .payload=Counter.marked w := rfl
theorem bank_source (w xs : List Bool) (raw out : Tape Bool) : bank w xs raw out (.enumeration .source)=Counter.marked xs := rfl
theorem bank_raw (w xs : List Bool) (raw out : Tape Bool) : bank w xs raw out rawOutput=raw := rfl
theorem bank_output (w xs : List Bool) (raw out : Tape Bool) : bank w xs raw out output=out := rfl
theorem bank_other (w xs : List Bool) (raw out : Tape Bool) (p : Port)
    (hp : p≠.payload) (hs : p≠.enumeration .source) (hr : p≠rawOutput) (ho : p≠output) : bank w xs raw out p=⟨[],[]⟩ := by
  fin_cases p <;> first | rfl | exact False.elim (hp rfl) | exact False.elim (hs rfl) | exact False.elim (hr rfl) | exact False.elim (ho rfl)

theorem normalized_records_spec (F : Fin (r+1) → RationalMobius) (xs : List Bool) (i : Fin (r+1)) (p : ℕ × ℕ) :
    p ∈ (FamilyNormalization.normalizedRecords F xs i).map RowEnumeration.decodePair ↔
      ∃ u v : Fin (Counter.value xs),v ∈ (F i).neighbors u ∧ p=(u.val,v.val) := by
  rw [FamilyNormalization.normalized_values]
  exact RowEnumeration.all_records_spec (F i) xs p

theorem normalized_records_nodup (F : Fin (r+1) → RationalMobius) (xs : List Bool) (i : Fin (r+1)) :
    ((FamilyNormalization.normalizedRecords F xs i).map RowEnumeration.decodePair).Nodup := by
  rw [FamilyNormalization.normalized_values]
  exact RowEnumeration.rows_values_nodup (F i) xs (Counter.value xs) 0 (by omega)

theorem output_nonblank (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    ∀ s ∈ FamilyNormalization.outputStream F xs,s≠.blank := by
  rw [FamilyNormalization.output_encoding]
  intro s hs
  obtain ⟨b,hb,hs⟩:=List.mem_flatten.mp hs
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hb
  simp only [List.mem_append,List.mem_singleton] at hs
  rcases hs with hs | rfl
  · obtain ⟨bit,_,rfl⟩:=List.mem_map.mp hs
    simp
  · simp

theorem output_ne_raw : output≠rawOutput := by decide +kernel

theorem output_length_le_time (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (t : ℕ)
    (pos : Port → ℤ) (outRev : List Bool)
    (h : Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.normalize .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
        (advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev)) :
    (FamilyNormalization.outputStream F xs).length≤t := by
  have hp:=(NativeHeadDisplacement.trace_bounds (program F) w h output).2
  simp only [cfg,workCfg,advance,output_ne_raw,ite_false,ite_true,add_zero] at hp
  omega

end TransposeFollowup.RawNormalization
