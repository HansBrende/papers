import TransposeFollowup.PortBindingFrame
import TransposeFollowup.RecordedRowResources
import TransposeFollowup.SeedMultipleMeaning
import TransposeFollowup.RawDimensionLoader
import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeHeadDisplacement

/-! Reuse the same forty tapes for every row. The row index itself is the
loop counter: a physical comparator tests it against the preserved dimension.
At completion, a paid erase/copy restores index zero for reuse. -/
namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
open RecordedRow (Port Bank)
set_option autoImplicit false

def indexPort : Port := RecordedRow.consumerPort .rowIndex
def dimensionPort : Port := .row (.prep (.images (.source (.shared .dimension))))
def zeroPort : Port := RecordedRow.consumerPort .zero

def identityBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p q; simp [eq_comm]

def singleBinding : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => indexPort,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=indexPort then some 0 else none
  decode_spec := by decide +kernel

def compareBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![indexPort,dimensionPort],by decide +kernel⟩
  decode := fun p => if p=indexPort then some 0 else if p=dimensionPort then some 1 else none
  decode_spec := by decide +kernel

def resetBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![zeroPort,indexPort],by decide +kernel⟩
  decode := fun p => if p=zeroPort then some 0 else if p=indexPort then some 1 else none
  decode_spec := by decide +kernel

def addPort : RepeatedAdd.Port → Port
  | .acc => indexPort
  | .factor => RecordedRow.consumerPort .unit
  | .fuel => RecordedRow.consumerPort .fuel
  | .scratch => RecordedRow.consumerPort .scratch
  | .zero => zeroPort

def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort,by decide +kernel⟩
  decode := fun p => match p with
    | .row (.prep (.images (.source (.shared .index)))) => some .acc
    | .row (.prep (.images (.source (.shared .unit)))) => some .factor
    | .row (.prep (.images (.source (.shared .fuel)))) => some .fuel
    | .row (.prep (.images (.source (.shared .scratch)))) => some .scratch
    | .row (.prep (.images (.source (.shared .zero)))) => some .zero
    | _ => none
  decode_spec := by decide +kernel

inductive Label (F : RationalMobius)
  | compare (pc : BinaryCompare.Label)
  | row (pc : RecordedRow.Label F)
  | increment (pc : RepeatedAdd.Label)
  | erase (pc : NativeErase.Label)
  | reset (pc : NativeMappedCopy.Label)
  | done | reject
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F := .compare (.scan .equal)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .compare (.done .less) => .jump (.row (RecordedRow.start F))
  | .compare (.done .equal) => .jump (.erase 2)
  | .compare (.done .greater) => .reject
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .row (.done _) => .jump (.increment (.counter 0))
  | .row pc => identityBinding.instruction Label.row (RecordedRow.program F pc)
  | .increment pc => if pc=.counter 12 then .jump (start F)
      else addBinding.instruction Label.increment (RepeatedAdd.program pc)
  | .erase pc => if pc=0 then .jump (.reset (.init (.erase 0)))
      else singleBinding.instruction Label.erase (NativeErase.program pc)
  | .reset pc => if pc=.seal .done then .jump .done
      else resetBinding.instruction Label.reset (NativeMappedCopy.program id pc)
  | .done => .halt
  | .reject => .reject

theorem compare_code (F : RationalMobius) (pc : BinaryCompare.Label)
    (hh : BinaryCompare.program pc≠.halt) (_ : BinaryCompare.program pc≠.reject) :
    program F (.compare pc)=MicrocodeEmbedding.instruction compareBinding.ports Label.compare (BinaryCompare.program pc) := by
  cases pc with
  | done r => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem row_code (F : RationalMobius) (pc : RecordedRow.Label F)
    (hh : RecordedRow.program F pc≠.halt) (_ : RecordedRow.program F pc≠.reject) :
    program F (.row pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.row (RecordedRow.program F pc) := by
  cases pc <;> try exact identityBinding.instruction_eq _ _
  exact False.elim (hh rfl)

theorem increment_code (F : RationalMobius) (pc : RepeatedAdd.Label)
    (hh : RepeatedAdd.program pc≠.halt) (_ : RepeatedAdd.program pc≠.reject) :
    program F (.increment pc)=MicrocodeEmbedding.instruction addBinding.ports Label.increment (RepeatedAdd.program pc) := by
  have h : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem erase_code (F : RationalMobius) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program F (.erase pc)=MicrocodeEmbedding.instruction singleBinding.ports Label.erase (NativeErase.program pc) := by
  have h : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem reset_code (F : RationalMobius) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt) (_ : NativeMappedCopy.program id pc≠.reject) :
    program F (.reset pc)=MicrocodeEmbedding.instruction resetBinding.ports Label.reset (NativeMappedCopy.program id pc) := by
  have h : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

abbrev Trace (F : RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

end TransposeFollowup.RowEnumeration


namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
open RecordedRow (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def indexBank (n : List Bool) (pre : List (Sym Bool)) (w : Tape Bool) : Bank :=
  Function.update (RecordedRow.initial n [] pre) indexPort w

theorem indexBank_marked (n iw : List Bool) (pre : List (Sym Bool)) :
    indexBank n pre (Counter.marked iw)=RecordedRow.initial n iw pre := by
  funext p; fin_cases p <;> rfl

theorem embed_compare (F : RationalMobius) (pc : BinaryCompare.Label) (n iw : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports (Label.compare (F:=F))
      (BinaryCompare.cfg pc (BinaryCompare.marked iw) (BinaryCompare.marked n)
        (fun t => pos (compareBinding.ports t))).denote (frame (RecordedRow.initial n iw pre) pos)=
      cfg (.compare pc) (RecordedRow.initial n iw pre) pos := by
  unfold MicrocodeEmbedding.embed BinaryCompare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← compareBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_increment (F : RationalMobius) (pc : RepeatedAdd.Label) (n iw base : List Bool)
    (hm : 0<n.length) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports (Label.increment (F:=F))
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] iw (ArithmeticSeed.one n.length))
        (fun p => pos (addPort p))) (frame (RecordedRow.initial n base pre) pos)=
      cfg (.increment pc) (RecordedRow.initial n iw pre) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p
  all_goals simp only [addBinding,addPort,FinitePortBinding.values,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
    RecordedRow.initial,RecordedRow.liftBank,RowExecution.initial,RowExecution.prepBank,
    RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
    SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
    ArithmeticSeed.one_length _ hm,ArithmeticSeed.zeros]
  all_goals rfl

theorem embed_row (F : RationalMobius) (pc : RecordedRow.Label F) (s base : Bank)
    (pos basePos : Port → ℤ) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.row (F:=F)) (RecordedRow.cfg pc s pos)
      (frame base basePos)=cfg (.row pc) s pos := by
  unfold MicrocodeEmbedding.embed RecordedRow.cfg cfg frame
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem embed_erase (F : RationalMobius) (pc : NativeErase.Label) (n : List Bool)
    (pre : List (Sym Bool)) (w : Tape Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed singleBinding.ports (Label.erase (F:=F))
      (NativeErase.cfg pc w (fun _ => pos indexPort)).denote (frame (RecordedRow.initial n [] pre) pos)=
      cfg (.erase pc) (indexBank n pre w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← singleBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_reset (F : RationalMobius) (pc : NativeMappedCopy.Label) (n : List Bool)
    (pre : List (Sym Bool)) (w : Tape Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed resetBinding.ports (Label.reset (F:=F))
      (NativeMappedCopy.cfg pc (Counter.marked (ArithmeticSeed.zeros n.length)) w
        (fun t => pos (resetBinding.ports t))) (frame (RecordedRow.initial n [] pre) pos)=
      cfg (.reset pc) (indexBank n pre w) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← resetBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem compare_call (F : RationalMobius) (n iw : List Bool) (hl : iw.length=n.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 5*n.length+6, Trace F t (cfg (start F) (RecordedRow.initial n iw pre) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (Counter.value iw) (Counter.value n))))
        (RecordedRow.initial n iw pre) pos) := by
  obtain ⟨t,ht,htr⟩ := BinaryCompare.comparison_trace iw n hl (fun j => pos (compareBinding.ports j))
  have he := MicrocodeEmbedding.trace_embed compareBinding.ports (Label.compare (F:=F))
    BinaryCompare.program (program F) (frame (RecordedRow.initial n iw pre) pos) (compare_code F) htr
  refine ⟨t,by simpa only [hl] using ht,?_⟩
  simpa only [embed_compare,start,NativeCounter.word_value] using he

theorem increment_call (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length) (hl : iw.length=n.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 18*n.length+51, Trace F t
      (cfg (.increment (.counter 0)) (RecordedRow.initial n iw pre) pos)
      (cfg (.increment (.counter 12))
        (RecordedRow.initial n (RepeatedAdd.addWord iw (ArithmeticSeed.one n.length)) pre) pos) := by
  have hu := ArithmeticSeed.one_length n.length hm
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace iw (ArithmeticSeed.one n.length) (hl.trans hu.symm)
    (fun p => pos (addPort p))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports (Label.increment (F:=F))
    RepeatedAdd.program (program F) (frame (RecordedRow.initial n iw pre) pos) (increment_code F) htr
  exact ⟨t,by simpa only [hu] using ht,by simpa only [embed_increment F _ _ _ _ hm] using he⟩

theorem row_call (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ RecordedRow.budget F n (F.denseRow i), Trace F t
      (cfg (.row (RecordedRow.start F)) (RecordedRow.initial n iw pre) pos)
      (cfg (.row (.done (RowStream.rowGuard F i)))
        (RecordedRow.initial n iw ((symbols (RecordedRow.records n iw (F.denseRow i))).reverse++pre))
        (RecordedRow.finalPositions pos (RecordedRow.records n iw (F.denseRow i)))) := by
  obtain ⟨t,ht,htr⟩ := RecordedRow.rational_trace F source i iw hl hv pre pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports (Label.row (F:=F))
    (RecordedRow.program F) (program F) (frame (RecordedRow.initial (PaddedWord.word (PaddedWord.commonConstant F) id source) iw pre) pos) (row_code F) htr
  exact ⟨t,ht,by simpa only [embed_row] using he⟩

theorem erase_call (F : RationalMobius) (n iw : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 4*iw.length+4, Trace F t (cfg (.erase 2) (RecordedRow.initial n iw pre) pos)
      (cfg (.erase 0) (indexBank n pre ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace iw (fun _ => pos indexPort)
  have he := MicrocodeEmbedding.trace_embed singleBinding.ports (Label.erase (F:=F))
    NativeErase.program (program F) (frame (RecordedRow.initial n [] pre) pos) (erase_code F) htr
  exact ⟨t,ht,by simpa only [embed_erase,indexBank_marked] using he⟩

theorem reset_call (F : RationalMobius) (n : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 6*n.length+14, Trace F t (cfg (.reset (.init (.erase 0))) (indexBank n pre ⟨[],[]⟩) pos)
      (cfg (.reset (.seal .done)) (RecordedRow.initial n (ArithmeticSeed.zeros n.length) pre) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id (ArithmeticSeed.zeros n.length)
    (fun j => pos (resetBinding.ports j))
  have he := MicrocodeEmbedding.trace_embed resetBinding.ports (Label.reset (F:=F))
    (NativeMappedCopy.program id) (program F) (frame (RecordedRow.initial n [] pre) pos) (reset_code F) htr
  refine ⟨t,by simpa only [ArithmeticSeed.zeros,List.length_replicate] using ht,?_⟩
  simpa only [List.map_id,embed_reset,indexBank_marked] using he

theorem finish_trace (F : RationalMobius) (n iw : List Bool) (hl : iw.length=n.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 10*n.length+21, Trace F t
      (cfg (.compare (.done .equal)) (RecordedRow.initial n iw pre) pos)
      (cfg .done (RecordedRow.initial n (ArithmeticSeed.zeros n.length) pre) pos) := by
  have j0 := jump_trace F (.compare (.done .equal)) (.erase 2) (RecordedRow.initial n iw pre) pos rfl
  obtain ⟨a,ha,ta⟩ := erase_call F n iw pre pos
  have ja := jump_trace F (.erase 0) (.reset (.init (.erase 0))) (indexBank n pre ⟨[],[]⟩) pos rfl
  obtain ⟨b,hb,tb⟩ := reset_call F n pre pos
  have jb := jump_trace F (.reset (.seal .done)) .done (RecordedRow.initial n (ArithmeticSeed.zeros n.length) pre) pos rfl
  exact ⟨1+a+1+b+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans j0 ta) ja) tb) jb⟩

end TransposeFollowup.RowEnumeration


/-! Exact index words for the physical row loop. The recursive lists below
specify outputs; machine costs and transitions are proved separately. -/
namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def indexWord (n : List Bool) : ℕ → List Bool
  | 0 => ArithmeticSeed.zeros n.length
  | i+1 => RepeatedAdd.addWord (indexWord n i) (ArithmeticSeed.one n.length)

theorem index_length (n : List Bool) (hm : 0<n.length) (i : ℕ) :
    (indexWord n i).length=n.length := by
  induction i with
  | zero => simp [indexWord,ArithmeticSeed.zeros]
  | succ i ih =>
    exact (RepeatedAdd.addWord_length _ _ (ih.trans (ArithmeticSeed.one_length _ hm).symm)).trans
      (ArithmeticSeed.one_length _ hm)

theorem index_value (n : List Bool) (hm : 0<n.length) (i : ℕ) (hi : i<2^n.length) :
    Counter.value (indexWord n i)=i := by
  induction i with
  | zero => simp [indexWord,ArithmeticSeed.zeros,PaddedWord.value_zeroes]
  | succ i ih =>
    have hv := ih (by omega)
    rw [indexWord,NativeCounter.word_value,RepeatedAdd.addWord_value _ _
      ((index_length n hm i).trans (ArithmeticSeed.one_length _ hm).symm)]
    rw [← NativeCounter.word_value,← NativeCounter.word_value,hv,ArithmeticSeed.one_value,
      ArithmeticSeed.one_length _ hm,Nat.mod_eq_of_lt hi]

def rowBits (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  RecordedRow.records n (indexWord n i.val) (F.denseRow i)

def rowsFrom (F : RationalMobius) (source : List Bool) : ℕ → ℕ → List Bool
  | 0,_ => []
  | r+1,i => if hi : i<Counter.value source then rowBits F source ⟨i,hi⟩++rowsFrom F source r (i+1) else []

def rowAllowance (F : RationalMobius) (n : List Bool) :=
  RecordedRow.budget F n (List.replicate (Counter.value n) true)

def allowance (F : RationalMobius) (n : List Bool) (r : ℕ) :=
  r*(rowAllowance F n+23*n.length+60)+15*n.length+27

theorem row_budget_le (F : RationalMobius) (n flags : List Bool) (hf : flags.length=Counter.value n) :
    RecordedRow.budget F n flags ≤ rowAllowance F n := by
  have hc := List.count_le_length (l:=flags) (a:=true)
  have hb : (true==true)=true := rfl
  unfold rowAllowance RecordedRow.budget RowConsumer.budget
  simp only [List.length_replicate,List.count_replicate,hb,ite_true,hf] at *
  nlinarith

end TransposeFollowup.RowEnumeration


namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
open RecordedRow (Port Bank)
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem common_positive (F : RationalMobius) (source : List Bool) :
    0<(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  rw [PaddedWord.word_length]
  unfold PaddedWord.commonConstant
  omega

theorem index_source (F : RationalMobius) (source : List Bool) (i : ℕ) (hi : i ≤ Counter.value source) :
    Counter.value (indexWord (PaddedWord.word (PaddedWord.commonConstant F) id source) i)=i :=
  index_value _ (common_positive F source) i (hi.trans_lt (RowConsumer.common_index_fit F source))

theorem output_positions_nil (pos : Port → ℤ) : RecordedRow.finalPositions pos []=pos := by
  funext p; cases p <;> simp [RecordedRow.finalPositions]

theorem output_positions_append (pos : Port → ℤ) (a b : List Bool) :
    RecordedRow.finalPositions (RecordedRow.finalPositions pos a) b=RecordedRow.finalPositions pos (a++b) := by
  funext p
  cases p <;> simp [RecordedRow.finalPositions]
  ring

theorem body_trace (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ rowAllowance F n+23*n.length+60, Trace F t
      (cfg (start F) (RecordedRow.initial n (indexWord n i.val) pre) pos)
      (cfg (start F) (RecordedRow.initial n (indexWord n (i.val+1)) ((symbols (rowBits F source i)).reverse++pre))
        (RecordedRow.finalPositions pos (rowBits F source i))) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  let iw := indexWord n i.val
  have hm : 0<n.length := common_positive F source
  have hl : iw.length=n.length := index_length n hm i.val
  have hv : Counter.value iw=i.val := index_source F source i.val i.isLt.le
  have hn : Counter.value n=Counter.value source := PaddedWord.common_value F source
  let bits := rowBits F source i
  let outpre := (symbols bits).reverse++pre
  let outpos := RecordedRow.finalPositions pos bits
  obtain ⟨a,ha,ta⟩ := compare_call F n iw hl pre pos
  have ta' : Trace F a (cfg (start F) (RecordedRow.initial n iw pre) pos)
      (cfg (.compare (.done .less)) (RecordedRow.initial n iw pre) pos) := by
    simpa only [hv,hn,BinaryCompare.numeric,i.isLt,ite_true] using ta
  have ja := jump_trace F (.compare (.done .less)) (.row (RecordedRow.start F)) (RecordedRow.initial n iw pre) pos rfl
  obtain ⟨b,hb,tb⟩ := row_call F source i iw hl hv pre pos
  have jrow := jump_trace F (.row (.done (RowStream.rowGuard F i))) (.increment (.counter 0))
    (RecordedRow.initial n iw outpre) outpos rfl
  obtain ⟨c,hc,tc⟩ := increment_call F n iw hm hl outpre outpos
  have jc := jump_trace F (.increment (.counter 12)) (start F)
    (RecordedRow.initial n (RepeatedAdd.addWord iw (ArithmeticSeed.one n.length)) outpre) outpos rfl
  have hbound := row_budget_le F n (F.denseRow i) ((F.denseRow_length i).trans hn.symm)
  have hb' : b ≤ rowAllowance F n := hb.trans hbound
  refine ⟨a+1+b+1+c+1,?_,?_⟩
  · change a+1+b+1+c+1 ≤ rowAllowance F n+23*n.length+60
    omega
  exact trace_trans (trace_trans (trace_trans (trace_trans (trace_trans ta' ja) tb) jrow) tc) jc

theorem terminal_trace (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ 15*n.length+27, Trace F t
      (cfg (start F) (RecordedRow.initial n (indexWord n (Counter.value source)) pre) pos)
      (cfg .done (RecordedRow.initial n (indexWord n 0) pre) pos) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  let iw := indexWord n (Counter.value source)
  have hm : 0<n.length := common_positive F source
  have hl : iw.length=n.length := index_length n hm _
  have hv : Counter.value iw=Counter.value source := index_source F source _ le_rfl
  have hn : Counter.value n=Counter.value source := PaddedWord.common_value F source
  obtain ⟨a,ha,ta⟩ := compare_call F n iw hl pre pos
  have ta' : Trace F a (cfg (start F) (RecordedRow.initial n iw pre) pos)
      (cfg (.compare (.done .equal)) (RecordedRow.initial n iw pre) pos) := by
    simpa only [hv,hn,BinaryCompare.numeric,Nat.lt_irrefl,ite_false] using ta
  obtain ⟨b,hb,tb⟩ := finish_trace F n iw hl pre pos
  refine ⟨a+b,?_,trace_trans ta' tb⟩
  change a+b ≤ 15*n.length+27
  omega

theorem loop_trace (F : RationalMobius) (source : List Bool) (r i : ℕ)
    (hi : i+r=Counter.value source) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ allowance F n r, Trace F t
      (cfg (start F) (RecordedRow.initial n (indexWord n i) pre) pos)
      (cfg .done (RecordedRow.initial n (indexWord n 0) ((symbols (rowsFrom F source r i)).reverse++pre))
        (RecordedRow.finalPositions pos (rowsFrom F source r i))) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  induction r generalizing i pre pos with
  | zero =>
    have he : i=Counter.value source := by omega
    subst i
    simpa only [allowance,Nat.zero_mul,Nat.zero_add,rowsFrom,symbols,List.map_nil,List.reverse_nil,
      List.nil_append,output_positions_nil] using terminal_trace F source pre pos
  | succ r ih =>
    have hlt : i<Counter.value source := by omega
    let j : Fin (Counter.value source) := ⟨i,hlt⟩
    obtain ⟨a,ha,ta⟩ := body_trace F source j pre pos
    obtain ⟨b,hb,tb⟩ := ih (i+1) (by omega) ((symbols (rowBits F source j)).reverse++pre)
      (RecordedRow.finalPositions pos (rowBits F source j))
    refine ⟨a+b,?_,?_⟩
    · change a+b ≤ allowance F n (r+1)
      change a ≤ rowAllowance F n+23*n.length+60 at ha
      change b ≤ allowance F n r at hb
      unfold allowance at *
      nlinarith
    · have whole := trace_trans ta tb
      simpa only [rowsFrom,hlt,↓reduceDIte,output_positions_append,symbols,List.map_append,List.reverse_append,List.append_assoc] using whole

theorem complete_trace (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ allowance F n (Counter.value source), Trace F t
      (cfg (start F) (RecordedRow.initial n (indexWord n 0) pre) pos)
      (cfg .done (RecordedRow.initial n (indexWord n 0)
        ((symbols (rowsFrom F source (Counter.value source) 0)).reverse++pre))
        (RecordedRow.finalPositions pos (rowsFrom F source (Counter.value source) 0))) :=
  loop_trace F source (Counter.value source) 0 (by omega) pre pos

end TransposeFollowup.RowEnumeration


namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
open RecordedRow (Port Bank)
set_option autoImplicit false

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

theorem native_all_rows (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ allowance F n (Counter.value source),
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (RecordedRow.initial n (indexWord n 0) pre) pos).denote
          (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg .done (RecordedRow.initial n (indexWord n 0)
          ((symbols (rowsFrom F source (Counter.value source) 0)).reverse++pre))
          (RecordedRow.finalPositions pos (rowsFrom F source (Counter.value source) 0))).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg .done (RecordedRow.initial n (indexWord n 0)
          ((symbols (rowsFrom F source (Counter.value source) 0)).reverse++pre))
          (RecordedRow.finalPositions pos (rowsFrom F source (Counter.value source) 0))).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (source : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    ∃ t ≤ allowance F n (Counter.value source),
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (RecordedRow.initial n (indexWord n 0) pre) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (RecordedRow.initial n (indexWord n 0)
            ((symbols (rowsFrom F source (Counter.value source) 0)).reverse++pre))
            (RecordedRow.finalPositions pos (rowsFrom F source (Counter.value source) 0))) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

def labelEquiv (F : RationalMobius) : Label F ≃
    BinaryCompare.Label ⊕ RecordedRow.Label F ⊕ RepeatedAdd.Label ⊕ NativeErase.Label ⊕ NativeMappedCopy.Label ⊕ Bool where
  toFun := fun
    | .compare pc => .inl pc | .row pc => .inr (.inl pc)
    | .increment pc => .inr (.inr (.inl pc)) | .erase pc => .inr (.inr (.inr (.inl pc)))
    | .reset pc => .inr (.inr (.inr (.inr (.inl pc))))
    | .done => .inr (.inr (.inr (.inr (.inr false))))
    | .reject => .inr (.inr (.inr (.inr (.inr true))))
  invFun := fun
    | .inl pc => .compare pc | .inr (.inl pc) => .row pc
    | .inr (.inr (.inl pc)) => .increment pc | .inr (.inr (.inr (.inl pc))) => .erase pc
    | .inr (.inr (.inr (.inr (.inl pc)))) => .reset pc
    | .inr (.inr (.inr (.inr (.inr false)))) => .done
    | .inr (.inr (.inr (.inr (.inr true)))) => .reject
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by
    rintro (pc | pc | pc | pc | pc | b)
    all_goals try rfl
    cases b <;> rfl

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=40 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+12566 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=40
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hr := (RecordedRow.fixed_resources F).2.2.1
    change Fintype.card (RecordedRow.Label F)-1+1=_ at hr
    have hp : 0<Fintype.card (RecordedRow.Label F) := Fintype.card_pos_iff.mpr ⟨RecordedRow.start F⟩
    have ha : Fintype.card RepeatedAdd.Label=99 := by decide +kernel
    have hb : Fintype.card BinaryCompare.Label=28 := by decide +kernel
    have he : Fintype.card NativeErase.Label=8 := by decide +kernel
    have hc : Fintype.card NativeMappedCopy.Label=24 := by decide +kernel
    simp only [Fintype.card_sum,Fintype.card_bool,ha,hb,he,hc]
    omega

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1 ≤ N) (hv : Counter.value source=N) (hl : source.length ≤ (N+1).size) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    allowance F (PaddedWord.word (PaddedWord.commonConstant F) id source) N ≤
      ((1876+72*T)*(F.integerOperandConstant^2).size+23118+928*T)*Transpose.inputLength N := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hn : Counter.value n=N := (PaddedWord.common_value F source).trans hv
  have hr := RecordedRow.total_budget F N source (List.replicate (Counter.value n) true) hN hv hl
    (by simpa only [List.length_replicate] using hn)
  change N*rowAllowance F n ≤ _ at hr
  have hm : 38*n.length+87 ≤ (38*PaddedWord.commonConstant F+87)+76*(N+1).size := by
    dsimp [n]; rw [PaddedWord.word_length]; omega
  have hsmall : 15*n.length+27 ≤ N*(15*n.length+27) := Nat.le_mul_of_pos_left _ hN
  have hover : N*(23*n.length+60)+15*n.length+27 ≤ N*(N*(38*n.length+87)) := by
    calc
      _ ≤ N*(38*n.length+87) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hN)
  have hd := dense_scan_budget (38*PaddedWord.commonConstant F+87) 76 N hN
  have he : 2*(38*PaddedWord.commonConstant F+87+3*76)=76*(F.integerOperandConstant^2).size+934 := by
    unfold PaddedWord.commonConstant; ring
  have htotal : N*(23*n.length+60)+15*n.length+27 ≤
      (76*(F.integerOperandConstant^2).size+934)*Transpose.inputLength N := by
    calc
      _ ≤ N*(N*(38*n.length+87)) := hover
      _ ≤ N*(N*((38*PaddedWord.commonConstant F+87)+76*(N+1).size)) := by gcongr
      _ ≤ _ := by simpa only [he] using hd
  change allowance F n N ≤ _
  unfold allowance
  nlinarith

end TransposeFollowup.RowEnumeration


/-! Mathematical meaning of the entire generated index-pair stream. The
native output is the fixed-width encoding of exactly the directed neighbor
relation of the supplied rational map. Multi-map normalization is separate. -/
namespace TransposeFollowup.RowEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def rowRecords (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  RowConsumer.records (indexWord n i.val) (ArithmeticSeed.one n.length) (F.denseRow i)
    (RowConsumer.zeroWord (ArithmeticSeed.one n.length))

def decodePair (p : List Bool × List Bool) : ℕ × ℕ :=
  (BinaryCompare.value p.1,BinaryCompare.value p.2)

def rowsRecords (F : RationalMobius) (source : List Bool) : ℕ → ℕ → List (List Bool × List Bool)
  | 0,_ => []
  | r+1,i => if hi : i<Counter.value source then rowRecords F source ⟨i,hi⟩++rowsRecords F source r (i+1) else []

theorem rowBits_encoding (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :
    rowBits F source i=(rowRecords F source i).flatMap (fun p => p.1++p.2) := rfl

theorem rows_encoding (F : RationalMobius) (source : List Bool) (r i : ℕ) :
    rowsFrom F source r i=(rowsRecords F source r i).flatMap (fun p => p.1++p.2) := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    by_cases h : i<Counter.value source
    · simp only [rowsFrom,rowsRecords,h,↓reduceDIte,List.flatMap_append,← rowBits_encoding,ih]
    · simp only [rowsFrom,rowsRecords,h,↓reduceDIte,List.flatMap_nil]

theorem row_values (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :
    (rowRecords F source i).map decodePair=(RowConsumer.targets (F.denseRow i) 0).map (fun j => (i.val,j)) := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := common_positive F source
  have hu : BinaryCompare.value (ArithmeticSeed.one n.length)=1 := by
    rw [← NativeCounter.word_value]; exact ArithmeticSeed.one_value _
  have hi : BinaryCompare.value (indexWord n i.val)=i.val := by
    rw [← NativeCounter.word_value]; exact index_source F source i.val i.isLt.le
  have hf : Counter.value source<2^(ArithmeticSeed.one n.length).length := by
    rw [ArithmeticSeed.one_length _ hm]; exact RowConsumer.common_index_fit F source
  exact RowConsumer.dense_record_values F i _ _ hu hi hf

theorem row_records_spec (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) (p : ℕ × ℕ) :
    p ∈ (rowRecords F source i).map decodePair ↔
      ∃ j : Fin (Counter.value source), j ∈ F.neighbors i ∧ p=(i.val,j.val) := by
  rw [row_values]
  constructor
  · rintro h
    obtain ⟨j,hj,hp⟩ := List.mem_map.mp h
    have hb := (RowConsumer.targets_bounds (F.denseRow i) 0 j hj).2
    have hjn : j<Counter.value source := by simpa only [Nat.zero_add,F.denseRow_length] using hb
    exact ⟨⟨j,hjn⟩,(RowConsumer.dense_targets F i ⟨j,hjn⟩).mp hj,hp.symm⟩
  · rintro ⟨j,hj,rfl⟩
    exact List.mem_map.mpr ⟨j.val,(RowConsumer.dense_targets F i j).mpr hj,rfl⟩

theorem rows_records_spec (F : RationalMobius) (source : List Bool) (r i : ℕ)
    (hi : i+r ≤ Counter.value source) (p : ℕ × ℕ) :
    p ∈ (rowsRecords F source r i).map decodePair ↔
      ∃ u v : Fin (Counter.value source), i ≤ u.val ∧ u.val < i+r ∧ v ∈ F.neighbors u ∧ p=(u.val,v.val) := by
  induction r generalizing i with
  | zero =>
    constructor
    · simp [rowsRecords]
    · rintro ⟨u,v,hl,hr,_,_⟩; omega
  | succ r ih =>
    have hlt : i<Counter.value source := by omega
    let j : Fin (Counter.value source) := ⟨i,hlt⟩
    have ht := ih (i+1) (by omega)
    simp only [rowsRecords,hlt,↓reduceDIte,List.map_append,List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨v,hv,hp⟩ := (row_records_spec F source j p).mp h
        exact ⟨j,v,le_rfl,by dsimp [j];omega,hv,hp⟩
      · obtain ⟨u,v,hl,hr,hv,hp⟩ := ht.mp h
        exact ⟨u,v,by omega,by omega,hv,hp⟩
    · rintro ⟨u,v,hl,hr,hv,hp⟩
      by_cases he : u.val=i
      · left
        have hu : u=j := Fin.ext he
        subst u
        exact (row_records_spec F source j p).mpr ⟨v,hv,hp⟩
      · right
        exact ht.mpr ⟨u,v,by omega,by omega,hv,hp⟩

theorem all_records_spec (F : RationalMobius) (source : List Bool) (p : ℕ × ℕ) :
    p ∈ (rowsRecords F source (Counter.value source) 0).map decodePair ↔
      ∃ u v : Fin (Counter.value source), v ∈ F.neighbors u ∧ p=(u.val,v.val) := by
  rw [rows_records_spec F source _ _ (by omega)]
  constructor
  · rintro ⟨u,v,_,_,hv,hp⟩; exact ⟨u,v,hv,hp⟩
  · rintro ⟨u,v,hv,hp⟩; exact ⟨u,v,Nat.zero_le _,by simpa only [Nat.zero_add] using u.isLt,hv,hp⟩

theorem row_values_nodup (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :
    ((rowRecords F source i).map decodePair).Nodup := by
  rw [row_values]
  exact (RowConsumer.targets_nodup (F.denseRow i) 0).map (fun _ _ h => congrArg Prod.snd h)

theorem rows_values_nodup (F : RationalMobius) (source : List Bool) (r i : ℕ)
    (hi : i+r ≤ Counter.value source) : ((rowsRecords F source r i).map decodePair).Nodup := by
  induction r generalizing i with
  | zero => simp [rowsRecords]
  | succ r ih =>
    have hlt : i<Counter.value source := by omega
    let j : Fin (Counter.value source) := ⟨i,hlt⟩
    simp only [rowsRecords,hlt,↓reduceDIte,List.map_append,List.nodup_append]
    refine ⟨row_values_nodup F source j,ih (i+1) (by omega),?_⟩
    intro p hp q hq heq
    subst q
    obtain ⟨v,hv,he⟩ := (row_records_spec F source j p).mp hp
    obtain ⟨u,w,hl,hr,hw,he'⟩ := (rows_records_spec F source r (i+1) (by omega) p).mp hq
    have hvv := congrArg Prod.fst (he.symm.trans he')
    change i=u.val at hvv
    omega

theorem row_records_width (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source)) :
    let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
    ∀ p ∈ rowRecords F source i, p.1.length=m ∧ p.2.length=m := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := common_positive F source
  have hu := ArithmeticSeed.one_length n.length hm
  have h := RowConsumer.records_width (indexWord n i.val) (ArithmeticSeed.one n.length) (F.denseRow i)
    (RowConsumer.zeroWord (ArithmeticSeed.one n.length)) ((index_length n hm i.val).trans hu.symm)
    (by simp [RowConsumer.zeroWord])
  simpa only [rowRecords, hu] using h

theorem rows_records_width (F : RationalMobius) (source : List Bool) (r i : ℕ) :
    let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
    ∀ p ∈ rowsRecords F source r i, p.1.length=m ∧ p.2.length=m := by
  induction r generalizing i with
  | zero => simp [rowsRecords]
  | succ r ih =>
    by_cases h : i<Counter.value source
    · simp only [rowsRecords,h,↓reduceDIte,List.mem_append]
      intro p hp
      rcases hp with hp | hp
      · exact row_records_width F source ⟨i,h⟩ p hp
      · exact ih (i+1) p hp
    · simp [rowsRecords,h]

end TransposeFollowup.RowEnumeration


/-! A marked dimension word is the only arithmetic input. This caller
prepares the row bank, emits the map's complete neighbor relation, and
physically clears all seed and work tapes before returning. -/
namespace TransposeFollowup.SeededEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | rows (p : RecordedRow.Port) | source
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def rowsBinding : FinitePortBinding RecordedRow.Port Port where
  ports := ⟨Port.rows,fun _ _ h => Port.rows.inj h⟩
  decode := fun p => match p with | .rows q => some q | .source => none
  decode_spec := by
    intro p q
    change (match p with | .rows r => some r | .source => none)=some q ↔ Port.rows q=p
    cases p <;> simp [eq_comm]

def tempPort : Port := .rows (.row (.prep .temp))
def scratchPort : Port := .rows (RecordedRow.consumerPort .scratch)

def seedPort : ArithmeticSeed.Port → Port
  | .source => .source
  | .number => .rows RowEnumeration.dimensionPort
  | .zeroA => .rows RowEnumeration.indexPort
  | .zeroB => .rows RowEnumeration.zeroPort
  | .one => .rows (RecordedRow.consumerPort .unit)
  | .fuel => .rows (RecordedRow.consumerPort .fuel)
  | .left => scratchPort
  | .right => tempPort

def seedBinding : FinitePortBinding ArithmeticSeed.Port Port where
  ports := ⟨seedPort,by decide +kernel⟩
  decode := fun p => match p with
    | .source => some .source
    | .rows (.row (.prep (.images (.source (.shared .dimension))))) => some .number
    | .rows (.row (.prep (.images (.source (.shared .index))))) => some .zeroA
    | .rows (.row (.prep (.images (.source (.shared .zero))))) => some .zeroB
    | .rows (.row (.prep (.images (.source (.shared .unit))))) => some .one
    | .rows (.row (.prep (.images (.source (.shared .fuel))))) => some .fuel
    | .rows (.row (.prep (.images (.source (.shared .scratch))))) => some .left
    | .rows (.row (.prep .temp)) => some .right
    | _ => none
  decode_spec := by decide +kernel

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun q => if q=p then some 0 else none
  decode_spec := by
    intro q j
    change (if q=p then some (0 : Fin 1) else none)=some j ↔ p=q
    fin_cases j
    simp [eq_comm]

def seedWords : Fin 5 ↪ Port :=
  ⟨![seedPort .number,seedPort .zeroA,seedPort .zeroB,seedPort .one,seedPort .fuel],by decide +kernel⟩

def identityBinding : FinitePortBinding Port Port where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p q; simp [eq_comm]

inductive Label (F : RationalMobius)
  | seed (pc : ArithmeticSeed.Label (PaddedWord.commonConstant F))
  | clear (last : Bool) (pc : NativeUnprepare.Label)
  | rows (pc : RowEnumeration.Label F)
  | erase (pc : NativeBatchErase.Label 5)
  | done
  deriving DecidableEq, Fintype

def clearPort (last : Bool) : Port := if last then scratchPort else tempPort

def start (F : RationalMobius) : Label F := .seed (.pad false (.init (.erase 0)))

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .seed .done => .jump (.clear false 0)
  | .seed pc => seedBinding.instruction Label.seed (ArithmeticSeed.program (PaddedWord.commonConstant F) pc)
  | .clear last pc => if pc=2 then .jump (if last then .done else .rows (RowEnumeration.start F))
      else (singleBinding (clearPort last)).instruction (Label.clear last) (NativeUnprepare.program pc)
  | .rows .done => .jump (.erase (NativeBatchErase.entry 5 0))
  | .rows pc => rowsBinding.instruction Label.rows (RowEnumeration.program F pc)
  | .erase .done => .jump (.clear true 0)
  | .erase pc => identityBinding.instruction Label.erase (NativeBatchErase.program seedWords pc)
  | .done => .halt

theorem seed_code (F : RationalMobius) (pc : ArithmeticSeed.Label (PaddedWord.commonConstant F))
    (hh : ArithmeticSeed.program (PaddedWord.commonConstant F) pc≠.halt)
    (_ : ArithmeticSeed.program (PaddedWord.commonConstant F) pc≠.reject) :
    program F (.seed pc)=MicrocodeEmbedding.instruction seedBinding.ports Label.seed
      (ArithmeticSeed.program (PaddedWord.commonConstant F) pc) := by
  cases pc <;> try exact seedBinding.instruction_eq _ _
  exact False.elim (hh rfl)

theorem clear_code (F : RationalMobius) (last : Bool) (pc : NativeUnprepare.Label)
    (hh : NativeUnprepare.program pc≠.halt) (_ : NativeUnprepare.program pc≠.reject) :
    program F (.clear last pc)=MicrocodeEmbedding.instruction (singleBinding (clearPort last)).ports
      (Label.clear last) (NativeUnprepare.program pc) := by
  have h : pc≠2 := by intro h; subst pc; exact hh rfl
  simp only [program,h,ite_false,FinitePortBinding.instruction_eq]

theorem rows_code (F : RationalMobius) (pc : RowEnumeration.Label F)
    (hh : RowEnumeration.program F pc≠.halt) (_ : RowEnumeration.program F pc≠.reject) :
    program F (.rows pc)=MicrocodeEmbedding.instruction rowsBinding.ports Label.rows (RowEnumeration.program F pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem erase_code (F : RationalMobius) (pc : NativeBatchErase.Label 5)
    (hh : NativeBatchErase.program seedWords pc≠.halt) (_ : NativeBatchErase.program seedWords pc≠.reject) :
    program F (.erase pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.erase (NativeBatchErase.program seedWords pc) := by
  cases pc <;> try exact identityBinding.instruction_eq _ _
  exact False.elim (hh rfl)

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

def initial (source : List Bool) (pre : List (Sym Bool)) : Bank
  | .source => Counter.marked source
  | .rows .output => ⟨pre,[]⟩
  | _ => ⟨[],[]⟩

def liftRows (source : List Bool) (s : RecordedRow.Bank) : Bank
  | .source => Counter.marked source | .rows p => s p

def prepared (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) : Bank :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  liftRows source (RecordedRow.initial n (RowEnumeration.indexWord n 0) pre)

def seeded (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) : Bank :=
  seedBinding.values (ArithmeticSeed.ready (PaddedWord.commonConstant F) source).tapes (initial source pre)

def finalPositions (pos : Port → ℤ) (bits : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.rows .output then (bits.length : ℤ) else 0

def words (F : RationalMobius) (source : List Bool) : Fin 5 → List Bool :=
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  ![n,ArithmeticSeed.zeros n.length,ArithmeticSeed.zeros n.length,ArithmeticSeed.one n.length,[true]]

abbrev Trace (F : RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

end TransposeFollowup.SeededEnumeration


namespace TransposeFollowup.SeededEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem initial_seed (source : List Bool) (pre : List (Sym Bool)) :
    seedBinding.values (ArithmeticSeed.initial source).tapes (initial source pre)=initial source pre := by
  funext p; fin_cases p <;> rfl

theorem prepared_seed (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) :
    Function.update (seeded F source pre) tempPort ⟨[],[]⟩=prepared F source pre := by
  funext p
  fin_cases p <;>
    simp only [seeded,prepared,liftRows,initial,seedBinding,FinitePortBinding.values,tempPort,
      ArithmeticSeed.ready,ArithmeticSeed.Bank.tapes,RowEnumeration.indexWord,
      RecordedRow.initial,RecordedRow.liftBank,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      PaddedWord.word_length,Function.update] <;> rfl

theorem seeded_temp (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) :
    seeded F source pre tempPort=BinaryCarry.preparedOutput := rfl

theorem prepared_words (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) (j : Fin 5) :
    prepared F source pre (seedWords j)=Counter.marked (words F source j) := by
  fin_cases j <;> rfl

theorem prepared_erased (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) :
    NativeBatchErase.stage seedWords (prepared F source pre) 5=
      Function.update (initial source pre) scratchPort BinaryCarry.preparedOutput := by
  funext p
  fin_cases p <;>
    dsimp only [Port.proxyTypeEquiv,RecordedRow.Port.proxyTypeEquiv,RowExecution.Port.proxyTypeEquiv,
      RowPreparation.Port.proxyTypeEquiv,SourceImages.Port.proxyTypeEquiv,SourceEndpoints.Port.proxyTypeEquiv,
      EndpointClip.Port.proxyTypeEquiv] <;>
    simp only [NativeBatchErase.stage,Fin.exists_fin_succ,Fin.exists_fin_zero,seedWords,
      Fin.val_zero,Fin.val_succ] <;>
    simp [prepared,liftRows,initial,scratchPort,seedPort,RecordedRow.consumerPort,
      RowEnumeration.dimensionPort,RowEnumeration.indexPort,RowEnumeration.zeroPort,
      RecordedRow.initial,RecordedRow.liftBank,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      Function.update]

theorem seed_positions (pos : Port → ℤ) :
    seedBinding.values (fun p => pos (seedPort p)) pos=pos := by
  funext p; fin_cases p <;> rfl

theorem rows_positions (pos : Port → ℤ) :
    rowsBinding.values (fun p => pos (.rows p)) pos=pos := by
  funext p; cases p <;> rfl

theorem rows_final_positions (pos : Port → ℤ) (bits : List Bool) :
    rowsBinding.values (RecordedRow.finalPositions (fun p => pos (.rows p)) bits) pos=finalPositions pos bits := by
  funext p
  cases p with
  | source => simp [rowsBinding,FinitePortBinding.values,finalPositions]
  | rows p => cases p <;> simp [rowsBinding,FinitePortBinding.values,RecordedRow.finalPositions,finalPositions]

theorem embed_seed (F : RationalMobius) (pc : ArithmeticSeed.Label (PaddedWord.commonConstant F))
    (s : ArithmeticSeed.Bank) (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed seedBinding.ports (Label.seed (F:=F))
      (ArithmeticSeed.cfg pc s (fun p => pos (seedPort p))) (frame base pos)=
      cfg (.seed pc) (seedBinding.values s.tapes base) pos := by
  exact seedBinding.embed_bank_project _ _ _ _ _

theorem embed_rows (F : RationalMobius) (pc : RowEnumeration.Label F) (s base : RecordedRow.Bank)
    (source : List Bool) (rpos : RecordedRow.Port → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed rowsBinding.ports (Label.rows (F:=F)) (RowEnumeration.cfg pc s rpos)
      (frame (liftRows source base) pos)=cfg (.rows pc) (liftRows source s) (rowsBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed RowEnumeration.cfg cfg frame
  simp only [← rowsBinding.values_eq_extend]
  congr 2
  funext p; cases p <;> rfl

theorem embed_clear (F : RationalMobius) (last : Bool) (pc : NativeUnprepare.Label)
    (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding (clearPort last)).ports (Label.clear (F:=F) last)
      (NativeUnprepare.cfg pc w (fun _ => pos (clearPort last))).denote (frame s pos)=
      cfg (.clear last pc) (Function.update s (clearPort last) w) pos := by
  unfold MicrocodeEmbedding.embed NativeUnprepare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (singleBinding (clearPort last)).values_eq_extend]
  congr 2 <;> funext p <;> by_cases h : p=clearPort last
  all_goals simp [singleBinding,FinitePortBinding.values,Function.update,h]

theorem embed_erase (F : RationalMobius) (pc : NativeBatchErase.Label 5) (s base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed identityBinding.ports (Label.erase (F:=F))
      (NativeBatchErase.cfg pc s pos) (frame base pos)=cfg (.erase pc) s pos := by
  unfold MicrocodeEmbedding.embed NativeBatchErase.cfg cfg frame
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem seed_call (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ ArithmeticSeed.budget (PaddedWord.commonConstant F) source, Trace F t
      (cfg (start F) (initial source pre) pos) (cfg (.seed .done) (seeded F source pre) pos) := by
  obtain ⟨t,ht,htr⟩ := ArithmeticSeed.common_seed_trace F source (fun p => pos (seedPort p))
  have he := MicrocodeEmbedding.trace_embed seedBinding.ports (Label.seed (F:=F))
    (ArithmeticSeed.program (PaddedWord.commonConstant F)) (program F) (frame (initial source pre) pos) (seed_code F) htr
  exact ⟨t,ht,by simpa only [embed_seed,initial_seed,start,seeded] using he⟩

theorem clear_call (F : RationalMobius) (last : Bool) (s : Bank)
    (hs : s (clearPort last)=BinaryCarry.preparedOutput) (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace F t (cfg (.clear last 0) s pos)
      (cfg (.clear last 2) (Function.update s (clearPort last) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeUnprepare.complete_trace (fun _ => pos (clearPort last))
  have he := MicrocodeEmbedding.trace_embed (singleBinding (clearPort last)).ports (Label.clear (F:=F) last)
    NativeUnprepare.program (program F) (frame s pos) (clear_code F last) htr
  exact ⟨t,ht,by simpa only [embed_clear,← hs,Function.update_eq_self] using he⟩

theorem rows_call (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    let bits := RowEnumeration.rowsFrom F source (Counter.value source) 0
    ∃ t ≤ RowEnumeration.allowance F n (Counter.value source), Trace F t
      (cfg (.rows (RowEnumeration.start F)) (prepared F source pre) pos)
      (cfg (.rows .done) (prepared F source ((symbols bits).reverse++pre)) (finalPositions pos bits)) := by
  obtain ⟨t,ht,htr⟩ := RowEnumeration.complete_trace F source pre (fun p => pos (.rows p))
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have he := MicrocodeEmbedding.trace_embed rowsBinding.ports (Label.rows (F:=F))
    (RowEnumeration.program F) (program F)
    (frame (prepared F source pre) pos) (rows_code F) htr
  exact ⟨t,ht,by simpa only [prepared,embed_rows,rows_positions,rows_final_positions] using he⟩

theorem erase_call (F : RationalMobius) (source : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
    ∃ t ≤ 16*m+29, Trace F t (cfg (.erase (NativeBatchErase.entry 5 0)) (prepared F source pre) pos)
      (cfg (.erase .done) (Function.update (initial source pre) scratchPort BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBatchErase.complete_trace seedWords (words F source) (prepared F source pre)
    (prepared_words F source pre) pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports (Label.erase (F:=F))
    (NativeBatchErase.program seedWords) (program F) (frame (prepared F source pre) pos) (erase_code F) htr
  refine ⟨t,?_,by simpa only [embed_erase,prepared_erased] using he⟩
  have hm := RowEnumeration.common_positive F source
  simp only [words,Fin.sum_univ_succ,ArithmeticSeed.zeros,ArithmeticSeed.one_length _ hm,
    List.length_replicate,List.length_cons,List.length_nil,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero] at ht
  omega


end TransposeFollowup.SeededEnumeration


namespace TransposeFollowup.SeededEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def budget (F : RationalMobius) (source : List Bool) : ℕ :=
  ArithmeticSeed.budget (PaddedWord.commonConstant F) source+
    RowEnumeration.allowance F (PaddedWord.word (PaddedWord.commonConstant F) id source) (Counter.value source)+
    16*(PaddedWord.word (PaddedWord.commonConstant F) id source).length+38

theorem complete_trace (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    let bits := RowEnumeration.rowsFrom F source (Counter.value source) 0
    ∃ t ≤ budget F source, Trace F t (cfg (start F) (initial source pre) pos)
      (cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)) := by
  let bits := RowEnumeration.rowsFrom F source (Counter.value source) 0
  let outpre := (symbols bits).reverse++pre
  let outpos := finalPositions pos bits
  obtain ⟨a,ha,ta⟩ := seed_call F source pre pos
  have ja := jump_trace F (.seed .done) (.clear false 0) (seeded F source pre) pos rfl
  obtain ⟨b,hb,tb⟩ := clear_call F false (seeded F source pre) (seeded_temp F source pre) pos
  change Trace F b (cfg (.clear false 0) (seeded F source pre) pos)
    (cfg (.clear false 2) (Function.update (seeded F source pre) tempPort ⟨[],[]⟩) pos) at tb
  rw [prepared_seed] at tb
  have jb := jump_trace F (.clear false 2) (.rows (RowEnumeration.start F)) (prepared F source pre) pos rfl
  obtain ⟨c,hc,tc⟩ := rows_call F source pre pos
  have jc := jump_trace F (.rows .done) (.erase (NativeBatchErase.entry 5 0)) (prepared F source outpre) outpos rfl
  obtain ⟨d,hd,td⟩ := erase_call F source outpre outpos
  let s := Function.update (initial source outpre) scratchPort BinaryCarry.preparedOutput
  have jd := jump_trace F (.erase .done) (.clear true 0) s outpos rfl
  obtain ⟨e,he,te⟩ := clear_call F true s (by exact Function.update_self _ _ _) outpos
  have hs : Function.update s (clearPort true) ⟨[],[]⟩=initial source outpre := by
    change Function.update (Function.update (initial source outpre) scratchPort BinaryCarry.preparedOutput)
      scratchPort ⟨[],[]⟩=initial source outpre
    rw [Function.update_idem]
    exact Function.update_eq_self scratchPort (initial source outpre)
  rw [hs] at te
  have je := jump_trace F (.clear true 2) .done (initial source outpre) outpos rfl
  refine ⟨a+1+b+1+c+1+d+1+e+1,?_,?_⟩
  · unfold budget
    omega
  exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta ja) tb) jb) tc) jc) td) jd) te) je

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

theorem native_complete (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let bits := RowEnumeration.rowsFrom F source (Counter.value source) 0
    ∃ t ≤ budget F source,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (initial source pre) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (source : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let bits := RowEnumeration.rowsFrom F source (Counter.value source) 0
    ∃ t ≤ budget F source,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (start F) (initial source pre) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F source pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.SeededEnumeration


namespace TransposeFollowup.SeededEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def labelEquiv (F : RationalMobius) : Label F ≃
    ArithmeticSeed.Label (PaddedWord.commonConstant F) ⊕
    (Bool × NativeUnprepare.Label) ⊕ RowEnumeration.Label F ⊕ NativeBatchErase.Label 5 ⊕ Unit where
  toFun := fun
    | .seed pc => .inl pc | .clear b pc => .inr (.inl (b,pc))
    | .rows pc => .inr (.inr (.inl pc)) | .erase pc => .inr (.inr (.inr (.inl pc)))
    | .done => .inr (.inr (.inr (.inr ())))
  invFun := fun
    | .inl pc => .seed pc | .inr (.inl (b,pc)) => .clear b pc
    | .inr (.inr (.inl pc)) => .rows pc | .inr (.inr (.inr (.inl pc))) => .erase pc
    | .inr (.inr (.inr (.inr _))) => .done
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨b,pc⟩ | pc | pc | ⟨⟩) <;> rfl

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=41 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+
      2*PaddedWord.commonConstant F+12780 ∧ (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=41
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hr := (RowEnumeration.fixed_resources F).2.2.1
    change Fintype.card (RowEnumeration.Label F)-1+1=_ at hr
    have hp : 0<Fintype.card (RowEnumeration.Label F) := Fintype.card_pos_iff.mpr ⟨RowEnumeration.start F⟩
    have he : Fintype.card (NativeBatchErase.Label 5)=41 := by decide +kernel
    have hu : Fintype.card NativeUnprepare.Label=3 := by decide +kernel
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
      Fintype.card_unit,ArithmeticSeed.label_card,he,hu]
    omega

theorem total_budget (F : RationalMobius) (N : ℕ) (source : List Bool)
    (hN : 1 ≤ N) (hv : Counter.value source=N) (hl : source.length ≤ (N+1).size) :
    let T := SourceImages.sourceSum F+SourceImages.coefficientSum F
    budget F source ≤
      ((1942+72*T)*(F.integerOperandConstant^2).size+24088+928*T)*Transpose.inputLength N := by
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hr := RowEnumeration.total_budget F N source hN hv hl
  have hs := ArithmeticSeed.total_budget F N source hN hl
  have hs0 : ArithmeticSeed.budget (PaddedWord.commonConstant F) source ≤
      N*(N*ArithmeticSeed.budget (PaddedWord.commonConstant F) source) := by
    exact (Nat.le_mul_of_pos_left _ hN).trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hN))
  have hs1 := hs0.trans hs
  have hm : 16*n.length+38 ≤ (16*PaddedWord.commonConstant F+38)+32*(N+1).size := by
    dsimp [n]; rw [PaddedWord.word_length]; omega
  have ho := dense_scan_budget (16*PaddedWord.commonConstant F+38) 32 N hN
  have he : 2*(16*PaddedWord.commonConstant F+38+3*32)=32*(F.integerOperandConstant^2).size+396 := by
    unfold PaddedWord.commonConstant; ring
  have hb : 16*n.length+38 ≤ (32*(F.integerOperandConstant^2).size+396)*Transpose.inputLength N := by
    calc
      _ ≤ N*(N*(16*n.length+38)) :=
        (Nat.le_mul_of_pos_left _ hN).trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hN))
      _ ≤ N*(N*((16*PaddedWord.commonConstant F+38)+32*(N+1).size)) := by gcongr
      _ ≤ _ := by simpa only [he] using ho
  unfold budget
  rw [hv]
  change ArithmeticSeed.budget (PaddedWord.commonConstant F) source+RowEnumeration.allowance F n N+
    16*n.length+38 ≤ _
  change RowEnumeration.allowance F n N ≤ _ at hr
  nlinarith

theorem native_records (F : RationalMobius) (source : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    let rs := RowEnumeration.rowsRecords F source (Counter.value source) 0
    let bits := rs.flatMap (fun p => p.1++p.2)
    (∀ p : ℕ × ℕ,p ∈ rs.map RowEnumeration.decodePair ↔
      ∃ u v : Fin (Counter.value source),v ∈ F.neighbors u ∧ p=(u.val,v.val)) ∧
    (rs.map RowEnumeration.decodePair).Nodup ∧
    (∀ p ∈ rs,p.1.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length ∧
      p.2.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) ∧
    ∃ t ≤ budget F source,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (start F) (initial source pre) pos).denote (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg .done (initial source ((symbols bits).reverse++pre)) (finalPositions pos bits)).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  refine ⟨RowEnumeration.all_records_spec F source,RowEnumeration.rows_values_nodup F source _ _ (by omega),
    RowEnumeration.rows_records_width F source _ _,?_⟩
  simpa only [RowEnumeration.rows_encoding] using native_complete F source pre pos input inputPos outRev

end TransposeFollowup.SeededEnumeration


/-! The raw loader and the seeded map enumerator share work tapes.
The payload has one separate, preserved tape. No dimension header or
preinitialized arithmetic bank is supplied to the resulting program. -/
namespace TransposeFollowup.RawEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | payload | enumeration (p : SeededEnumeration.Port)
  deriving DecidableEq,Fintype
abbrev Bank := Port → Tape Bool

def sharedPort (p : EndpointClip.Port) : Port := .enumeration (.rows (.row (.prep (.images (.source (.shared p))))))

def rawPort : RawDimensionLoader.Port → Port
  | .payload => .payload
  | .loader (.work .candidate) => .enumeration .source
  | .loader (.work .square) => sharedPort .dimension
  | .loader (.work .bits) => sharedPort .index
  | .loader (.work .threshold) => sharedPort .unit
  | .loader (.work .unit) => sharedPort .zero
  | .loader (.work .zero) => sharedPort .fuel
  | .loader (.work .fuel) => sharedPort .scratch
  | .loader (.work .scratch) => sharedPort .grid
  | .loader (.work .copyThreshold) => sharedPort (.work 0)
  | .loader (.work .product) => sharedPort (.work 1)
  | .loader (.work .repeatFuel) => sharedPort (.work 2)
  | .loader (.work .length) => sharedPort (.work 3)
  | .loader .source => sharedPort (.out 0)
  | .loader .extra => sharedPort (.out 1)

def rawBinding : FinitePortBinding RawDimensionLoader.Port Port where
  ports:=⟨rawPort,by decide +kernel⟩
  decode:=fun p => match p with
    | .payload => some .payload
    | .enumeration .source => some (.loader (.work .candidate))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .dimension)))))) => some (.loader (.work .square))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .index)))))) => some (.loader (.work .bits))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .unit)))))) => some (.loader (.work .threshold))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .zero)))))) => some (.loader (.work .unit))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .fuel)))))) => some (.loader (.work .zero))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .scratch)))))) => some (.loader (.work .fuel))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared .grid)))))) => some (.loader (.work .scratch))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.work 0))))))) => some (.loader (.work .copyThreshold))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.work 1))))))) => some (.loader (.work .product))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.work 2))))))) => some (.loader (.work .repeatFuel))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.work 3))))))) => some (.loader (.work .length))
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.out 0))))))) => some (.loader .source)
    | .enumeration (.rows (.row (.prep (.images (.source (.shared (.out 1))))))) => some (.loader .extra)
    | _ => none
  decode_spec:=by decide +kernel

def enumerationBinding : FinitePortBinding SeededEnumeration.Port Port where
  ports:=⟨Port.enumeration,by intro p q h;cases h;rfl⟩
  decode:=fun p => match p with | .enumeration p => some p | _ => none
  decode_spec:=by decide +kernel

inductive Label (F : RationalMobius)
  | raw (pc : RawDimensionLoader.Label)
  | enumeration (pc : SeededEnumeration.Label F)
  deriving DecidableEq,Fintype

def start (F : RationalMobius) : Label F := .raw RawDimensionLoader.start

def program (F : RationalMobius) : NativeIO.Program Port (Label F)
  | .raw (.load .done) => .work (.jump (.enumeration (SeededEnumeration.start F)))
  | .raw pc => NativeIOEmbedding.boundInstruction rawBinding Label.raw (RawDimensionLoader.program pc)
  | .enumeration pc => .work (enumerationBinding.instruction Label.enumeration (SeededEnumeration.program F pc))

theorem raw_code (F : RationalMobius) (pc : RawDimensionLoader.Label) (hh : RawDimensionLoader.program pc≠.work .halt)
    (_ : RawDimensionLoader.program pc≠.work .reject) :
    program F (.raw pc)=NativeIOEmbedding.instruction rawBinding.ports Label.raw (RawDimensionLoader.program pc) := by
  cases pc with
  | measure pc => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | load pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem enumeration_code (F : RationalMobius) (pc : SeededEnumeration.Label F)
    (_ : SeededEnumeration.program F pc≠.halt) (_ : SeededEnumeration.program F pc≠.reject) :
    NativeIO.workProgram (program F) (.enumeration pc)=
      MicrocodeEmbedding.instruction enumerationBinding.ports Label.enumeration (SeededEnumeration.program F pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩

def initial (pre : List (Sym Bool)) : Bank
  | .enumeration (.rows .output) => ⟨pre,[]⟩ | _ => ⟨[],[]⟩

def liftBank (payload : List Bool) (s : SeededEnumeration.Bank) : Bank
  | .payload => Counter.marked payload | .enumeration p => s p

def loaded (payload xs : List Bool) (pre : List (Sym Bool)) := liftBank payload (SeededEnumeration.initial xs pre)

def finalPositions (pos : Port → ℤ) (bits : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.enumeration (.rows .output) then (bits.length : ℤ) else 0

abbrev Trace (F : RationalMobius) (w : List Bool) := OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

end TransposeFollowup.RawEnumeration


namespace TransposeFollowup.RawEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem initial_raw (pre : List (Sym Bool)) : rawBinding.values RawDimensionLoader.initial (initial pre)=initial pre := by
  funext p;fin_cases p <;> rfl

theorem loaded_raw (w xs : List Bool) (pre : List (Sym Bool)) :
    rawBinding.values (RawDimensionLoader.finalBank w xs) (initial pre)=loaded w xs pre := by
  funext p;fin_cases p <;> rfl

theorem embed_raw (F : RationalMobius) (pc : RawDimensionLoader.Label) (s : RawDimensionLoader.Bank) (base : Bank)
    (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed rawBinding.ports (Label.raw (F:=F))
      (RawDimensionLoader.cfg pc s (fun p => pos (rawPort p)) ip outRev) (frame base pos)=
      cfg (.raw pc) (rawBinding.values s base) pos ip outRev := by
  unfold NativeIOEmbedding.embed RawDimensionLoader.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed RawDimensionLoader.workCfg workCfg frame
  simp only [← rawBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem raw_call (F : RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ 8300*w.length, Trace F w t (cfg (start F) (initial pre) pos 0 outRev)
      (cfg (.raw (.load .done)) (loaded w xs pre) pos w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := RawDimensionLoader.complete_trace w n hn hw (fun p => pos (rawPort p)) outRev
  have he := NativeIOEmbedding.trace_embed rawBinding.ports (Label.raw (F:=F)) RawDimensionLoader.program (program F)
    (frame (initial pre) pos) w (raw_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_raw,initial_raw,loaded_raw,start] using he⟩

theorem enumeration_positions (pos : Port → ℤ) :
    enumerationBinding.values (fun p => pos (.enumeration p)) pos=pos := by
  funext p;cases p <;> rfl

theorem enumeration_final_positions (pos : Port → ℤ) (bits : List Bool) :
    enumerationBinding.values (SeededEnumeration.finalPositions (fun p => pos (.enumeration p)) bits) pos=finalPositions pos bits := by
  funext p
  cases p <;> simp [enumerationBinding,FinitePortBinding.values,SeededEnumeration.finalPositions,finalPositions]

theorem embed_enumeration (F : RationalMobius) (pc : SeededEnumeration.Label F) (s base : SeededEnumeration.Bank)
    (w : List Bool) (rpos : SeededEnumeration.Port → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed enumerationBinding.ports (Label.enumeration (F:=F)) (SeededEnumeration.cfg pc s rpos)
      (frame (liftBank w base) pos)=workCfg (.enumeration pc) (liftBank w s) (enumerationBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed SeededEnumeration.cfg workCfg frame
  simp only [← enumerationBinding.values_eq_extend]
  congr 2
  funext p;cases p <;> rfl

theorem enumeration_call (F : RationalMobius) (w xs : List Bool) (pre : List (Sym Bool))
    (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    let bits := RowEnumeration.rowsFrom F xs (Counter.value xs) 0
    ∃ t ≤ SeededEnumeration.budget F xs, Trace F w t
      (cfg (.enumeration (SeededEnumeration.start F)) (loaded w xs pre) pos ip outRev)
      (cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse++pre)) (finalPositions pos bits) ip outRev) := by
  obtain ⟨t,ht,htr⟩ := SeededEnumeration.complete_trace F xs pre (fun p => pos (.enumeration p))
  have he := MicrocodeEmbedding.trace_embed enumerationBinding.ports (Label.enumeration (F:=F)) (SeededEnumeration.program F)
    (NativeIO.workProgram (program F)) (frame (loaded w xs pre) pos) (enumeration_code F) htr
  refine ⟨t,ht,?_⟩
  simpa only [loaded,embed_enumeration,enumeration_positions,enumeration_final_positions,cfg] using
    NativeIO.lift_work_trace (program F) w ip outRev he

theorem jump_trace (F : RationalMobius) (w xs : List Bool) (pre : List (Sym Bool))
    (pos : Port → ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.raw (.load .done)) (loaded w xs pre) pos w.length outRev)
      (cfg (.enumeration (SeededEnumeration.start F)) (loaded w xs pre) pos w.length outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.RawEnumeration


namespace TransposeFollowup.RawEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def coefficient (F : RationalMobius) : ℕ :=
  let T:=SourceImages.sourceSum F+SourceImages.coefficientSum F
  (1942+72*T)*(F.integerOperandConstant^2).size+32389+928*T

theorem initial_nil : initial []=(fun _ => ⟨[],[]⟩) := by
  funext p;fin_cases p <;> rfl

theorem complete_trace (F : RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    let bits:=RowEnumeration.rowsFrom F xs n 0
    ∃ t ≤ coefficient F*w.length, Trace F w t (cfg (start F) (initial pre) pos 0 outRev)
      (cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse++pre)) (finalPositions pos bits) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩ := raw_call F w n hn hw pre pos outRev
  obtain ⟨b,hb,tb⟩ := enumeration_call F w xs pre pos w.length outRev
  rw [hv] at tb
  have he := SeededEnumeration.total_budget F n xs hn hv (by rw [hl];exact Nat.size_le_size (Nat.le_succ n))
  have hL : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨xs,hx,hv,hl,a+1+b,?_,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans ta (jump_trace F w xs pre pos outRev)) tb⟩
  dsimp only at he
  rw [← hw] at he
  unfold coefficient
  nlinarith

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    let bits:=RowEnumeration.rowsFrom F xs n 0
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse))
          (finalPositions (fun _ => 0) bits) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse))
        (finalPositions (fun _ => 0) bits) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw [] (fun _ => 0) []
  simp only [List.append_nil] at htr
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hb : (cfg (start F) (initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=Transpose.init (nativeMachine F) := by
      rw [initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,SeededEnumeration.program]

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label F → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.work .halt → program F pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program F pc))
    (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    let bits:=RowEnumeration.rowsFrom F xs n 0
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg (start F) (initial pre) pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels
          (cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse++pre)) (finalPositions pos bits) w.length outRev)
          outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw pre pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

end TransposeFollowup.RawEnumeration


namespace TransposeFollowup.RawEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def labelEquiv (F : RationalMobius) : Label F ≃ RawDimensionLoader.Label ⊕ SeededEnumeration.Label F where
  toFun | .raw pc => .inl pc | .enumeration pc => .inr pc
  invFun | .inl pc => .raw pc | .inr pc => .enumeration pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by intro pc;cases pc <;> rfl

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+
      2*PaddedWord.commonConstant F+14222 ∧ (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hs := (SeededEnumeration.fixed_resources F).2.2.1
    change Fintype.card (SeededEnumeration.Label F)-1+1=_ at hs
    have hp : 0<Fintype.card (SeededEnumeration.Label F) := Fintype.card_pos_iff.mpr ⟨SeededEnumeration.start F⟩
    have hr : Fintype.card RawDimensionLoader.Label=1442 := by decide +kernel
    simp only [Fintype.card_sum,hr]
    omega

theorem native_records (F : RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    let rs:=RowEnumeration.rowsRecords F xs n 0
    let bits:=rs.flatMap (fun p => p.1++p.2)
    (∀ p : ℕ × ℕ,p ∈ rs.map RowEnumeration.decodePair ↔ ∃ u v : Fin n,v ∈ F.neighbors u ∧ p=(u.val,v.val)) ∧
    (rs.map RowEnumeration.decodePair).Nodup ∧
    (∀ p ∈ rs,p.1.length=2*n.size+PaddedWord.commonConstant F ∧ p.2.length=2*n.size+PaddedWord.commonConstant F) ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse))
          (finalPositions (fun _ => 0) bits) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg (.enumeration .done) (loaded w xs ((symbols bits).reverse))
        (finalPositions (fun _ => 0) bits) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr,hstop⟩ := native_complete F w n hn hw
  subst n
  refine ⟨xs,hx,rfl,hl,?_,?_,?_,t,ht,?_,?_⟩
  · intro p
    exact RowEnumeration.all_records_spec F xs p
  · exact RowEnumeration.rows_values_nodup F xs (Counter.value xs) 0 (by omega)
  · have hm : (PaddedWord.word (PaddedWord.commonConstant F) id xs).length=2*(Counter.value xs).size+PaddedWord.commonConstant F := by
      rw [PaddedWord.word_length,hl]
    simpa only [hm] using RowEnumeration.rows_records_width F xs (Counter.value xs) 0
  · simpa only [RowEnumeration.rows_encoding] using htr
  · simpa only [RowEnumeration.rows_encoding] using hstop

end TransposeFollowup.RawEnumeration


/-! A fixed nonempty family shares the single-map enumerator's 42 tapes.
Only the first phase loads the raw input. Each phase appends one paid STOP,
including when it emits no pairs. The family belongs to finite control. -/
namespace TransposeFollowup.FamilyEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

abbrev Port := RawEnumeration.Port
abbrev Bank := RawEnumeration.Bank
def output : Port := .enumeration (.rows .output)

inductive Label (F : Fin (r+1) → RationalMobius)
  | first (pc : RawEnumeration.Label (F 0))
  | rest (j : Fin r) (pc : SeededEnumeration.Label (F j.succ))
  | done
  deriving DecidableEq,Fintype

def identityBinding : FinitePortBinding Port Port where
  ports:=Function.Embedding.refl Port
  decode:=some
  decode_spec:=by intro p q; simp [eq_comm]

def entry (F : Fin (r+1) → RationalMobius) (k : ℕ) : Label F :=
  if h : k<r then .rest ⟨k,h⟩ (SeededEnumeration.start (F ⟨k+1,by omega⟩)) else .done

def start (F : Fin (r+1) → RationalMobius) : Label F := .first (RawEnumeration.start (F 0))

def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .first (.enumeration .done) => .work (.act (Microcode.single output ⟨some .stop,.right⟩) (entry F 0))
  | .first pc => NativeIOEmbedding.boundInstruction identityBinding Label.first (RawEnumeration.program (F 0) pc)
  | .rest j .done => .work (.act (Microcode.single output ⟨some .stop,.right⟩) (entry F (j.val+1)))
  | .rest j pc => .work (RawEnumeration.enumerationBinding.instruction (Label.rest j) (SeededEnumeration.program (F j.succ) pc))
  | .done => .work .halt

theorem first_code (F : Fin (r+1) → RationalMobius) (pc : RawEnumeration.Label (F 0))
    (hh : RawEnumeration.program (F 0) pc≠.work .halt) (_ : RawEnumeration.program (F 0) pc≠.work .reject) :
    program F (.first pc)=NativeIOEmbedding.instruction identityBinding.ports Label.first (RawEnumeration.program (F 0) pc) := by
  cases pc with
  | raw pc => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | enumeration pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem rest_code (F : Fin (r+1) → RationalMobius) (j : Fin r) (pc : SeededEnumeration.Label (F j.succ))
    (hh : SeededEnumeration.program (F j.succ) pc≠.halt) (_ : SeededEnumeration.program (F j.succ) pc≠.reject) :
    NativeIO.workProgram (program F) (.rest j pc)=MicrocodeEmbedding.instruction RawEnumeration.enumerationBinding.ports
      (Label.rest j) (SeededEnumeration.program (F j.succ) pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def advance (pos : Port → ℤ) (d : ℕ) : Port → ℤ := fun p => pos p+if p=output then (d : ℤ) else 0
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem advance_zero (pos : Port → ℤ) : advance pos 0=pos := by
  funext p; simp [advance]

theorem advance_add (pos : Port → ℤ) (a b : ℕ) : advance (advance pos a) b=advance pos (a+b) := by
  funext p; by_cases h : p=output <;> simp [advance,h,add_assoc]

theorem advance_bits (pos : Port → ℤ) (bits : List Bool) : RawEnumeration.finalPositions pos bits=advance pos bits.length := rfl

end TransposeFollowup.FamilyEnumeration


namespace TransposeFollowup.FamilyEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem embed_first (F : Fin (r+1) → RationalMobius) (pc : RawEnumeration.Label (F 0))
    (s base : Bank) (pos framePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed identityBinding.ports (Label.first (F:=F)) (RawEnumeration.cfg pc s pos ip outRev)
      (RawEnumeration.frame base framePos)=cfg (.first pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed RawEnumeration.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed RawEnumeration.workCfg workCfg RawEnumeration.frame
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem first_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    let bits:=RowEnumeration.rowsFrom (F 0) xs n 0
    ∃ t ≤ RawEnumeration.coefficient (F 0)*w.length, Trace F w t
      (cfg (start F) (RawEnumeration.initial pre) pos 0 outRev)
      (cfg (.first (.enumeration .done)) (RawEnumeration.loaded w xs ((symbols bits).reverse++pre))
        (advance pos bits.length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := RawEnumeration.complete_trace (F 0) w n hn hw pre pos outRev
  have he := NativeIOEmbedding.trace_embed identityBinding.ports (Label.first (F:=F)) (RawEnumeration.program (F 0))
    (program F) (RawEnumeration.frame (RawEnumeration.initial pre) pos) w (first_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_first,start,advance_bits] using he⟩

theorem embed_rest (F : Fin (r+1) → RationalMobius) (j : Fin r) (pc : SeededEnumeration.Label (F j.succ))
    (s base : SeededEnumeration.Bank) (w : List Bool) (rpos : SeededEnumeration.Port → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed RawEnumeration.enumerationBinding.ports (Label.rest (F:=F) j)
      (SeededEnumeration.cfg pc s rpos) (RawEnumeration.frame (RawEnumeration.liftBank w base) pos)=
      workCfg (.rest j pc) (RawEnumeration.liftBank w s) (RawEnumeration.enumerationBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed SeededEnumeration.cfg workCfg RawEnumeration.frame
  simp only [← RawEnumeration.enumerationBinding.values_eq_extend]
  congr 2
  funext p;cases p <;> rfl

theorem rest_call (F : Fin (r+1) → RationalMobius) (j : Fin r) (w xs : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    let bits:=RowEnumeration.rowsFrom (F j.succ) xs (Counter.value xs) 0
    ∃ t ≤ SeededEnumeration.budget (F j.succ) xs, Trace F w t
      (cfg (.rest j (SeededEnumeration.start (F j.succ))) (RawEnumeration.loaded w xs pre) pos ip outRev)
      (cfg (.rest j .done) (RawEnumeration.loaded w xs ((symbols bits).reverse++pre))
        (advance pos bits.length) ip outRev) := by
  obtain ⟨t,ht,htr⟩ := SeededEnumeration.complete_trace (F j.succ) xs pre (fun p => pos (.enumeration p))
  have he := MicrocodeEmbedding.trace_embed RawEnumeration.enumerationBinding.ports (Label.rest (F:=F) j)
    (SeededEnumeration.program (F j.succ)) (NativeIO.workProgram (program F))
    (RawEnumeration.frame (RawEnumeration.loaded w xs pre) pos) (rest_code F j) htr
  refine ⟨t,ht,?_⟩
  simpa only [RawEnumeration.loaded,embed_rest,RawEnumeration.enumeration_positions,
    RawEnumeration.enumeration_final_positions,advance_bits,cfg] using NativeIO.lift_work_trace (program F) w ip outRev he

theorem seal_trace (F : Fin (r+1) → RationalMobius) (pc next : Label F)
    (hc : program F pc=.work (.act (Microcode.single output ⟨some .stop,.right⟩) next))
    (w xs : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg pc (RawEnumeration.loaded w xs pre) pos ip outRev)
      (cfg next (RawEnumeration.loaded w xs (.stop::pre)) (advance pos 1) ip outRev) := by
  let z : NativeZipper.Config Port (Label F) := ⟨⟨pc,RawEnumeration.loaded w xs pre⟩,pos⟩
  let z' : NativeZipper.Config Port (Label F) := ⟨⟨next,RawEnumeration.loaded w xs (.stop::pre)⟩,advance pos 1⟩
  have hz : NativeZipper.step (NativeIO.workProgram (program F)) z=z' := by
    simp only [z,z',NativeZipper.step,Microcode.step,NativeIO.workProgram,hc,Microcode.Action.apply]
    congr 2
    · funext p
      fin_cases p <;> rfl
    · funext p
      by_cases h : p=output <;> simp [Microcode.single,advance,h,NativeMicrocode.direction,Transpose.Dir.shift]
  have he : NativeMicrocode.step (NativeIO.workProgram (program F)) z.denote=z'.denote := by
    rw [← NativeZipper.step_denote,hz]
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,hc]
  · change Trace F w 0 (NativeIO.step (program F) w (cfg pc (RawEnumeration.loaded w xs pre) pos ip outRev)) _
    have hs : NativeIO.step (program F) w (cfg pc (RawEnumeration.loaded w xs pre) pos ip outRev)=
        cfg next (RawEnumeration.loaded w xs (.stop::pre)) (advance pos 1) ip outRev := by
      change NativeIO.step (program F) w ⟨z.denote,ip,outRev⟩=⟨z'.denote,ip,outRev⟩
      simp only [NativeIO.step,z,NativeZipper.Config.denote,Microcode.Config.denote,hc]
      exact congrArg (fun c => (⟨c,ip,outRev⟩ : NativeIO.Config Port (Label F))) he
    rw [hs]
    exact .refl _

end TransposeFollowup.FamilyEnumeration


namespace TransposeFollowup.FamilyEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def batch (F : RationalMobius) (xs : List Bool) : List (Sym Bool) :=
  symbols (RowEnumeration.rowsFrom F xs (Counter.value xs) 0) ++ [.stop]

def restStream (F : Fin (r+1) → RationalMobius) (xs : List Bool) : ℕ → ℕ → List (Sym Bool)
  | _,0 => []
  | k,q+1 => if h : k<r then batch (F (⟨k,h⟩ : Fin r).succ) xs ++ restStream F xs (k+1) q else []

def restBudget (F : Fin (r+1) → RationalMobius) (xs : List Bool) : ℕ → ℕ → ℕ
  | _,0 => 0
  | k,q+1 => if h : k<r then SeededEnumeration.budget (F (⟨k,h⟩ : Fin r).succ) xs+1+restBudget F xs (k+1) q else 0

def stream (F : Fin (r+1) → RationalMobius) (xs : List Bool) := batch (F 0) xs ++ restStream F xs 0 r

theorem rest_batch (F : Fin (r+1) → RationalMobius) (j : Fin r) (w xs : List Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ SeededEnumeration.budget (F j.succ) xs+1, Trace F w t
      (cfg (entry F j.val) (RawEnumeration.loaded w xs pre) pos ip outRev)
      (cfg (entry F (j.val+1)) (RawEnumeration.loaded w xs ((batch (F j.succ) xs).reverse++pre))
        (advance pos (batch (F j.succ) xs).length) ip outRev) := by
  let bits:=RowEnumeration.rowsFrom (F j.succ) xs (Counter.value xs) 0
  obtain ⟨a,ha,ta⟩ := rest_call F j w xs pre pos ip outRev
  have tb := seal_trace F (.rest j .done) (entry F (j.val+1)) rfl w xs
    ((symbols bits).reverse++pre) (advance pos bits.length) ip outRev
  refine ⟨a+1,by omega,?_⟩
  have hj : entry F j.val=.rest j (SeededEnumeration.start (F j.succ)) := by
    simp only [entry,dite_eq_left j.isLt]
    rfl
  rw [hj]
  simpa only [bits,batch,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.cons_append,List.append_assoc,advance_add,List.length_append,List.length_cons,
    List.length_nil,symbols,List.length_map] using NativeCountedLoop.trace_trans ta tb

theorem first_batch (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ RawEnumeration.coefficient (F 0)*w.length+1, Trace F w t
      (cfg (start F) (RawEnumeration.initial pre) pos 0 outRev)
      (cfg (entry F 0) (RawEnumeration.loaded w xs ((batch (F 0) xs).reverse++pre))
        (advance pos (batch (F 0) xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩ := first_call F w n hn hw pre pos outRev
  rw [← hv] at ta
  let bits:=RowEnumeration.rowsFrom (F 0) xs (Counter.value xs) 0
  have tb := seal_trace F (.first (.enumeration .done)) (entry F 0) rfl w xs
    ((symbols bits).reverse++pre) (advance pos bits.length) w.length outRev
  refine ⟨xs,hx,hv,hl,a+1,by omega,?_⟩
  simpa only [batch,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.append_assoc,advance_add,List.length_append,List.length_cons,List.length_nil,symbols,List.length_map]
    using NativeCountedLoop.trace_trans ta tb

theorem rest_trace (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (q k : ℕ) (hk : k+q=r) (pre : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ restBudget F xs k q, Trace F w t
      (cfg (entry F k) (RawEnumeration.loaded w xs pre) pos ip outRev)
      (cfg .done (RawEnumeration.loaded w xs ((restStream F xs k q).reverse++pre))
        (advance pos (restStream F xs k q).length) ip outRev) := by
  induction q generalizing k pre pos with
  | zero =>
    have he : k=r := by omega
    subst k
    refine ⟨0,by rfl,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte,restStream,List.reverse_nil,List.nil_append,List.length_nil,advance_zero]
    exact .refl _
  | succ q ih =>
    have hkr : k<r := by omega
    let j : Fin r := ⟨k,hkr⟩
    obtain ⟨a,ha,ta⟩ := rest_batch F j w xs pre pos ip outRev
    obtain ⟨b,hb,tb⟩ := ih (k+1) (by omega) ((batch (F j.succ) xs).reverse++pre)
      (advance pos (batch (F j.succ) xs).length)
    refine ⟨a+b,?_,?_⟩
    · simp only [restBudget,hkr,↓reduceDIte]
      exact Nat.add_le_add ha hb
    · simpa only [restStream,hkr,↓reduceDIte,List.reverse_append,List.append_assoc,advance_add,List.length_append]
        using NativeCountedLoop.trace_trans ta tb

end TransposeFollowup.FamilyEnumeration


namespace TransposeFollowup.FamilyEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def seededCoefficient (F : RationalMobius) : ℕ :=
  let T:=SourceImages.sourceSum F+SourceImages.coefficientSum F
  (1942+72*T)*(F.integerOperandConstant^2).size+24088+928*T

def restCoefficient (F : Fin (r+1) → RationalMobius) : ℕ → ℕ → ℕ
  | _,0 => 0
  | k,q+1 => if h : k<r then seededCoefficient (F (⟨k,h⟩ : Fin r).succ)+1+restCoefficient F (k+1) q else 0

def coefficient (F : Fin (r+1) → RationalMobius) := RawEnumeration.coefficient (F 0)+1+restCoefficient F 0 r

theorem rest_budget_le (F : Fin (r+1) → RationalMobius) (xs : List Bool) (n : ℕ) (hn : 1≤n)
    (hv : Counter.value xs=n) (hl : xs.length=n.size) (q k : ℕ) :
    restBudget F xs k q ≤ restCoefficient F k q*Transpose.inputLength n := by
  have hL : 1≤Transpose.inputLength n := hn.trans (DimensionCandidate.dimension_le_length n hn)
  induction q generalizing k with
  | zero => simp [restBudget,restCoefficient]
  | succ q ih =>
    by_cases hk : k<r
    · have he := SeededEnumeration.total_budget (F (⟨k,hk⟩ : Fin r).succ) n xs hn hv
        (by rw [hl];exact Nat.size_le_size (Nat.le_succ n))
      change SeededEnumeration.budget _ _ ≤ seededCoefficient _*Transpose.inputLength n at he
      have hb := ih (k+1)
      simp only [restBudget,restCoefficient,hk,↓reduceDIte]
      nlinarith
    · simp [restBudget,restCoefficient,hk]

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length, Trace F w t (cfg (start F) (RawEnumeration.initial pre) pos 0 outRev)
      (cfg .done (RawEnumeration.loaded w xs ((stream F xs).reverse++pre))
        (advance pos (stream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩ := first_batch F w n hn hw pre pos outRev
  obtain ⟨b,hb,tb⟩ := rest_trace F w xs r 0 (by omega) ((batch (F 0) xs).reverse++pre)
    (advance pos (batch (F 0) xs).length) w.length outRev
  have he := rest_budget_le F xs n hn hv hl r 0
  rw [← hw] at he
  have hL : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨xs,hx,hv,hl,a+b,?_,?_⟩
  · unfold coefficient
    nlinarith
  · simpa only [stream,List.reverse_append,List.append_assoc,advance_add,List.length_append]
      using NativeCountedLoop.trace_trans ta tb

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg .done (RawEnumeration.loaded w xs (stream F xs).reverse)
          (advance (fun _ => 0) (stream F xs).length) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg .done (RawEnumeration.loaded w xs (stream F xs).reverse)
        (advance (fun _ => 0) (stream F xs).length) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw [] (fun _ => 0) []
  simp only [List.append_nil] at htr
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hb : (cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) := by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hb]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (F : Fin (r+1) → RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label F → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.work .halt → program F pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program F pc))
    (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg (start F) (RawEnumeration.initial pre) pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels
          (cfg .done (RawEnumeration.loaded w xs ((stream F xs).reverse++pre)) (advance pos (stream F xs).length) w.length outRev)
          outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw pre pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

end TransposeFollowup.FamilyEnumeration


namespace TransposeFollowup.FamilyEnumeration
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def seedStates (F : RationalMobius) : ℕ :=
  198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
  396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*SourceImages.coefficientSum F+
  2*PaddedWord.commonConstant F+12780

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃
    RawEnumeration.Label (F 0) ⊕ (Σ j : Fin r,SeededEnumeration.Label (F j.succ)) ⊕ Unit where
  toFun | .first pc => .inl pc | .rest j pc => .inr (.inl ⟨j,pc⟩) | .done => .inr (.inr ())
  invFun | .inl pc => .first pc | .inr (.inl ⟨j,pc⟩) => .rest j pc | .inr (.inr _) => .done
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc | ⟨j,pc⟩ | ⟨⟩) <;> rfl

theorem seed_label_card (F : RationalMobius) : Fintype.card (SeededEnumeration.Label F)=seedStates F := by
  have hs := (SeededEnumeration.fixed_resources F).2.2.1
  change Fintype.card (SeededEnumeration.Label F)-1+1=seedStates F at hs
  have hp : 0<Fintype.card (SeededEnumeration.Label F) := Fintype.card_pos_iff.mpr ⟨SeededEnumeration.start F⟩
  omega

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1443+∑ i : Fin (r+1),seedStates (F i) ∧ (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hp : 0<Fintype.card (RawEnumeration.Label (F 0)) := Fintype.card_pos_iff.mpr ⟨RawEnumeration.start (F 0)⟩
    have hr : Fintype.card (RawEnumeration.Label (F 0))=1442+seedStates (F 0) := by
      rw [Fintype.card_congr (RawEnumeration.labelEquiv (F 0)),Fintype.card_sum,seed_label_card]
      have hd : Fintype.card RawDimensionLoader.Label=1442 := by decide +kernel
      rw [hd]
    simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_unit,seed_label_card,hr,Fin.sum_univ_succ]
    omega

theorem rest_stream_ofFn (F : Fin (r+1) → RationalMobius) (xs : List Bool) (q k : ℕ) (hk : k+q≤r) :
    restStream F xs k q=(List.ofFn (fun j : Fin q => batch (F ⟨k+j.val+1,by omega⟩) xs)).flatten := by
  induction q generalizing k with
  | zero => simp [restStream]
  | succ q ih =>
    have hkr : k<r := by omega
    simp only [restStream,hkr,↓reduceDIte,List.ofFn_succ,List.flatten_cons]
    rw [ih (k+1) (by omega)]
    congr 1
    congr 1
    apply congrArg List.ofFn
    funext j
    congr 2
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem stream_ofFn (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    stream F xs=(List.ofFn (fun i : Fin (r+1) => batch (F i) xs)).flatten := by
  unfold stream
  rw [rest_stream_ofFn F xs r 0 (by omega)]
  simp only [List.ofFn_succ,List.flatten_cons]
  simp only [Nat.zero_add]
  rfl

theorem rest_coefficient_sum (F : Fin (r+1) → RationalMobius) (q k : ℕ) (hk : k+q≤r) :
    restCoefficient F k q=∑ j : Fin q,(seededCoefficient (F ⟨k+j.val+1,by omega⟩)+1) := by
  induction q generalizing k with
  | zero => simp [restCoefficient]
  | succ q ih =>
    have hkr : k<r := by omega
    simp only [restCoefficient,hkr,↓reduceDIte,Fin.sum_univ_succ]
    rw [ih (k+1) (by omega)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 3
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

theorem coefficient_sum (F : Fin (r+1) → RationalMobius) :
    coefficient F=8301+∑ i : Fin (r+1),(seededCoefficient (F i)+1) := by
  unfold coefficient
  rw [rest_coefficient_sum F r 0 (by omega),Fin.sum_univ_succ]
  simp only [Nat.zero_add]
  have he : RawEnumeration.coefficient (F 0)=8301+seededCoefficient (F 0) := by
    dsimp only [RawEnumeration.coefficient,seededCoefficient]
    omega
  rw [he]
  simp only [Nat.add_assoc]
  rfl

theorem batch_delimiter_count (F : RationalMobius) (xs : List Bool) : (batch F xs).count .stop=1 := by
  have h : ∀ bits : List Bool,(symbols bits).count (.stop : Sym Bool)=0 := by
    intro bits
    apply List.count_eq_zero.mpr
    simp [symbols]
  simp [batch,List.count_append,h]

theorem stream_delimiter_count (F : Fin (r+1) → RationalMobius) (xs : List Bool) : (stream F xs).count .stop=r+1 := by
  have h : ∀ q k,k+q≤r → (restStream F xs k q).count .stop=q := by
    intro q
    induction q with
    | zero => intro k hk; rfl
    | succ q ih =>
      intro k hk
      have hkr : k<r := by omega
      simp only [restStream,hkr,↓reduceDIte,List.count_append,batch_delimiter_count,ih (k+1) (by omega)]
      omega
  simp only [stream,List.count_append,batch_delimiter_count,h r 0 (by omega)]
  omega

theorem native_records (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    (∀ i : Fin (r+1),let rs:=RowEnumeration.rowsRecords (F i) xs n 0
      (∀ p : ℕ × ℕ,p ∈ rs.map RowEnumeration.decodePair ↔ ∃ u v : Fin n,v ∈ (F i).neighbors u ∧ p=(u.val,v.val)) ∧
      (rs.map RowEnumeration.decodePair).Nodup ∧
      (∀ p ∈ rs,p.1.length=2*n.size+PaddedWord.commonConstant (F i) ∧ p.2.length=2*n.size+PaddedWord.commonConstant (F i))) ∧
    stream F xs=(List.ofFn (fun i : Fin (r+1) =>
      symbols ((RowEnumeration.rowsRecords (F i) xs n 0).flatMap (fun p => p.1++p.2))++[.stop])).flatten ∧
    (stream F xs).count .stop=r+1 ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg .done (RawEnumeration.loaded w xs (stream F xs).reverse)
          (advance (fun _ => 0) (stream F xs).length) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg .done (RawEnumeration.loaded w xs (stream F xs).reverse)
        (advance (fun _ => 0) (stream F xs).length) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr,hstop⟩ := native_complete F w n hn hw
  subst n
  refine ⟨xs,hx,rfl,hl,?_,?_,stream_delimiter_count F xs,t,ht,htr,hstop⟩
  · intro i
    refine ⟨RowEnumeration.all_records_spec (F i) xs,RowEnumeration.rows_values_nodup (F i) xs _ _ (by omega),?_⟩
    have hm : (PaddedWord.word (PaddedWord.commonConstant (F i)) id xs).length=
        2*(Counter.value xs).size+PaddedWord.commonConstant (F i) := by rw [PaddedWord.word_length,hl]
    simpa only [hm] using RowEnumeration.rows_records_width (F i) xs (Counter.value xs) 0
  · simpa only [batch,RowEnumeration.rows_encoding] using stream_ofFn F xs

end TransposeFollowup.FamilyEnumeration


/-! Raw-input family generation followed by a paid rewind to the first
record symbol. This supplies a real tape interface for the field reader;
it does not yet interpret fields or deduplicate records. -/
namespace TransposeFollowup.FamilyReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

abbrev Port := FamilyEnumeration.Port
abbrev Bank := RawEnumeration.Bank
abbrev output := FamilyEnumeration.output

inductive Label (F : Fin (r+1) → RationalMobius)
  | generate (pc : FamilyEnumeration.Label F)
  | rewind (pc : NativeSpanRewind.Label)
  deriving DecidableEq,Fintype

def rewindBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => output,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=output then some 0 else none
  decode_spec:=by intro p j;fin_cases j;change (if p=output then some (0 : Fin 1) else none)=some 0 ↔ output=p;simp [eq_comm]

def start (F : Fin (r+1) → RationalMobius) : Label F := .generate (FamilyEnumeration.start F)

def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .generate .done => .work (.jump (.rewind .left))
  | .generate pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.generate (FamilyEnumeration.program F pc)
  | .rewind pc => .work (rewindBinding.instruction Label.rewind (NativeSpanRewind.program pc))

theorem generate_code (F : Fin (r+1) → RationalMobius) (pc : FamilyEnumeration.Label F)
    (hh : FamilyEnumeration.program F pc≠.work .halt) (_ : FamilyEnumeration.program F pc≠.work .reject) :
    program F (.generate pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.generate
      (FamilyEnumeration.program F pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem rewind_code (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (_ : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program F) (.rewind pc)=MicrocodeEmbedding.instruction rewindBinding.ports Label.rewind
      (NativeSpanRewind.program pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩

def readBank (w xs : List Bool) (syms : List (Sym Bool)) : Bank :=
  Function.update (RawEnumeration.loaded w xs []) output ⟨[],syms⟩

abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem stream_nonblank (F : Fin (r+1) → RationalMobius) (xs : List Bool) :
    ∀ s ∈ FamilyEnumeration.stream F xs,s≠.blank := by
  rw [FamilyEnumeration.stream_ofFn]
  intro s hs
  obtain ⟨b,hb,hs⟩ := List.mem_flatten.mp hs
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
  simp only [FamilyEnumeration.batch,List.mem_append,List.mem_singleton] at hs
  rcases hs with hs | rfl
  · obtain ⟨bit,_,rfl⟩ := List.mem_map.mp hs
    simp
  · simp

theorem length_le_time (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (t : ℕ)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (outRev : List Bool)
    (h : FamilyEnumeration.Trace F w t (FamilyEnumeration.cfg (FamilyEnumeration.start F) (RawEnumeration.initial pre) pos 0 outRev)
      (FamilyEnumeration.cfg .done (RawEnumeration.loaded w xs ((FamilyEnumeration.stream F xs).reverse++pre))
        (FamilyEnumeration.advance pos (FamilyEnumeration.stream F xs).length) w.length outRev)) :
    (FamilyEnumeration.stream F xs).length≤t := by
  have hp := (NativeHeadDisplacement.trace_bounds (FamilyEnumeration.program F) w h output).2
  simp only [FamilyEnumeration.cfg,FamilyEnumeration.workCfg,FamilyEnumeration.advance,output,ite_true] at hp
  omega

end TransposeFollowup.FamilyReader


namespace TransposeFollowup.FamilyReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem embed_generate (F : Fin (r+1) → RationalMobius) (pc : FamilyEnumeration.Label F)
    (s base : Bank) (pos framePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F))
      (FamilyEnumeration.cfg pc s pos ip outRev) (RawEnumeration.frame base framePos)=cfg (.generate pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed FamilyEnumeration.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed FamilyEnumeration.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem generate_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ FamilyEnumeration.coefficient F*w.length,
      (FamilyEnumeration.stream F xs).length≤t ∧ Trace F w t
        (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
        (cfg (.generate .done) (RawEnumeration.loaded w xs (FamilyEnumeration.stream F xs).reverse)
          (FamilyEnumeration.advance pos (FamilyEnumeration.stream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := FamilyEnumeration.complete_trace F w n hn hw [] pos outRev
  have hb := length_le_time F w xs t [] pos outRev htr
  have he := NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F))
    (FamilyEnumeration.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (generate_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,hb,by simpa only [embed_generate,List.append_nil,start] using he⟩

theorem embed_rewind (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : Bank) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed rewindBinding.ports (Label.rewind (F:=F)) (NativeSpanRewind.cfg pc word (fun _ => z)).denote
      (RawEnumeration.frame base pos)=
      workCfg (.rewind pc) (Function.update base output word) (Function.update pos output z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote workCfg RawEnumeration.frame
  simp only [← rewindBinding.values_eq_extend]
  congr 2 <;> funext p <;> by_cases hp : p=output
  all_goals simp [rewindBinding,FinitePortBinding.values,Function.update,hp]

theorem loaded_at_output (w xs : List Bool) (pre : List (Sym Bool)) :
    RawEnumeration.loaded w xs pre output=⟨pre,[]⟩ := rfl

theorem loaded_update (w xs : List Bool) (pre syms : List (Sym Bool)) :
    Function.update (RawEnumeration.loaded w xs pre) output ⟨[],syms⟩=readBank w xs syms := by
  funext p
  fin_cases p <;> rfl

theorem restored_positions (pos : Port → ℤ) (m : ℕ) :
    Function.update (FamilyEnumeration.advance pos m) output (pos output)=pos := by
  funext p
  by_cases hp : p=output <;> simp [Function.update,FamilyEnumeration.advance,hp]

theorem rewind_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (syms : List (Sym Bool))
    (h : ∀ s ∈ syms,s≠.blank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*syms.length+3, Trace F w t
      (cfg (.rewind .left) (RawEnumeration.loaded w xs syms.reverse) (FamilyEnumeration.advance pos syms.length) ip outRev)
      (cfg (.rewind .done) (readBank w xs syms) pos ip outRev) := by
  let adv := FamilyEnumeration.advance pos syms.length
  obtain ⟨t,ht,htr⟩ := NativeSpanRewind.rewind_trace syms h (fun _ => adv output)
  have he := MicrocodeEmbedding.trace_embed rewindBinding.ports (Label.rewind (F:=F)) NativeSpanRewind.program
    (NativeIO.workProgram (program F)) (RawEnumeration.frame (RawEnumeration.loaded w xs syms.reverse) adv)
    (rewind_code F) htr
  have hi : Function.update (RawEnumeration.loaded w xs syms.reverse) output ⟨syms.reverse,[]⟩=
      RawEnumeration.loaded w xs syms.reverse := by rw [← loaded_at_output w xs syms.reverse,Function.update_eq_self]
  have hz : adv output-syms.length=pos output := by simp [adv,FamilyEnumeration.advance]
  have hf : Function.update adv output (pos output)=pos := restored_positions pos syms.length
  refine ⟨t,ht,?_⟩
  simpa only [embed_rewind,hi,Function.update_eq_self,loaded_update,hz,hf,cfg]
    using NativeIO.lift_work_trace (program F) w ip outRev he

theorem jump_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ)
    (ip : ℤ) (outRev : List Bool) : Trace F w 1 (cfg (.generate .done) s pos ip outRev)
      (cfg (.rewind .left) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.FamilyReader


namespace TransposeFollowup.FamilyReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := 3*FamilyEnumeration.coefficient F+4

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length, Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.rewind .done) (readBank w xs (FamilyEnumeration.stream F xs)) pos w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,hs,ta⟩ := generate_call F w n hn hw pos outRev
  obtain ⟨b,hb,tb⟩ := rewind_call F w xs (FamilyEnumeration.stream F xs) (stream_nonblank F xs) pos w.length outRev
  have tj := jump_trace F w (RawEnumeration.loaded w xs (FamilyEnumeration.stream F xs).reverse)
    (FamilyEnumeration.advance pos (FamilyEnumeration.stream F xs).length) w.length outRev
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
        some ((cfg (.rewind .done) (readBank w xs (FamilyEnumeration.stream F xs)) (fun _ => 0) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w ((cfg (.rewind .done) (readBank w xs (FamilyEnumeration.stream F xs))
        (fun _ => 0) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw (fun _ => 0) []
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hi : (cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) := by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,NativeSpanRewind.program]

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
          (cfg (.rewind .done) (readBank w xs (FamilyEnumeration.stream F xs)) pos w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩ := complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ FamilyEnumeration.Label F ⊕ NativeSpanRewind.Label where
  toFun | .generate pc => .inl pc | .rewind pc => .inr pc
  invFun | .inl pc => .generate pc | .inr pc => .rewind pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1447+∑ i : Fin (r+1),FamilyEnumeration.seedStates (F i) ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum]
    have hs := (FamilyEnumeration.fixed_resources F).2.2.1
    change Fintype.card (FamilyEnumeration.Label F)-1+1=_ at hs
    have hp : 0<Fintype.card (FamilyEnumeration.Label F) := Fintype.card_pos_iff.mpr ⟨FamilyEnumeration.start F⟩
    have hr : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
    rw [hr]
    omega

end TransposeFollowup.FamilyReader
