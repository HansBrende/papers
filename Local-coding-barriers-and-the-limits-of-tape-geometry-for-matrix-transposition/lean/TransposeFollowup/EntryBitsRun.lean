import TransposeFollowup.NativeNonemptyWord
import TransposeFollowup.StoredWordLength
import TransposeFollowup.DimensionCandidateData

/-! Exact arithmetic behind the entry-bit loader. In particular, powers of
2 use size(N-1), not size(N); the N=1 case is represented by one zero bit
before its length is measured. -/
namespace TransposeFollowup.EntryBits
open FixedTapeCompiler
set_option autoImplicit false

theorem size_eq_log2 (n : ℕ) (hn : n≠0) : n.size=n.log2+1 := by
  have hl : n.log2<n.size:=Nat.lt_size.mpr (Nat.log2_self_le hn)
  have hu : n.size ≤ n.log2+1:=Nat.size_le.mpr ((Nat.log2_lt hn).mp (by omega))
  omega

theorem entryBits_eq (n : ℕ) : Transpose.entryBits n=max 1 (n-1).size := by
  by_cases h : n-1=0
  · simp [Transpose.entryBits,h]
  · rw [size_eq_log2 (n-1) h]
    simp [Transpose.entryBits]

theorem entryBits_le_word (xs : List Bool) (hx : 0<Counter.value xs) :
    Transpose.entryBits (Counter.value xs) ≤ xs.length := by
  have h1 : 1 ≤ xs.length := by cases xs <;> simp_all [Counter.value]
  have hv : (Counter.value xs).size ≤ xs.length:=Nat.size_le.mpr (by
    rw [NativeCounter.word_value];exact BinaryCarry.value_lt xs)
  have hs:=Nat.size_le_size (Nat.sub_le (Counter.value xs) 1)
  rw [entryBits_eq]
  exact max_le h1 (hs.trans hv)

theorem prepared_length (xs ys : List Bool) (hx : 0<Counter.value xs)
    (hl : ys.length=(Counter.value (Counter.decrement xs)).size) :
    (NativeNonemptyWord.word ys).length=Transpose.entryBits (Counter.value xs) := by
  have hd:=Counter.decrement_value xs (MeasuredWord.nonzero xs hx)
  have hv : Counter.value (Counter.decrement xs)=Counter.value xs-1 := by omega
  rw [NativeNonemptyWord.word_length,hl,hv,entryBits_eq]

end TransposeFollowup.EntryBits


/-! Fixed control for entryBits(N). Tape0 preserves the supplied dimension;
tapes1/2 are temporary and tape3 receives the measured entry-bit count.
All three additional tapes start blank. -/
namespace TransposeFollowup.EntryBits
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
abbrev Port:=Fin 4
abbrev Bank:=Port → Tape Bool

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun q => if q=p then some 0 else none
  decode_spec:=by
    intro q i
    change (if q=p then some 0 else none)=some i ↔ p=q
    fin_cases i
    by_cases h : q=p
    · subst q;simp
    · simp [h,Ne.symm h]

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![0,1],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else none
  decode_spec:=by intro p t;fin_cases p <;> fin_cases t <;> decide

def measureBinding : FinitePortBinding InputMeasure.Port Port where
  ports:=⟨![1,2,3],by decide +kernel⟩
  decode:=fun p => if p=1 then some 0 else if p=2 then some 1 else if p=3 then some 2 else none
  decode_spec:=by intro p t;fin_cases p <;> fin_cases t <;> decide

inductive Label
  | copy (pc : NativeMappedCopy.Label)
  | decrement (pc : Microcode.DecrementFamily.Label)
  | trim (pc : NativeTrim.Label)
  | ensure (pc : NativeNonemptyWord.Label)
  | measure (pc : InputMeasure.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label:=.copy (.init (.erase 0))

def program : Microcode.Program Port Label
  | .copy pc => if pc=.seal .done then .jump (.decrement 0)
      else copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .decrement pc => if pc=11 then .jump (.trim .scan)
      else (singleBinding 1).instruction Label.decrement (Microcode.DecrementFamily.program pc)
  | .trim pc => if pc=.done then .jump (.ensure .check)
      else (singleBinding 1).instruction Label.trim (NativeTrim.program pc)
  | .ensure pc => if pc=.done then .jump (.measure (.copy false (.init (.erase 0))))
      else (singleBinding 1).instruction Label.ensure (NativeNonemptyWord.program pc)
  | .measure pc => if pc=.done then .jump (.erase 2)
      else measureBinding.instruction Label.measure (NativeIO.workProgram InputMeasure.program pc)
  | .erase pc => if pc=0 then .jump .done
      else (singleBinding 1).instruction Label.erase (NativeErase.program pc)
  | .done => .halt

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem decrement_code (pc : Microcode.DecrementFamily.Label) (hh : Microcode.DecrementFamily.program pc≠.halt)
    (_ : Microcode.DecrementFamily.program pc≠.reject) :
    program (.decrement pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports Label.decrement (Microcode.DecrementFamily.program pc) := by
  have hp : pc≠11 := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem trim_code (pc : NativeTrim.Label) (hh : NativeTrim.program pc≠.halt) (_ : NativeTrim.program pc≠.reject) :
    program (.trim pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports Label.trim (NativeTrim.program pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem ensure_code (pc : NativeNonemptyWord.Label) (hh : NativeNonemptyWord.program pc≠.halt)
    (_ : NativeNonemptyWord.program pc≠.reject) :
    program (.ensure pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports Label.ensure (NativeNonemptyWord.program pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem measure_code (pc : InputMeasure.Label) (hh : NativeIO.workProgram InputMeasure.program pc≠.halt)
    (_ : NativeIO.workProgram InputMeasure.program pc≠.reject) :
    program (.measure pc)=MicrocodeEmbedding.instruction measureBinding.ports Label.measure (NativeIO.workProgram InputMeasure.program pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction (singleBinding 1).ports Label.erase (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label:=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port:=⟨fun p => (s p).denote,pos⟩
def bank (source work tally output : Tape Bool) : Bank:=![source,work,tally,output]
def initial (xs : List Bool) : Bank:=bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ ⟨[],[]⟩
def working (xs ys : List Bool) : Bank:=bank (Counter.marked xs) (Counter.marked ys) ⟨[],[]⟩ ⟨[],[]⟩
def measured (xs ys : List Bool) : Bank:=bank (Counter.marked xs) (Counter.marked ys) ⟨[],[]⟩
  (Counter.marked (MeasuredWord.result ys.length))
def final (xs : List Bool) : Bank:=bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩
  (Counter.marked (MeasuredWord.result (Transpose.entryBits (Counter.value xs))))

abbrev Trace:=OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
noncomputable def nativeEncoding:=NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine:=NativeMicrocode.machine nativeEncoding program

end TransposeFollowup.EntryBits


/-! Exact framed calls for entry-bit calculation. Original dimension and
unused work tapes are preserved; all source heads return after each call. -/
namespace TransposeFollowup.EntryBits
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_copy (pc : NativeMappedCopy.Label) (source target : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc source target (fun p => pos (copyBinding.ports p))) (frame s pos)=
      cfg (.copy pc) (Function.update (Function.update s 0 source) 1 target) pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg frame cfg
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_decrement (pc : Microcode.DecrementFamily.Label) (xs : List Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports Label.decrement
      (NativeCounter.cfg pc xs (fun _ => pos 1)).denote (frame s pos)=
      cfg (.decrement pc) (Function.update s 1 (Counter.marked xs)) pos := by
  unfold MicrocodeEmbedding.embed NativeCounter.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus frame cfg
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_trim (pc : NativeTrim.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports Label.trim
      (NativeTrim.cfg pc word (fun _ => pos 1)).denote (frame s pos)=
      cfg (.trim pc) (Function.update s 1 word) pos := by
  unfold MicrocodeEmbedding.embed NativeTrim.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_ensure (pc : NativeNonemptyWord.Label) (xs : List Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports Label.ensure
      (NativeNonemptyWord.cfg pc xs (fun _ => pos 1)).denote (frame s pos)=
      cfg (.ensure pc) (Function.update s 1 (Counter.marked xs)) pos := by
  unfold MicrocodeEmbedding.embed NativeNonemptyWord.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_measure (pc : InputMeasure.Label) (s : InputMeasure.Bank) (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed measureBinding.ports Label.measure
      (InputMeasure.workCfg pc s (fun p => pos (measureBinding.ports p))) (frame base pos)=
      cfg (.measure pc) (measureBinding.values s base) pos := by
  unfold MicrocodeEmbedding.embed InputMeasure.workCfg frame cfg
  simp only [← measureBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_erase (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding 1).ports Label.erase
      (NativeErase.cfg pc word (fun _ => pos 1)).denote (frame s pos)=
      cfg (.erase pc) (Function.update s 1 word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus frame cfg
  simp only [← (singleBinding 1).values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ) (h : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem copy_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*xs.length+14,Trace t (cfg start (initial xs) pos)
      (cfg (.copy (.seal .done)) (working xs xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeMappedCopy.copy_trace id xs (fun p => pos (copyBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy (NativeMappedCopy.program id)
    program (frame (initial xs) pos) copy_code htr
  have hi : Function.update (Function.update (initial xs) 0 (Counter.marked xs)) 1 ⟨[],[]⟩=initial xs := by
    funext p;fin_cases p <;> rfl
  have hf : Function.update (Function.update (initial xs) 0 (Counter.marked xs)) 1 (Counter.marked xs)=working xs xs := by
    funext p;fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_copy,List.map_id,hi,hf,start] using he⟩

theorem decrement_call (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ 4*xs.length+8,Trace t (cfg (.decrement 0) (working xs xs) pos)
      (cfg (.decrement 11) (working xs (Counter.decrement xs)) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeCounter.decrement_trace xs (fun _ => pos 1)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 1).ports Label.decrement Microcode.DecrementFamily.program
    program (frame (working xs xs) pos) decrement_code htr
  have hc:=NativeCounter.native_sequence_budget 1 xs
  simp only [Counter.totalCost,Nat.add_zero] at hc
  have hi : Function.update (working xs xs) 1 (Counter.marked xs)=working xs xs := Function.update_eq_self _ _
  have hf : Function.update (working xs xs) 1 (Counter.marked (Counter.decrement xs))=working xs (Counter.decrement xs) := by
    funext p;fin_cases p <;> rfl
  exact ⟨t,by omega,by simpa only [embed_decrement,NativeCounter.returnLabel,MeasuredWord.nonzero xs hx,
    Bool.false_eq_true,ite_false,hi,hf] using he⟩

theorem trim_call (xs ys : List Bool) (pos : Port → ℤ) :
    ∃ zs,NativeTrim.Normalized zs ∧ Counter.value zs=Counter.value ys ∧ zs.length=(Counter.value ys).size ∧
      ∃ t ≤ 4*ys.length+10,Trace t (cfg (.trim .scan) (working xs ys) pos)
        (cfg (.trim .done) (working xs zs) pos) := by
  obtain ⟨zs,hz,hv,hl,t,ht,htr⟩:=NativeTrim.complete_trace ys (fun _ => pos 1)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 1).ports Label.trim NativeTrim.program
    program (frame (working xs ys) pos) trim_code htr
  have hi : Function.update (working xs ys) 1 (Counter.marked ys)=working xs ys := Function.update_eq_self _ _
  have hf : Function.update (working xs ys) 1 (Counter.marked zs)=working xs zs := by
    funext p;fin_cases p <;> rfl
  exact ⟨zs,hz,hv,hl,t,ht,by simpa only [embed_trim,hi,hf] using he⟩

theorem ensure_call (xs ys : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 3,Trace t (cfg (.ensure .check) (working xs ys) pos)
      (cfg (.ensure .done) (working xs (NativeNonemptyWord.word ys)) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeNonemptyWord.complete_trace ys (fun _ => pos 1)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 1).ports Label.ensure NativeNonemptyWord.program
    program (frame (working xs ys) pos) ensure_code htr
  have hi : Function.update (working xs ys) 1 (Counter.marked ys)=working xs ys := Function.update_eq_self _ _
  have hf : Function.update (working xs ys) 1 (Counter.marked (NativeNonemptyWord.word ys))=working xs (NativeNonemptyWord.word ys) := by
    funext p;fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_ensure,hi,hf] using he⟩

theorem measure_call (xs ys : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 32*ys.length+42,Trace t
      (cfg (.measure (.copy false (.init (.erase 0)))) (working xs ys) pos)
      (cfg (.measure .done) (measured xs ys) pos) := by
  obtain ⟨t,ht,htr⟩:=InputMeasure.stored_length_trace ys (fun p => pos (measureBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed measureBinding.ports Label.measure (NativeIO.workProgram InputMeasure.program)
    program (frame (working xs ys) pos) measure_code htr
  have hi : measureBinding.values (InputMeasure.loaded ys) (working xs ys)=working xs ys := by
    funext p;fin_cases p <;> rfl
  have hf : measureBinding.values (InputMeasure.final ys) (working xs ys)=measured xs ys := by
    funext p;fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [embed_measure,hi,hf] using he⟩

theorem erase_call (xs ys : List Bool) (hl : ys.length=Transpose.entryBits (Counter.value xs)) (pos : Port → ℤ) :
    ∃ t ≤ 4*ys.length+4,Trace t (cfg (.erase 2) (measured xs ys) pos)
      (cfg (.erase 0) (final xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeErase.erase_trace ys (fun _ => pos 1)
  have he:=MicrocodeEmbedding.trace_embed (singleBinding 1).ports Label.erase NativeErase.program
    program (frame (measured xs ys) pos) erase_code htr
  have hi : Function.update (measured xs ys) 1 (Counter.marked ys)=measured xs ys := Function.update_eq_self _ _
  have hf : Function.update (measured xs ys) 1 (⟨[],[]⟩:Tape Bool)=final xs := by
    funext p;fin_cases p <;> simp [measured,final,bank,hl]
  exact ⟨t,ht,by simpa only [embed_erase,hi,hf] using he⟩

end TransposeFollowup.EntryBits


/-! The complete paid entry-bit loader. A positive dimension word is the
only prepared work input. All three additional tapes start blank; the two
temporary tapes end blank and every absolute head is restored. -/
namespace TransposeFollowup.EntryBits
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem complete_trace (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ 50*xs.length+87,Trace t (cfg start (initial xs) pos) (cfg .done (final xs) pos) := by
  obtain ⟨a,ha,ta⟩:=copy_call xs pos
  have ja:=jump_trace (.copy (.seal .done)) (.decrement 0) (working xs xs) pos rfl
  obtain ⟨b,hb,tb⟩:=decrement_call xs hx pos
  have jb:=jump_trace (.decrement 11) (.trim .scan) (working xs (Counter.decrement xs)) pos rfl
  obtain ⟨ys,_,_,hl,c,hc,tc⟩:=trim_call xs (Counter.decrement xs) pos
  have jc:=jump_trace (.trim .done) (.ensure .check) (working xs ys) pos rfl
  obtain ⟨d,hd,td⟩:=ensure_call xs ys pos
  let zs:=NativeNonemptyWord.word ys
  have hz : zs.length=Transpose.entryBits (Counter.value xs):=prepared_length xs ys hx hl
  have jd:=jump_trace (.ensure .done) (.measure (.copy false (.init (.erase 0)))) (working xs zs) pos rfl
  obtain ⟨e,he,te⟩:=measure_call xs zs pos
  have je:=jump_trace (.measure .done) (.erase 2) (measured xs zs) pos rfl
  obtain ⟨f,hf,tf⟩:=erase_call xs zs hz pos
  have jf:=jump_trace (.erase 0) .done (final xs) pos rfl
  refine ⟨a+(1+(b+(1+(c+(1+(d+(1+(e+(1+(f+1)))))))))),?_,?_⟩
  · have hbnd:=entryBits_le_word xs hx
    simp only [Counter.length_decrement] at hc
    rw [hz] at he hf
    omega
  · exact NativeCountedLoop.trace_trans ta (NativeCountedLoop.trace_trans ja
      (NativeCountedLoop.trace_trans tb (NativeCountedLoop.trace_trans jb
        (NativeCountedLoop.trace_trans tc (NativeCountedLoop.trace_trans jc
          (NativeCountedLoop.trace_trans td (NativeCountedLoop.trace_trans jd
            (NativeCountedLoop.trace_trans te (NativeCountedLoop.trace_trans je
              (NativeCountedLoop.trace_trans tf jf))))))))))

theorem native_entryBits (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 50*xs.length+87,
      Transpose.stepN nativeMachine input t ((cfg start (initial xs) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done (final xs) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input ((cfg .done (final xs) pos).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩:=complete_trace xs hx pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem fixed_resources : nativeMachine.k=4 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=165 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=165
  decide +kernel

theorem output_contract (xs : List Bool) (hx : 0<Counter.value xs) :
    ∃ ys,Counter.value ys=Transpose.entryBits (Counter.value xs) ∧
      ys.length=Transpose.entryBits (Counter.value xs) ∧ ys.length ≤ xs.length ∧
      final xs=bank (Counter.marked xs) ⟨[],[]⟩ ⟨[],[]⟩ (Counter.marked ys) := by
  refine ⟨MeasuredWord.result (Transpose.entryBits (Counter.value xs)),MeasuredWord.result_value _,
    MeasuredWord.result_length _,?_,rfl⟩
  rw [MeasuredWord.result_length]
  exact entryBits_le_word xs hx

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : Microcode.Program U J)
    (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 50*xs.length+87,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (initial xs) pos) outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final xs) pos) outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩:=complete_trace xs hx pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.EntryBits
