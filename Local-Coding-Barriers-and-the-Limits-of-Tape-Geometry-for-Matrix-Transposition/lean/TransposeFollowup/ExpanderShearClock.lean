import TransposeFollowup.ExpanderShearClockProduct

/-! A fixed eleven-tape controller computes the exact unary row width
`d * entryBits d` from a marked dimension. The source dimension is retained;
all scratch is blank on return and every head is restored. -/
namespace TransposeFollowup.ExpanderShearClock
open FixedTapeCompiler CopyMachine RadiusBuilder
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Port := RadiusBuilder.Port
abbrev Bank := RadiusBuilder.Bank

def fillBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.product,.result],by decide +kernel⟩
  decode := fun p => match p with | .product => some 0 | .result => some 1 | _ => none
  decode_spec := by intro p t; cases p <;> fin_cases t <;> decide +kernel

inductive Label
  | build (pc : ExpanderShearClockProduct.Label)
  | init (pc : NativeBuffer.Label)
  | fill (pc : CountedFill.Label 1)
  | seal (pc : NativeSealBack.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .build ExpanderShearClockProduct.start

def program : Microcode.Program Port Label
  | .build .done => .jump (.init (.erase 0))
  | .build pc => identityBinding.instruction Label.build (ExpanderShearClockProduct.program pc)
  | .init .done => .jump (.fill (.counter 0))
  | .init pc => (singleBinding .result).instruction Label.init (NativeBuffer.program pc)
  | .fill (.counter pc) => if pc=12 then .jump (.seal .seal)
      else fillBinding.instruction Label.fill (CountedFill.program 1 true (.counter pc))
  | .fill pc => fillBinding.instruction Label.fill (CountedFill.program 1 true pc)
  | .seal .done => .jump (.erase 2)
  | .seal pc => (singleBinding .result).instruction Label.seal (NativeSealBack.program pc)
  | .erase pc => if pc=0 then .jump .done
      else (singleBinding .product).instruction Label.erase (NativeErase.program pc)
  | .done => .halt

theorem build_code (pc : ExpanderShearClockProduct.Label)
    (hh : ExpanderShearClockProduct.program pc ≠ .halt)
    (_ : ExpanderShearClockProduct.program pc ≠ .reject) :
    program (.build pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.build
      (ExpanderShearClockProduct.program pc) := by
  cases pc <;> simp_all [program,ExpanderShearClockProduct.program,FinitePortBinding.instruction_eq]

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc ≠ .halt)
    (_ : NativeBuffer.program pc ≠ .reject) :
    program (.init pc)=MicrocodeEmbedding.instruction (singleBinding .result).ports Label.init
      (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem fill_code (pc : CountedFill.Label 1) (hh : CountedFill.program 1 true pc ≠ .halt)
    (_ : CountedFill.program 1 true pc ≠ .reject) :
    program (.fill pc)=MicrocodeEmbedding.instruction fillBinding.ports Label.fill
      (CountedFill.program 1 true pc) := by
  have hp : pc ≠ .counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem seal_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc ≠ .halt)
    (_ : NativeSealBack.program pc ≠ .reject) :
    program (.seal pc)=MicrocodeEmbedding.instruction (singleBinding .result).ports Label.seal
      (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeErase.Label) (hh : NativeErase.program pc ≠ .halt)
    (_ : NativeErase.program pc ≠ .reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction (singleBinding .product).ports Label.erase
      (NativeErase.program pc) := by
  have hp : pc ≠ 0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

def word (xs : List Bool) : List Bool :=
  List.replicate (Counter.value xs * Transpose.entryBits (Counter.value xs)) true

def work (xs fuel : List Bool) (out : Tape Bool) : Bank
  | .source => Counter.marked xs | .product => Counter.marked fuel
  | .result => out | _ => ⟨[],[]⟩

def final (xs : List Bool) : Bank
  | .source => Counter.marked xs | .result => Counter.marked (word xs) | _ => ⟨[],[]⟩

def positions (origin : Port → ℤ) (acc : List Bool) (p : Port) : ℤ :=
  origin p + if p=.result then (acc.length : ℤ) else 0

def budget (xs : List Bool) : ℕ := RadiusBuilder.budget 0 xs +
  13 * (Counter.value xs * Transpose.entryBits (Counter.value xs)) + 8 * width 0 xs + 32

theorem embed_bank {U J : Type*} (binding : FinitePortBinding U Port)
    (labels : J → Label) (pc : J) (inner : U → Tape Bool) (outer : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed binding.ports labels
      (⟨⟨pc,fun p => (inner p).denote⟩,fun p => pos (binding.ports p)⟩ : NativeMicrocode.Config U J)
      (frame outer pos)=cfg (labels pc) (binding.values inner outer) pos := by
  exact binding.embed_bank_project _ _ _ _ _

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem build_call (xs : List Bool) (hx : 0 < Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ RadiusBuilder.budget 0 xs, Trace t
      (cfg start (RadiusBuilder.initial xs) pos)
      (cfg (.build .done) (work xs (product 0 xs) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := ExpanderShearClockProduct.complete_trace xs hx pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports Label.build
    ExpanderShearClockProduct.program program (frame (RadiusBuilder.initial xs) pos) build_code htr
  have hf : ExpanderShearClockProduct.final xs=work xs (product 0 xs) ⟨[],[]⟩ := by
    funext p; cases p <;> rfl
  have hi := embed_bank identityBinding Label.build ExpanderShearClockProduct.start
    (RadiusBuilder.initial xs) (RadiusBuilder.initial xs) pos
  have ho := embed_bank identityBinding Label.build ExpanderShearClockProduct.Label.done
    (ExpanderShearClockProduct.final xs) (RadiusBuilder.initial xs) pos
  change MicrocodeEmbedding.embed _ _ (ExpanderShearClockProduct.cfg _ _ _) _ = _ at hi ho
  have hpos : (fun p => pos (identityBinding.ports p))=pos := rfl
  rw [hpos] at hi ho
  exact ⟨t,ht,by rw [hi,ho] at he; simpa only [hf,start,
    show ∀ b : Bank, identityBinding.values b (RadiusBuilder.initial xs)=b from fun _ => rfl] using he⟩

private theorem single_focus (t : Tape Bool) :
    (Function.update (fun _ : Fin 1 => (⟨[],[]⟩ : Tape Bool)) 0 t) = fun _ => t := by
  funext i; fin_cases i; rfl

theorem init_call (xs fuel : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace t (cfg (.init (.erase 0)) (work xs fuel ⟨[],[]⟩) pos)
      (cfg (.init .done) (work xs fuel (NativeSealBack.openWord [])) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos .result)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .result).ports Label.init
    NativeBuffer.program program (frame (work xs fuel ⟨[],[]⟩) pos) init_code htr
  have hi : (singleBinding .result).values (fun _ => (⟨[],[]⟩ : Tape Bool))
      (work xs fuel ⟨[],[]⟩)=work xs fuel ⟨[],[]⟩ := by funext p; cases p <;> rfl
  have hf : (singleBinding .result).values (fun _ => BinaryCarry.preparedOutput)
      (work xs fuel ⟨[],[]⟩)=work xs fuel (NativeSealBack.openWord []) := by funext p; cases p <;> rfl
  have ei := embed_bank (singleBinding .result) Label.init (NativeBuffer.Label.erase 0)
    (fun _ => (⟨[],[]⟩ : Tape Bool)) (work xs fuel ⟨[],[]⟩) pos
  have ef := embed_bank (singleBinding .result) Label.init NativeBuffer.Label.done
    (fun _ => BinaryCarry.preparedOutput) (work xs fuel ⟨[],[]⟩) pos
  have hpos : (fun p => pos ((singleBinding .result).ports p))=(fun _ => pos .result) := rfl
  rw [hpos,hi] at ei
  rw [hpos,hf] at ef
  exact ⟨t,ht,by simpa only [NativeBuffer.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus,single_focus,ei,ef] using he⟩

theorem embed_fill (pc : CountedFill.Label 1) (xs fuel acc : List Bool) (origin : Port → ℤ) :
    MicrocodeEmbedding.embed fillBinding.ports Label.fill
      (CountedFill.cfg pc fuel acc (fun p => origin (fillBinding.ports p))).denote
      (frame (RadiusBuilder.initial xs) origin)=
      cfg (.fill pc) (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc) := by
  unfold MicrocodeEmbedding.embed CountedFill.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [←fillBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;>
    simp [fillBinding,FinitePortBinding.values,CountedFill.bank,CountedFill.positions,positions,
      RadiusBuilder.initial,work]

theorem fill_call (xs fuel acc : List Bool) (origin : Port → ℤ) :
    ∃ t ≤ 11 * Counter.value fuel + 8 + 4*fuel.length, Trace t
      (cfg (.fill (.counter 0)) (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc))
      (cfg (.fill (.counter 12))
        (work xs (List.replicate fuel.length true)
          (NativeSealBack.openWord (acc ++ List.replicate (Counter.value fuel) true)))
        (positions origin (acc ++ List.replicate (Counter.value fuel) true))) := by
  obtain ⟨t,ht,htr⟩ := CountedFill.fill_trace 1 true fuel acc (fun p => origin (fillBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed fillBinding.ports Label.fill
    (CountedFill.program 1 true) program (frame (RadiusBuilder.initial xs) origin) fill_code htr
  exact ⟨t,by omega,by simpa only [Nat.mul_one,embed_fill] using he⟩

theorem seal_call (xs fuel acc : List Bool) (origin : Port → ℤ) :
    ∃ t ≤ 2*acc.length+5, Trace t
      (cfg (.seal .seal) (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc))
      (cfg (.seal .done) (work xs fuel (Counter.marked acc)) origin) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace acc (fun _ => positions origin acc .result)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .result).ports Label.seal
    NativeSealBack.program program (frame (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc))
    seal_code htr
  have h₀ : MicrocodeEmbedding.embed (singleBinding .result).ports Label.seal
      (NativeSealBack.cfg .seal (NativeSealBack.openWord acc) (fun _ => positions origin acc .result)).denote
      (frame (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc))=
      cfg (.seal .seal) (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc) := by
    unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [←(singleBinding .result).values_eq_extend]
    congr 2 <;> funext p <;> cases p <;> rfl
  have h₁ : MicrocodeEmbedding.embed (singleBinding .result).ports Label.seal
      (NativeSealBack.cfg .done (Counter.marked acc)
        (fun _ => positions origin acc .result-acc.length)).denote
      (frame (work xs fuel (NativeSealBack.openWord acc)) (positions origin acc))=
      cfg (.seal .done) (work xs fuel (Counter.marked acc)) origin := by
    unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [←(singleBinding .result).values_eq_extend]
    congr 2 <;> funext p <;> cases p <;>
      simp [singleBinding,FinitePortBinding.values,work,positions]
  exact ⟨t,ht,by simpa only [h₀,h₁] using he⟩

theorem erase_call (xs fuel : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*fuel.length+4, Trace t
      (cfg (.erase 2) (work xs fuel (Counter.marked (word xs))) pos)
      (cfg (.erase 0) (final xs) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace fuel (fun _ => pos .product)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .product).ports Label.erase
    NativeErase.program program (frame (work xs fuel (Counter.marked (word xs))) pos) erase_code htr
  have hi : (singleBinding .product).values (fun _ => Counter.marked fuel)
      (work xs fuel (Counter.marked (word xs)))=work xs fuel (Counter.marked (word xs)) := by
    funext p; cases p <;> rfl
  have hf : (singleBinding .product).values (fun _ => (⟨[],[]⟩ : Tape Bool))
      (work xs fuel (Counter.marked (word xs)))=final xs := by funext p; cases p <;> rfl
  have ei := embed_bank (singleBinding .product) Label.erase (2 : NativeErase.Label)
    (fun _ => Counter.marked fuel) (work xs fuel (Counter.marked (word xs))) pos
  have ef := embed_bank (singleBinding .product) Label.erase (0 : NativeErase.Label)
    (fun _ => (⟨[],[]⟩ : Tape Bool)) (work xs fuel (Counter.marked (word xs))) pos
  have hpos : (fun p => pos ((singleBinding .product).ports p))=(fun _ => pos .product) := rfl
  rw [hpos,hi] at ei
  rw [hpos,hf] at ef
  exact ⟨t,ht,by simpa only [NativeErase.cfg,NativeZipper.Config.denote,Microcode.Config.denote,
    Microcode.focus,single_focus,ei,ef] using he⟩

theorem complete_trace (xs : List Bool) (hx : 0 < Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ budget xs, Trace t (cfg start (RadiusBuilder.initial xs) pos) (cfg .done (final xs) pos) := by
  obtain ⟨a,ha,ta⟩ := build_call xs hx pos
  have ja := jump_trace (.build .done) (.init (.erase 0)) (work xs (product 0 xs) ⟨[],[]⟩) pos rfl
  obtain ⟨b,hb,tb⟩ := init_call xs (product 0 xs) pos
  have jb := jump_trace (.init .done) (.fill (.counter 0))
    (work xs (product 0 xs) (NativeSealBack.openWord [])) pos rfl
  obtain ⟨c,hc,tc⟩ := fill_call xs (product 0 xs) [] pos
  have hp : positions pos []=pos := by funext p; simp [positions]
  have hw : [] ++ List.replicate (Counter.value (product 0 xs)) true=word xs := by
    simp [word,product_value 0 xs hx]
  rw [hp,hw] at tc
  have jc := jump_trace (.fill (.counter 12)) (.seal .seal)
    (work xs (List.replicate (product 0 xs).length true) (NativeSealBack.openWord (word xs)))
    (positions pos (word xs)) rfl
  obtain ⟨e,he,te⟩ := seal_call xs (List.replicate (product 0 xs).length true) (word xs) pos
  have je := jump_trace (.seal .done) (.erase 2)
    (work xs (List.replicate (product 0 xs).length true) (Counter.marked (word xs))) pos rfl
  obtain ⟨f,hf,tf⟩ := erase_call xs (List.replicate (product 0 xs).length true) pos
  have jf := jump_trace (.erase 0) .done (final xs) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb (trace_trans tc
    (trace_trans jc (trace_trans te (trace_trans je (trace_trans tf jf))))))))⟩
  simp only [word,List.length_replicate,product_length,product_value 0 xs hx] at hc he hf
  unfold budget
  omega

theorem budget_linear (xs : List Bool) (hx : 0 < Counter.value xs)
    (hl : xs.length ≤ Counter.value xs) :
    budget xs ≤ 1200 * (Counter.value xs * Transpose.entryBits (Counter.value xs)) := by
  have hr := RadiusBuilder.budget_linear 0 xs hx hl
  have hb : 1 ≤ Transpose.entryBits (Counter.value xs) := by rw [EntryBits.entryBits_eq]; omega
  have hp : 1 ≤ Counter.value xs * Transpose.entryBits (Counter.value xs) := by nlinarith
  have hd : Counter.value xs ≤ Counter.value xs * Transpose.entryBits (Counter.value xs) := by nlinarith
  have hw : width 0 xs ≤ 6 * (Counter.value xs * Transpose.entryBits (Counter.value xs)) := by
    norm_num [width,padding]
    nlinarith
  norm_num [RadiusBuilder.linearConstant,RadiusBuilder.padding] at hr
  unfold budget
  nlinarith

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (hx : 0 < Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (RadiusBuilder.initial xs) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final xs) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace xs hx pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

@[simp] theorem final_source (xs : List Bool) : final xs .source=Counter.marked xs := rfl
@[simp] theorem final_result (xs : List Bool) : final xs .result=Counter.marked (word xs) := rfl
@[simp] theorem word_length (xs : List Bool) :
    (word xs).length=Counter.value xs * Transpose.entryBits (Counter.value xs) := by simp [word]

theorem final_other (xs : List Bool) (p : Port) (h₁ : p ≠ .source) (h₂ : p ≠ .result) :
    final xs p=⟨[],[]⟩ := by cases p <;> simp_all [final]

theorem fixed_resources : nativeMachine.k=11 ∧ nativeMachine.g+1=5 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Port=11
  decide +kernel

end TransposeFollowup.ExpanderShearClock
