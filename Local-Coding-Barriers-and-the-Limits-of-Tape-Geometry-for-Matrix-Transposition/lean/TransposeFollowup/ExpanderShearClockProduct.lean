import TransposeFollowup.RadiusClockRun

/-! Exact binary word width from a retained dimension. This reuses the
verified entry-width and multiplication routines, with a shorter caller
that omits radius rounding. Every auxiliary tape is cleared. -/
namespace TransposeFollowup.ExpanderShearClockProduct
open FixedTapeCompiler CopyMachine RadiusBuilder
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Port := RadiusBuilder.Port
abbrev Bank := RadiusBuilder.Bank

def erasePorts : Fin 6 ↪ Port := ⟨![.bits,.result,.number,.zero,.one,.fuel], by decide +kernel⟩

inductive Label
  | entry (pc : EntryBits.Label)
  | seed (pc : ArithmeticSeed.Label (padding 0))
  | scale (pc : DimensionScale.Label)
  | erase (pc : NativeBatchErase.Label 6)
  | clear (right : Bool) (pc : NativeUnprepare.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .entry EntryBits.start

def program : Microcode.Program Port Label
  | .entry .done => .jump (.seed (.pad false (.init (.erase 0))))
  | .entry pc => entryBinding.instruction Label.entry (EntryBits.program pc)
  | .seed .done => .jump (.scale DimensionScale.start)
  | .seed pc => seedBinding.instruction Label.seed (ArithmeticSeed.program (padding 0) pc)
  | .scale .done => .jump (.erase (NativeBatchErase.entry 6 0))
  | .scale pc => scaleBinding.instruction Label.scale (DimensionScale.program pc)
  | .erase .done => .jump (.clear false 0)
  | .erase pc => identityBinding.instruction Label.erase (NativeBatchErase.program erasePorts pc)
  | .clear r pc => if pc=2 then .jump (if r then .done else .clear true 0)
      else (singleBinding (if r then .right else .left)).instruction (Label.clear r) (NativeUnprepare.program pc)
  | .done => .halt

theorem entry_code (pc : EntryBits.Label) (hh : EntryBits.program pc≠.halt)
    (_ : EntryBits.program pc≠.reject) :
    program (.entry pc)=MicrocodeEmbedding.instruction entryBinding.ports Label.entry (EntryBits.program pc) := by
  cases pc <;> simp_all [program,EntryBits.program,FinitePortBinding.instruction_eq]

theorem seed_code (pc : ArithmeticSeed.Label (padding 0)) (hh : ArithmeticSeed.program (padding 0) pc≠.halt)
    (_ : ArithmeticSeed.program (padding 0) pc≠.reject) :
    program (.seed pc)=MicrocodeEmbedding.instruction seedBinding.ports Label.seed (ArithmeticSeed.program (padding 0) pc) := by
  cases pc <;> simp_all [program,ArithmeticSeed.program,FinitePortBinding.instruction_eq]

theorem scale_code (pc : DimensionScale.Label) (hh : DimensionScale.program pc≠.halt)
    (_ : DimensionScale.program pc≠.reject) :
    program (.scale pc)=MicrocodeEmbedding.instruction scaleBinding.ports Label.scale (DimensionScale.program pc) := by
  cases pc <;> simp_all [program,DimensionScale.program,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeBatchErase.Label 6) (hh : NativeBatchErase.program erasePorts pc≠.halt)
    (_ : NativeBatchErase.program erasePorts pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.erase (NativeBatchErase.program erasePorts pc) := by
  cases pc <;> simp_all [program,NativeBatchErase.program,FinitePortBinding.instruction_eq]

theorem clear_code (r : Bool) (pc : NativeUnprepare.Label)
    (hh : NativeUnprepare.program pc≠.halt) (_ : NativeUnprepare.program pc≠.reject) :
    program (.clear r pc)=MicrocodeEmbedding.instruction (singleBinding (if r then .right else .left)).ports
      (Label.clear r) (NativeUnprepare.program pc) := by
  have hp : pc≠2:=by intro h;subst pc;exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)
noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

def clean (xs : List Bool) : Bank
  | .source => Counter.marked xs | .product => Counter.marked (product 0 xs)
  | .left | .right => BinaryCarry.preparedOutput | _ => ⟨[],[]⟩
def halfClean (xs : List Bool) : Bank := Function.update (clean xs) .left ⟨[],[]⟩
def final (xs : List Bool) : Bank
  | .source => Counter.marked xs | .product => Counter.marked (product 0 xs) | _ => ⟨[],[]⟩
def eraseWords (xs : List Bool) : Fin 6 → List Bool :=
  ![bitWord xs,ArithmeticSeed.zeros (width 0 xs),factor 0 xs,
    ArithmeticSeed.zeros (width 0 xs),ArithmeticSeed.one (width 0 xs),[true]]
theorem erase_words (xs : List Bool) (j : Fin 6) :
    scaled 0 xs (erasePorts j)=Counter.marked (eraseWords xs j) := by fin_cases j <;> rfl

theorem erase_final (xs : List Bool) :
    NativeBatchErase.stage erasePorts (scaled 0 xs) 6=clean xs := by
  funext p
  cases p
  all_goals simp [NativeBatchErase.stage,erasePorts,Fin.exists_fin_succ,scaled,stage,clean]

theorem erase_budget (xs : List Bool) :
    (∑ j : Fin 6,(4*(eraseWords xs j).length+5))=
      4*Transpose.entryBits (Counter.value xs)+16*width 0 xs+34 := by
  simp only [Fin.sum_univ_succ,eraseWords,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,bitWord_length,factor_length,ArithmeticSeed.zeros,
    List.length_replicate,ArithmeticSeed.one_length _ (width_positive 0 xs),List.length_cons,List.length_nil]
  omega

theorem embed_bank {U J : Type*} (binding : FinitePortBinding U Port)
    (labels : J → Label) (pc : J) (inner : U → Tape Bool) (outer : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed binding.ports labels
      (⟨⟨pc,fun p => (inner p).denote⟩,fun p => pos (binding.ports p)⟩ : NativeMicrocode.Config U J)
      (frame outer pos)=cfg (labels pc) (binding.values inner outer) pos := by
  exact binding.embed_bank_project _ _ _ _ _

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem entry_call (xs : List Bool) (hx : 0<Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ 50*xs.length+87,Trace t (cfg (start) (RadiusBuilder.initial xs) pos)
      (cfg (.entry .done) (measured xs) pos) := by
  obtain ⟨t,ht,htr⟩:=EntryBits.complete_trace xs hx (fun p => pos (entryBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed entryBinding.ports Label.entry EntryBits.program
    (program) (frame (RadiusBuilder.initial xs) pos) (entry_code) htr
  have hi : entryBinding.values (EntryBits.initial xs) (RadiusBuilder.initial xs)=RadiusBuilder.initial xs:=by
    funext p;cases p <;> rfl
  have hf : entryBinding.values (EntryBits.final xs) (RadiusBuilder.initial xs)=measured xs:=by
    funext p;cases p <;> rfl
  exact ⟨t,ht,by simpa only [EntryBits.cfg,embed_bank,hi,hf,start] using he⟩

theorem seed_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 46*xs.length+17*padding 0+81,Trace t
      (cfg (.seed (.pad false (.init (.erase 0)))) (measured xs) pos)
      (cfg (.seed .done) (seeded 0 xs) pos) := by
  obtain ⟨t,ht,htr⟩:=ArithmeticSeed.seed_trace (padding 0) xs (width_positive 0 xs)
    (fun p => pos (seedBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed seedBinding.ports Label.seed (ArithmeticSeed.program (padding 0))
    (program) (frame (measured xs) pos) (seed_code) htr
  have hi : seedBinding.values (ArithmeticSeed.initial xs).tapes (measured xs)=measured xs:=by
    funext p;cases p <;> rfl
  have hf : seedBinding.values (ArithmeticSeed.ready (padding 0) xs).tapes (measured xs)=seeded 0 xs:=by
    funext p;cases p <;> rfl
  exact ⟨t,ht,by simpa only [ArithmeticSeed.cfg,embed_bank,hi,hf] using he⟩

theorem scale_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ Transpose.entryBits (Counter.value xs)*(18*width 0 xs+39)+
        14*Transpose.entryBits (Counter.value xs)+6*width 0 xs+44,
      Trace t (cfg (.scale DimensionScale.start) (seeded 0 xs) pos)
        (cfg (.scale .done) (scaled 0 xs) pos) := by
  obtain ⟨t,ht,htr⟩:=DimensionScale.complete_trace (bitWord xs) (factor 0 xs)
    (fun p => pos (scaleBinding.ports p))
  have he:=MicrocodeEmbedding.trace_embed scaleBinding.ports Label.scale DimensionScale.program
    (program) (frame (seeded 0 xs) pos) (scale_code) htr
  have hi : scaleBinding.values (DimensionScale.initial (bitWord xs) (factor 0 xs)).tapes (seeded 0 xs)=seeded 0 xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,scaleBinding,DimensionScale.initial,DimensionScale.Bank.tapes,
      seeded,stage,factor_length]
  have hf : scaleBinding.values (DimensionScale.final (bitWord xs) (factor 0 xs)).tapes (seeded 0 xs)=scaled 0 xs:=by
    funext p;cases p <;> simp [FinitePortBinding.values,scaleBinding,DimensionScale.final,DimensionScale.initial,
      DimensionScale.Bank.tapes,seeded,scaled,stage,product,factor_length]
  refine ⟨t,?_,by simpa only [DimensionScale.cfg,embed_bank,hi,hf] using he⟩
  simpa only [DimensionScale.budget_expansion,bitWord_value,bitWord_length,factor_length] using ht

theorem erase_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*Transpose.entryBits (Counter.value xs)+16*width 0 xs+34,Trace t
      (cfg (.erase (NativeBatchErase.entry 6 0)) (scaled 0 xs) pos)
      (cfg (.erase .done) (clean xs) pos) := by
  obtain ⟨t,ht,htr⟩:=NativeBatchErase.complete_trace erasePorts (eraseWords xs) (scaled 0 xs) (erase_words xs) pos
  have he:=MicrocodeEmbedding.trace_embed identityBinding.ports Label.erase (NativeBatchErase.program erasePorts)
    (program) (frame (scaled 0 xs) pos) (erase_code) htr
  have hi : identityBinding.values (scaled 0 xs) (scaled 0 xs)=scaled 0 xs:=rfl
  have hf : identityBinding.values (clean xs) (scaled 0 xs)=clean xs:=rfl
  change OperationalTrace.Trace _ _ t
    (MicrocodeEmbedding.embed identityBinding.ports Label.erase
      ⟨⟨NativeBatchErase.entry 6 0,fun p => (scaled 0 xs p).denote⟩,fun p => pos (identityBinding.ports p)⟩
      (frame (scaled 0 xs) pos))
    (MicrocodeEmbedding.embed identityBinding.ports Label.erase
      ⟨⟨NativeBatchErase.Label.done,fun p => (NativeBatchErase.stage erasePorts (scaled 0 xs) 6 p).denote⟩,
        fun p => pos (identityBinding.ports p)⟩ (frame (scaled 0 xs) pos)) at he
  exact ⟨t,by simpa only [erase_budget] using ht,
    by simpa only [NativeBatchErase.cfg,embed_bank,erase_final,hi,hf] using he⟩

theorem clear_call (r : Bool) (s : Bank) (pos : Port → ℤ)
    (hs : s (if r then .right else .left)=BinaryCarry.preparedOutput) :
    ∃ t ≤ 2,Trace t (cfg (.clear r 0) s pos)
      (cfg (.clear r 2) (Function.update s (if r then .right else .left) ⟨[],[]⟩) pos) := by
  let port : Port:=if r then .right else .left
  obtain ⟨t,ht,htr⟩:=NativeUnprepare.complete_trace (fun p => pos ((singleBinding port).ports p))
  have he:=MicrocodeEmbedding.trace_embed (singleBinding port).ports (Label.clear r) NativeUnprepare.program
    (program) (frame s pos) (clear_code r) htr
  have hi : (singleBinding port).values (fun _ => BinaryCarry.preparedOutput) s=s:=by
    funext p;by_cases h : p=port
    · subst p;simpa [FinitePortBinding.values,singleBinding] using hs.symm
    · simp [FinitePortBinding.values,singleBinding,h]
  have hf : (singleBinding port).values (fun _ => (⟨[],[]⟩ : Tape Bool)) s=Function.update s port ⟨[],[]⟩:=by
    funext p;by_cases h : p=port <;> simp [FinitePortBinding.values,singleBinding,Function.update,h]
  exact ⟨t,ht,by simpa only [NativeUnprepare.cfg,NativeZipper.Config.denote,Microcode.Config.denote,embed_bank,hi,hf] using he⟩


theorem complete_trace (xs : List Bool) (hx : 0 < Counter.value xs) (pos : Port → ℤ) :
    ∃ t ≤ RadiusBuilder.budget 0 xs, Trace t
      (cfg start (RadiusBuilder.initial xs) pos) (cfg .done (final xs) pos) := by
  obtain ⟨a,ha,ta⟩ := entry_call xs hx pos
  have ja := jump_trace (.entry .done) (.seed (.pad false (.init (.erase 0)))) (measured xs) pos rfl
  obtain ⟨b,hb,tb⟩ := seed_call xs pos
  have jb := jump_trace (.seed .done) (.scale DimensionScale.start) (seeded 0 xs) pos rfl
  obtain ⟨c,hc,tc⟩ := scale_call xs pos
  have jc := jump_trace (.scale .done) (.erase (NativeBatchErase.entry 6 0)) (scaled 0 xs) pos rfl
  obtain ⟨g,hg,tg⟩ := erase_call xs pos
  have jg := jump_trace (.erase .done) (.clear false 0) (clean xs) pos rfl
  obtain ⟨h,hh,th⟩ := clear_call false (clean xs) pos rfl
  change Trace h (cfg (.clear false 0) (clean xs) pos) (cfg (.clear false 2) (halfClean xs) pos) at th
  have jh := jump_trace (.clear false 2) (.clear true 0) (halfClean xs) pos rfl
  obtain ⟨i,hi,ti⟩ := clear_call true (halfClean xs) pos rfl
  have hend : Function.update (halfClean xs) .right ⟨[],[]⟩=final xs := by funext p; cases p <;> rfl
  rw [show (if true then Port.right else Port.left)=Port.right from rfl,hend] at ti
  have ji := jump_trace (.clear true 2) .done (final xs) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb (trace_trans tc
    (trace_trans jc (trace_trans tg (trace_trans jg (trace_trans th (trace_trans jh (trace_trans ti ji))))))))))⟩
  unfold RadiusBuilder.budget
  nlinarith

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc, program pc ≠ .halt → program pc ≠ .reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (hx : 0 < Counter.value xs) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ RadiusBuilder.budget 0 xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (RadiusBuilder.initial xs) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final xs) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace xs hx pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.ExpanderShearClockProduct
