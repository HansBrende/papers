import TransposeFollowup.RawNormalizationMeaning
import TransposeFollowup.FamilySelectorMeaning
import TransposeFollowup.PortBindingFrame
import TransposeFollowup.SeedMultipleMeaning

/-! Return the normalized stream under its first-symbol head. The raw
stream remains stored at its end head;all other work heads are restored. -/
namespace TransposeFollowup.NormalizedReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := RawNormalization.Port
abbrev Bank := RawNormalization.Bank
abbrev output := RawNormalization.output

inductive Label (F : Fin (r+1) → RationalMobius)
  | generate (pc : RawNormalization.Label F)
  | rewind (pc : NativeSpanRewind.Label)
  deriving DecidableEq,Fintype

def rewindBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => output,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=output then some 0 else none
  decode_spec:=by intro p j;fin_cases j;change (if p=output then some (0 : Fin 1) else none)=some 0 ↔ output=p;simp [eq_comm]
def start (F : Fin (r+1) → RationalMobius) : Label F := .generate (RawNormalization.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .generate (.normalize .done) => .work (.jump (.rewind .left))
  | .generate pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.generate (RawNormalization.program F pc)
  | .rewind pc => .work (rewindBinding.instruction Label.rewind (NativeSpanRewind.program pc))

theorem generate_code (F : Fin (r+1) → RationalMobius) (pc : RawNormalization.Label F)
    (hh : RawNormalization.program F pc≠.work .halt) (_ : RawNormalization.program F pc≠.work .reject) :
    program F (.generate pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.generate (RawNormalization.program F pc) := by
  cases pc with
  | normalize pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
theorem rewind_code (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (_ : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program F) (.rewind pc)=MicrocodeEmbedding.instruction rewindBinding.ports Label.rewind (NativeSpanRewind.program pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem embed_generate (F : Fin (r+1) → RationalMobius) (pc : RawNormalization.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F)) (RawNormalization.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.generate pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed RawNormalization.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed RawNormalization.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem generate_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ RawNormalization.coefficient F*w.length,(FamilyNormalization.outputStream F xs).length≤t ∧ Trace F w t
      (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.generate (.normalize .done)) (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
        (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=RawNormalization.complete_trace F w n hn hw pos outRev
  have hl':=RawNormalization.output_length_le_time F w xs t pos outRev htr
  have he:=NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F))
    (RawNormalization.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (generate_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,hl',by simpa only [embed_generate,start] using he⟩

theorem embed_rewind (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : Bank) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed rewindBinding.ports (Label.rewind (F:=F)) (NativeSpanRewind.cfg pc word (fun _ => z)).denote
      (RawEnumeration.frame base pos)=workCfg (.rewind pc) (Function.update base output word) (Function.update pos output z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote workCfg RawEnumeration.frame
  simp only [← rewindBinding.values_eq_extend]
  congr 2 <;> funext p <;> by_cases hp : p=output
  all_goals simp [rewindBinding,FinitePortBinding.values,Function.update,hp]

theorem bank_update (w xs : List Bool) (raw out word : Tape Bool) :
    Function.update (RawNormalization.bank w xs raw out) output word=RawNormalization.bank w xs raw word := by
  funext p
  by_cases hp : p=output
  · subst p;rw [Function.update_self,RawNormalization.bank_output]
  · rw [Function.update_of_ne hp]
    by_cases ha : p=.payload
    · subst p;rw [RawNormalization.bank_payload,RawNormalization.bank_payload]
    · by_cases hs : p=.enumeration .source
      · subst p;rw [RawNormalization.bank_source,RawNormalization.bank_source]
      · by_cases hr : p=RawNormalization.rawOutput
        · subst p;rw [RawNormalization.bank_raw,RawNormalization.bank_raw]
        · rw [RawNormalization.bank_other w xs raw out p ha hs hr hp,RawNormalization.bank_other w xs raw word p ha hs hr hp]

theorem restored_positions (pos : Port → ℤ) (a b : ℕ) :
    Function.update (RawNormalization.advance pos a b) output (pos output)=RawNormalization.advance pos a 0 := by
  funext p
  by_cases hp : p=output
  · subst p;simp [Function.update,RawNormalization.advance,RawNormalization.output_ne_raw]
  · simp [Function.update,RawNormalization.advance,hp]

theorem rewind_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (raw syms : List (Sym Bool))
    (h : ∀ s ∈ syms,s≠.blank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*syms.length+3,Trace F w t
      (cfg (.rewind .left) (RawNormalization.bank w xs ⟨raw.reverse,[]⟩ ⟨syms.reverse,[]⟩) (RawNormalization.advance pos raw.length syms.length) ip outRev)
      (cfg (.rewind .done) (RawNormalization.bank w xs ⟨raw.reverse,[]⟩ ⟨[],syms⟩) (RawNormalization.advance pos raw.length 0) ip outRev) := by
  let adv:=RawNormalization.advance pos raw.length syms.length
  obtain ⟨t,ht,htr⟩:=NativeSpanRewind.rewind_trace syms h (fun _ => adv output)
  have he:=MicrocodeEmbedding.trace_embed rewindBinding.ports (Label.rewind (F:=F)) NativeSpanRewind.program (NativeIO.workProgram (program F))
    (RawEnumeration.frame (RawNormalization.bank w xs ⟨raw.reverse,[]⟩ ⟨syms.reverse,[]⟩) adv) (rewind_code F) htr
  have hz : adv output-syms.length=pos output := by simp [adv,RawNormalization.advance,RawNormalization.output_ne_raw]
  refine ⟨t,ht,?_⟩
  simpa only [embed_rewind,bank_update,Function.update_eq_self,hz,adv,restored_positions,cfg]
    using NativeIO.lift_work_trace (program F) w ip outRev he

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.generate (.normalize .done)) s pos ip outRev) (cfg (.rewind .left) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.NormalizedReader


namespace TransposeFollowup.NormalizedReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := 3*RawNormalization.coefficient F+4

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.rewind .done) (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩)
        (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,hsize,ta⟩:=generate_call F w n hn hw pos outRev
  obtain ⟨b,hb,tb⟩:=rewind_call F w xs (FamilyEnumeration.stream F xs) (FamilyNormalization.outputStream F xs)
    (RawNormalization.output_nonblank F xs) pos w.length outRev
  have tj:=transfer_trace F w (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨(FamilyNormalization.outputStream F xs).reverse,[]⟩)
    (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length (FamilyNormalization.outputStream F xs).length) w.length outRev
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
        some ((cfg (.rewind .done) (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩)
          (RawNormalization.advance (fun _ => 0) (FamilyEnumeration.stream F xs).length 0) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.rewind .done) (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩)
          (RawNormalization.advance (fun _ => 0) (FamilyEnumeration.stream F xs).length 0) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw (fun _ => 0) []
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
          (cfg (.rewind .done) (RawNormalization.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩)
            (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev)
          outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ RawNormalization.Label F ⊕ NativeSpanRewind.Label where
  toFun | .generate pc => .inl pc | .rewind pc => .inr pc
  invFun | .inl pc => .generate pc | .inr pc => .rewind pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=1452+(∑ i : Fin (r+1),FamilyEnumeration.seedStates (F i))+
      (∑ i : Fin (r+1),(PaddedWord.commonConstant (F i)+2*FamilyNormalization.padding F i+197)) ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum]
    have hr:=(RawNormalization.fixed_resources F).2.2.1
    change Fintype.card (RawNormalization.Label F)-1+1=_ at hr
    have hp : 0<Fintype.card (RawNormalization.Label F) := Fintype.card_pos_iff.mpr ⟨RawNormalization.start F⟩
    have hh : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
    rw [hh]
    omega

end TransposeFollowup.NormalizedReader


/-! Reuse the42-tape preparation,rewind its raw stream,and run the complete
finite-family selector. The payload and normalized query stream are framed. -/
namespace TransposeFollowup.RawSelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := RawEnumeration.Port
abbrev Bank := RawEnumeration.Bank
abbrev rawOutput := RawNormalization.rawOutput
abbrev normalizedOutput := RawNormalization.output
def output : Port := RawEnumeration.sharedPort .scratch
def selectPort : Fin 9 → Port :=
  ![.enumeration .source,RawEnumeration.sharedPort .dimension,normalizedOutput,
    RawEnumeration.sharedPort .index,RawEnumeration.sharedPort .zero,RawEnumeration.sharedPort .unit,
    RawEnumeration.sharedPort .fuel,rawOutput,output]
def selectBinding : FinitePortBinding (Fin 9) Port where
  ports:=⟨selectPort,by decide +kernel⟩
  decode:=fun p => if p=selectPort 0 then some 0 else if p=selectPort 1 then some 1 else if p=selectPort 2 then some 2 else
    if p=selectPort 3 then some 3 else if p=selectPort 4 then some 4 else if p=selectPort 5 then some 5 else
    if p=selectPort 6 then some 6 else if p=selectPort 7 then some 7 else if p=selectPort 8 then some 8 else none
  decode_spec:=by decide +kernel
abbrev rewindBinding := FamilyReader.rewindBinding

inductive Label (F : Fin (r+1) → RationalMobius)
  | prepare (pc : NormalizedReader.Label F)
  | rewind (pc : NativeSpanRewind.Label)
  | select (pc : FamilySelector.Label F)
  deriving DecidableEq,Fintype
def start (F : Fin (r+1) → RationalMobius) : Label F := .prepare (NormalizedReader.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .prepare (.rewind .done) => .work (.jump (.rewind .left))
  | .prepare pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.prepare (NormalizedReader.program F pc)
  | .rewind .done => .work (.jump (.select (FamilySelector.entry F 0)))
  | .rewind pc => .work (rewindBinding.instruction Label.rewind (NativeSpanRewind.program pc))
  | .select pc => .work (selectBinding.instruction Label.select (FamilySelector.program F pc))

theorem prepare_code (F : Fin (r+1) → RationalMobius) (pc : NormalizedReader.Label F)
    (hh : NormalizedReader.program F pc≠.work .halt) (_ : NormalizedReader.program F pc≠.work .reject) :
    program F (.prepare pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.prepare (NormalizedReader.program F pc) := by
  cases pc with
  | rewind pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
theorem rewind_code (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (hh : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program F) (.rewind pc)=MicrocodeEmbedding.instruction rewindBinding.ports Label.rewind (NativeSpanRewind.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]
theorem select_code (F : Fin (r+1) → RationalMobius) (pc : FamilySelector.Label F)
    (_ : FamilySelector.program F pc≠.halt) (_ : FamilySelector.program F pc≠.reject) :
    NativeIO.workProgram (program F) (.select pc)=MicrocodeEmbedding.instruction selectBinding.ports Label.select (FamilySelector.program F pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def liftBank (w : List Bool) (s : FilteredBatch.Bank) : Bank := selectBinding.values s (RawEnumeration.loaded w [] [])
def bank (w xs : List Bool) (raw normalized out : Tape Bool) := liftBank w (FilteredBatch.ready xs normalized raw out)
def advance (pos : Port → ℤ) (raw out : ℕ) :=
  fun p => pos p+(if p=rawOutput then (raw : ℤ) else 0)+(if p=output then (out : ℤ) else 0)
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) := OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem prepared_bank (w xs : List Bool) (raw normalized : Tape Bool) :
    RawNormalization.bank w xs raw normalized=bank w xs raw normalized ⟨[],[]⟩ := by
  funext p;fin_cases p <;> rfl

theorem embed_prepare (F : Fin (r+1) → RationalMobius) (pc : NormalizedReader.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F)) (NormalizedReader.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.prepare pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed NormalizedReader.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed NormalizedReader.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem embed_select (F : Fin (r+1) → RationalMobius) (pc : FamilySelector.Label F) (w : List Bool)
    (s base : FilteredBatch.Bank) (rpos : Fin 9 → ℤ) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed selectBinding.ports (Label.select (F:=F)) (FamilySelector.cfg pc s rpos)
      (RawEnumeration.frame (liftBank w base) pos)=workCfg (.select pc) (liftBank w s) (selectBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed FamilySelector.cfg workCfg RawEnumeration.frame liftBank
  simp only [← selectBinding.values_eq_extend,FinitePortBinding.map_values,FinitePortBinding.values_overwrite]

theorem select_positions (pos : Port → ℤ) : selectBinding.values (fun p => pos (selectPort p)) pos=pos :=
  selectBinding.values_project pos

theorem select_final_positions (pos : Port → ℤ) (a b : ℕ) :
    selectBinding.values (FilteredBatch.advance (fun p => pos (selectPort p)) a b) pos=advance pos a b := by
  funext p
  rw [selectBinding.values_eq_extend]
  by_cases hp : ∃ q,selectBinding.ports q=p
  · obtain ⟨q,rfl⟩:=hp
    rw [MicrocodeEmbedding.extend_at]
    have hr : selectBinding.ports q=rawOutput ↔ q=7 := by
      change selectBinding.ports q=selectBinding.ports (7 : Fin 9) ↔ q=7
      exact selectBinding.ports.injective.eq_iff
    have ho : selectBinding.ports q=output ↔ q=8 := by
      change selectBinding.ports q=selectBinding.ports (8 : Fin 9) ↔ q=8
      exact selectBinding.ports.injective.eq_iff
    simp only [FilteredBatch.advance,advance,hr,ho]
    rfl
  · rw [MicrocodeEmbedding.extend_outside _ _ hp]
    have hr : p≠rawOutput := by intro h;exact hp ⟨7,h.symm⟩
    have ho : p≠output := by intro h;exact hp ⟨8,h.symm⟩
    simp [advance,hr,ho]

end TransposeFollowup.RawSelector


namespace TransposeFollowup.RawSelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem bank_update_raw (w xs : List Bool) (raw normalized out word : Tape Bool) :
    Function.update (bank w xs raw normalized out) rawOutput word=bank w xs word normalized out := by
  change Function.update (selectBinding.values (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []))
    (selectBinding.ports (7 : Fin 9)) word=selectBinding.values (FilteredBatch.ready xs normalized word out) (RawEnumeration.loaded w [] [])
  rw [FinitePortBinding.values_update]
  congr 1
  funext p;fin_cases p <;> rfl

theorem embed_rewind (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : Bank) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed rewindBinding.ports (Label.rewind (F:=F)) (NativeSpanRewind.cfg pc word (fun _ => z)).denote
      (RawEnumeration.frame base pos)=workCfg (.rewind pc) (Function.update base rawOutput word) (Function.update pos rawOutput z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote workCfg RawEnumeration.frame
  simp only [← rewindBinding.values_eq_extend]
  congr 2 <;> funext p <;> by_cases hp : p=rawOutput
  all_goals simp [rewindBinding,FamilyReader.rewindBinding,FinitePortBinding.values,Function.update,hp]

theorem restored_positions (pos : Port → ℤ) (m : ℕ) :
    Function.update (RawNormalization.advance pos m 0) rawOutput (pos rawOutput)=pos := by
  funext p
  by_cases hp : p=rawOutput
  · subst p;simp
  · simp [Function.update,RawNormalization.advance,hp]

theorem rewind_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (syms : List (Sym Bool))
    (h : ∀ s ∈ syms,s≠.blank) (normalized out : Tape Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*syms.length+3,Trace F w t
      (cfg (.rewind .left) (bank w xs ⟨syms.reverse,[]⟩ normalized out) (RawNormalization.advance pos syms.length 0) ip outRev)
      (cfg (.rewind .done) (bank w xs ⟨[],syms⟩ normalized out) pos ip outRev) := by
  let adv:=RawNormalization.advance pos syms.length 0
  obtain ⟨t,ht,htr⟩:=NativeSpanRewind.rewind_trace syms h (fun _ => adv rawOutput)
  have he:=MicrocodeEmbedding.trace_embed rewindBinding.ports (Label.rewind (F:=F)) NativeSpanRewind.program
    (NativeIO.workProgram (program F)) (RawEnumeration.frame (bank w xs ⟨syms.reverse,[]⟩ normalized out) adv) (rewind_code F) htr
  have hz : adv rawOutput-syms.length=pos rawOutput := by simp [adv,RawNormalization.advance]
  refine ⟨t,ht,?_⟩
  simpa only [embed_rewind,bank_update_raw,Function.update_eq_self,hz,adv,restored_positions,cfg]
    using NativeIO.lift_work_trace (program F) w ip outRev he

end TransposeFollowup.RawSelector


namespace TransposeFollowup.RawSelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem prepare_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ NormalizedReader.coefficient F*w.length,(FamilyEnumeration.stream F xs).length≤t ∧ Trace F w t
      (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.prepare (.rewind .done))
        (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩)
        (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=NormalizedReader.complete_trace F w n hn hw pos outRev
  have hb:=(NativeHeadDisplacement.trace_bounds (NormalizedReader.program F) w htr rawOutput).2
  have hlen : (FamilyEnumeration.stream F xs).length≤t := by
    simp only [NormalizedReader.cfg,NormalizedReader.workCfg,RawNormalization.advance,ite_true,Nat.cast_zero,ite_self,add_zero] at hb
    omega
  have he:=NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F))
    (NormalizedReader.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (prepare_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,hlen,by simpa only [embed_prepare,prepared_bank,start] using he⟩

theorem select_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (hn : 1≤Counter.value xs) (hx : xs.length≤(Counter.value xs+1).size)
    (pre suffix out : List (Sym Bool)) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ FamilySelector.coefficient F*Transpose.inputLength (Counter.value xs),Trace F w t
      (cfg (.select (FamilySelector.entry F 0))
        (bank w xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨out,[]⟩) pos ip outRev)
      (cfg (.select .done) (bank w xs ⟨(FamilyNormalization.inputStream F xs).reverse++pre,suffix⟩
        ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse++out,[]⟩)
        (advance pos (FamilyNormalization.inputStream F xs).length (FamilySelector.outputStream F xs).length) ip outRev) := by
  obtain ⟨t,ht,htr⟩:=FamilySelector.complete_trace F xs hn hx pre suffix out (fun p => pos (selectPort p))
  have he:=MicrocodeEmbedding.trace_embed selectBinding.ports (Label.select (F:=F)) (FamilySelector.program F)
    (NativeIO.workProgram (program F))
    (RawEnumeration.frame (liftBank w (FamilySelector.bank F xs ⟨pre,FamilyNormalization.inputStream F xs++suffix⟩ ⟨out,[]⟩)) pos)
    (select_code F) htr
  simp only [embed_select,select_positions,select_final_positions] at he
  exact ⟨t,ht,by simpa only [cfg,bank,FamilySelector.bank] using NativeIO.lift_work_trace (program F) w ip outRev he⟩

theorem prepare_transfer (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.prepare (.rewind .done)) s pos ip outRev) (cfg (.rewind .left) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

theorem select_transfer (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.rewind .done) s pos ip outRev) (cfg (.select (FamilySelector.entry F 0)) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.RawSelector


namespace TransposeFollowup.RawSelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := 3*NormalizedReader.coefficient F+FamilySelector.coefficient F+5

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.select .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
        ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
        (advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,hlen,ta⟩:=prepare_call F w n hn hw pos outRev
  obtain ⟨b,hb,tb⟩:=rewind_call F w xs (FamilyEnumeration.stream F xs) (FamilyReader.stream_nonblank F xs)
    ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩ pos w.length outRev
  have j1:=prepare_transfer F w
    (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩)
    (RawNormalization.advance pos (FamilyEnumeration.stream F xs).length 0) w.length outRev
  have j2:=select_transfer F w
    (bank w xs ⟨[],FamilyEnumeration.stream F xs⟩ ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],[]⟩) pos w.length outRev
  have hn' : 1≤Counter.value xs := by omega
  have hl' : xs.length≤(Counter.value xs+1).size := by rw [hv,hl];exact Nat.size_le_size (by omega)
  obtain ⟨c,hc,tc⟩:=select_call F w xs hn' hl' [] [] [] pos w.length outRev
  simp only [List.append_nil,FamilyNormalization.input_stream_eq] at tc
  rw [hv,← hw] at hc
  have hL : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  refine ⟨xs,hx,hv,hl,a+1+b+1+c,?_,?_⟩
  · unfold coefficient
    nlinarith
  · exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.select .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
          ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
          (advance (fun _ => 0) (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.select .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
          ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
          (advance (fun _ => 0) (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw (fun _ => 0) []
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hi : (cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F) := by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,FamilySelector.program]

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
          (cfg (.select .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
            ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
            (advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev)
          outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ NormalizedReader.Label F ⊕ NativeSpanRewind.Label ⊕ FamilySelector.Label F where
  toFun | .prepare pc => .inl pc | .rewind pc => .inr (.inl pc) | .select pc => .inr (.inr pc)
  invFun | .inl pc => .prepare pc | .inr (.inl pc) => .rewind pc | .inr (.inr pc) => .select pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) : (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=Fintype.card (NormalizedReader.Label F)+4+Fintype.card (FamilySelector.Label F) ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F)]
    have hh : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
    simp only [Fintype.card_sum,hh]
    omega

end TransposeFollowup.RawSelector


namespace TransposeFollowup.RawSelector
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem bank_payload (w xs : List Bool) (raw normalized out : Tape Bool) :
    bank w xs raw normalized out .payload=Counter.marked w := rfl
theorem bank_source (w xs : List Bool) (raw normalized out : Tape Bool) :
    bank w xs raw normalized out (.enumeration .source)=Counter.marked xs := selectBinding.values_at (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []) 0
theorem bank_raw (w xs : List Bool) (raw normalized out : Tape Bool) :
    bank w xs raw normalized out rawOutput=raw := selectBinding.values_at (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []) 7
theorem bank_normalized (w xs : List Bool) (raw normalized out : Tape Bool) :
    bank w xs raw normalized out normalizedOutput=normalized := selectBinding.values_at (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []) 2
theorem bank_output (w xs : List Bool) (raw normalized out : Tape Bool) :
    bank w xs raw normalized out output=out := selectBinding.values_at (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []) 8
theorem bank_other (w xs : List Bool) (raw normalized out : Tape Bool) (p : Port)
    (hp : p≠.payload) (hs : p≠.enumeration .source) (hr : p≠rawOutput) (hn : p≠normalizedOutput) (ho : p≠output) :
    bank w xs raw normalized out p=⟨[],[]⟩ := by
  fin_cases p <;> first
    | rfl
    | exact False.elim (hp rfl)
    | exact False.elim (hs rfl)
    | exact False.elim (hr rfl)
    | exact False.elim (hn rfl)
    | exact False.elim (ho rfl)

theorem output_ne_raw : output≠rawOutput := by decide +kernel

theorem output_length_le_time (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (t : ℕ)
    (pos : Port → ℤ) (outRev : List Bool)
    (h : Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.select .done) (bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
        ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
        (advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev)) :
    (FamilySelector.outputStream F xs).length≤t := by
  have hp:=(NativeHeadDisplacement.trace_bounds (program F) w h output).2
  simp only [cfg,workCfg,advance,output_ne_raw,ite_false,ite_true,add_zero] at hp
  omega

end TransposeFollowup.RawSelector


/-! Native canonical-union generation followed by its paid output rewind.
The retained raw stream stays at its end;the normalized stream stays ready. -/
namespace TransposeFollowup.CanonicalReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := RawSelector.Port
abbrev Bank := RawSelector.Bank
abbrev output := RawSelector.output

inductive Label (F : Fin (r+1) → RationalMobius)
  | generate (pc : RawSelector.Label F)
  | rewind (pc : NativeSpanRewind.Label)
  deriving DecidableEq,Fintype

def rewindBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => output,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=output then some 0 else none
  decode_spec:=by intro p j;fin_cases j;change (if p=output then some (0 : Fin 1) else none)=some 0 ↔ output=p;simp [eq_comm]
def start (F : Fin (r+1) → RationalMobius) : Label F := .generate (RawSelector.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .generate (.select .done) => .work (.jump (.rewind .left))
  | .generate pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.generate (RawSelector.program F pc)
  | .rewind pc => .work (rewindBinding.instruction Label.rewind (NativeSpanRewind.program pc))

theorem generate_code (F : Fin (r+1) → RationalMobius) (pc : RawSelector.Label F)
    (hh : RawSelector.program F pc≠.work .halt) (_ : RawSelector.program F pc≠.work .reject) :
    program F (.generate pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.generate (RawSelector.program F pc) := by
  cases pc with
  | select pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
theorem rewind_code (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (_ : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program F) (.rewind pc)=MicrocodeEmbedding.instruction rewindBinding.ports Label.rewind (NativeSpanRewind.program pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem embed_generate (F : Fin (r+1) → RationalMobius) (pc : RawSelector.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F)) (RawSelector.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.generate pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed RawSelector.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed RawSelector.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem generate_call (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ RawSelector.coefficient F*w.length,(FamilySelector.outputStream F xs).length≤t ∧ Trace F w t
      (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.generate (.select .done)) (RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
        ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
        (RawSelector.advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=RawSelector.complete_trace F w n hn hw pos outRev
  have hl':=RawSelector.output_length_le_time F w xs t pos outRev htr
  have he:=NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.generate (F:=F))
    (RawSelector.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (generate_code F) htr
  exact ⟨xs,hx,hv,hl,t,ht,hl',by simpa only [embed_generate,start] using he⟩

theorem embed_rewind (F : Fin (r+1) → RationalMobius) (pc : NativeSpanRewind.Label)
    (word : Tape Bool) (base : Bank) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed rewindBinding.ports (Label.rewind (F:=F)) (NativeSpanRewind.cfg pc word (fun _ => z)).denote
      (RawEnumeration.frame base pos)=workCfg (.rewind pc) (Function.update base output word) (Function.update pos output z) := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote workCfg RawEnumeration.frame
  simp only [← rewindBinding.values_eq_extend]
  congr 2 <;> funext p <;> by_cases hp : p=output
  all_goals simp [rewindBinding,FinitePortBinding.values,Function.update,hp]

theorem bank_update (w xs : List Bool) (raw normalized out word : Tape Bool) :
    Function.update (RawSelector.bank w xs raw normalized out) output word=RawSelector.bank w xs raw normalized word := by
  change Function.update (RawSelector.selectBinding.values (FilteredBatch.ready xs normalized raw out) (RawEnumeration.loaded w [] []))
    (RawSelector.selectBinding.ports (8 : Fin 9)) word=RawSelector.selectBinding.values (FilteredBatch.ready xs normalized raw word) (RawEnumeration.loaded w [] [])
  rw [FinitePortBinding.values_update]
  congr 1
  funext p;fin_cases p <;> rfl

theorem restored_positions (pos : Port → ℤ) (a b : ℕ) :
    Function.update (RawSelector.advance pos a b) output (pos output)=RawSelector.advance pos a 0 := by
  funext p
  by_cases hp : p=output
  · subst p;simp [Function.update,RawSelector.advance,RawSelector.output_ne_raw]
  · simp [Function.update,RawSelector.advance,hp]

theorem rewind_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (raw syms : List (Sym Bool))
    (h : ∀ s ∈ syms,s≠.blank) (normalized : Tape Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*syms.length+3,Trace F w t
      (cfg (.rewind .left) (RawSelector.bank w xs ⟨raw.reverse,[]⟩ normalized ⟨syms.reverse,[]⟩)
        (RawSelector.advance pos raw.length syms.length) ip outRev)
      (cfg (.rewind .done) (RawSelector.bank w xs ⟨raw.reverse,[]⟩ normalized ⟨[],syms⟩)
        (RawSelector.advance pos raw.length 0) ip outRev) := by
  let adv:=RawSelector.advance pos raw.length syms.length
  obtain ⟨t,ht,htr⟩:=NativeSpanRewind.rewind_trace syms h (fun _ => adv output)
  have he:=MicrocodeEmbedding.trace_embed rewindBinding.ports (Label.rewind (F:=F)) NativeSpanRewind.program (NativeIO.workProgram (program F))
    (RawEnumeration.frame (RawSelector.bank w xs ⟨raw.reverse,[]⟩ normalized ⟨syms.reverse,[]⟩) adv) (rewind_code F) htr
  have hz : adv output-syms.length=pos output := by simp [adv,RawSelector.advance,RawSelector.output_ne_raw]
  refine ⟨t,ht,?_⟩
  simpa only [embed_rewind,bank_update,Function.update_eq_self,hz,adv,restored_positions,cfg]
    using NativeIO.lift_work_trace (program F) w ip outRev he

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.generate (.select .done)) s pos ip outRev) (cfg (.rewind .left) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.CanonicalReader


namespace TransposeFollowup.CanonicalReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := 3*RawSelector.coefficient F+4
def readyBank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :=
  RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
    ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨[],FamilySelector.outputStream F xs⟩
def finalPositions (F : Fin (r+1) → RationalMobius) (xs : List Bool) (pos : Port → ℤ) :=
  RawSelector.advance pos (FamilyEnumeration.stream F xs).length 0

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn : 1≤n)
    (hw : w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.rewind .done) (readyBank F w xs) (finalPositions F xs pos) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,hsize,ta⟩:=generate_call F w n hn hw pos outRev
  obtain ⟨b,hb,tb⟩:=rewind_call F w xs (FamilyEnumeration.stream F xs) (FamilySelector.outputStream F xs)
    (FamilySelector.output_nonblank F xs) ⟨[],FamilyNormalization.outputStream F xs⟩ pos w.length outRev
  have tj:=transfer_trace F w
    (RawSelector.bank w xs ⟨(FamilyEnumeration.stream F xs).reverse,[]⟩
      ⟨[],FamilyNormalization.outputStream F xs⟩ ⟨(FamilySelector.outputStream F xs).reverse,[]⟩)
    (RawSelector.advance pos (FamilyEnumeration.stream F xs).length (FamilySelector.outputStream F xs).length) w.length outRev
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
        some ((cfg (.rewind .done) (readyBank F w xs) (finalPositions F xs (fun _ => 0)) w.length []).denote (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.rewind .done) (readyBank F w xs) (finalPositions F xs (fun _ => 0)) w.length []).denote (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw (fun _ => 0) []
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
          (cfg (.rewind .done) (readyBank F w xs) (finalPositions F xs pos) w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃ RawSelector.Label F ⊕ NativeSpanRewind.Label where
  toFun | .generate pc => .inl pc | .rewind pc => .inr pc
  invFun | .inl pc => .generate pc | .inr pc => .rewind pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=42 ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=Fintype.card (RawSelector.Label F)+4 ∧ (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum]
    have hh : Fintype.card NativeSpanRewind.Label=4 := by decide +kernel
    rw [hh]
    omega

end TransposeFollowup.CanonicalReader


/-! The existing arithmetic initializer reuses seven blank tapes after
canonical-stream preparation. All five retained tapes survive. -/
namespace TransposeFollowup.SchedulerSeed
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port := CanonicalReader.Port
abbrev Bank := CanonicalReader.Bank

def seedPort : ArithmeticSeed.Port → Port
  | .source => .enumeration .source
  | .number => RawEnumeration.sharedPort .dimension
  | .zeroA => RawEnumeration.sharedPort .index
  | .zeroB => RawEnumeration.sharedPort .zero
  | .one => RawEnumeration.sharedPort .unit
  | .fuel => RawEnumeration.sharedPort (.work 0)
  | .left => RawEnumeration.sharedPort .fuel
  | .right => RawEnumeration.sharedPort (.work 1)
def seedBinding : FinitePortBinding ArithmeticSeed.Port Port where
  ports:=⟨seedPort,by decide +kernel⟩
  decode:=fun p => if p=seedPort .source then some .source else if p=seedPort .number then some .number else
    if p=seedPort .zeroA then some .zeroA else if p=seedPort .zeroB then some .zeroB else
    if p=seedPort .one then some .one else if p=seedPort .fuel then some .fuel else
    if p=seedPort .left then some .left else if p=seedPort .right then some .right else none
  decode_spec:=by decide +kernel

inductive Label (F : Fin (r+1) → RationalMobius)
  | prepare (pc : CanonicalReader.Label F)
  | seed (pc : ArithmeticSeed.Label (FamilyNormalization.common F))
  deriving DecidableEq,Fintype
def start (F : Fin (r+1) → RationalMobius) : Label F := .prepare (CanonicalReader.start F)
def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program Port (Label F)
  | .prepare (.rewind .done) => .work (.jump (.seed (.pad false (.init (.erase 0)))))
  | .prepare pc => NativeIOEmbedding.boundInstruction FamilyEnumeration.identityBinding Label.prepare (CanonicalReader.program F pc)
  | .seed pc => .work (seedBinding.instruction Label.seed (ArithmeticSeed.program (FamilyNormalization.common F) pc))

theorem prepare_code (F : Fin (r+1) → RationalMobius) (pc : CanonicalReader.Label F)
    (hh : CanonicalReader.program F pc≠.work .halt) (_ : CanonicalReader.program F pc≠.work .reject) :
    program F (.prepare pc)=NativeIOEmbedding.instruction FamilyEnumeration.identityBinding.ports Label.prepare (CanonicalReader.program F pc) := by
  cases pc with
  | rewind pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
  | _ => simp only [program,NativeIOEmbedding.bound_instruction_eq]
theorem seed_code (F : Fin (r+1) → RationalMobius) (pc : ArithmeticSeed.Label (FamilyNormalization.common F))
    (_ : ArithmeticSeed.program (FamilyNormalization.common F) pc≠.halt)
    (_ : ArithmeticSeed.program (FamilyNormalization.common F) pc≠.reject) :
    NativeIO.workProgram (program F) (.seed pc)=MicrocodeEmbedding.instruction seedBinding.ports Label.seed
      (ArithmeticSeed.program (FamilyNormalization.common F) pc) := by
  simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

def workCfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def cfg {F : Fin (r+1) → RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config Port (Label F) :=
  ⟨workCfg pc s pos,ip,outRev⟩
def readyBank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) : Bank :=
  seedBinding.values (ArithmeticSeed.ready (FamilyNormalization.common F) xs).tapes (CanonicalReader.readyBank F w xs)
abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program F) w) (NativeIO.Active (program F))

theorem embed_prepare (F : Fin (r+1) → RationalMobius) (pc : CanonicalReader.Label F)
    (s base : Bank) (pos basePos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F)) (CanonicalReader.cfg pc s pos ip outRev)
      (RawEnumeration.frame base basePos)=cfg (.prepare pc) s pos ip outRev := by
  unfold NativeIOEmbedding.embed CanonicalReader.cfg cfg
  congr 1
  unfold MicrocodeEmbedding.embed CanonicalReader.workCfg workCfg RawEnumeration.frame
  simp only [← FamilyEnumeration.identityBinding.values_eq_extend]
  rfl

theorem embed_seed (F : Fin (r+1) → RationalMobius) (pc : ArithmeticSeed.Label (FamilyNormalization.common F))
    (s : ArithmeticSeed.Bank) (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed seedBinding.ports (Label.seed (F:=F))
      (ArithmeticSeed.cfg pc s (fun p => pos (seedPort p))) (RawEnumeration.frame base pos)=
      workCfg (.seed pc) (seedBinding.values s.tapes base) pos := by
  unfold MicrocodeEmbedding.embed ArithmeticSeed.cfg workCfg RawEnumeration.frame
  simp only [← seedBinding.values_eq_extend,FinitePortBinding.map_values]
  congr 1
  exact seedBinding.values_project pos

theorem initial_bank (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    seedBinding.values (ArithmeticSeed.initial xs).tapes (CanonicalReader.readyBank F w xs)=CanonicalReader.readyBank F w xs := by
  funext p;fin_cases p <;> rfl

theorem seed_call (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ ArithmeticSeed.budget (FamilyNormalization.common F) xs,Trace F w t
      (cfg (.seed (.pad false (.init (.erase 0)))) (CanonicalReader.readyBank F w xs) pos ip outRev)
      (cfg (.seed .done) (readyBank F w xs) pos ip outRev) := by
  have hp:0<2*xs.length+FamilyNormalization.common F:=by
    have h:=RowEnumeration.common_positive (F 0) xs
    rw [PaddedWord.word_length] at h
    have hc:=FamilyNormalization.le_common F 0
    omega
  obtain ⟨t,ht,htr⟩:=ArithmeticSeed.seed_trace (FamilyNormalization.common F) xs hp (fun p => pos (seedPort p))
  have he:=MicrocodeEmbedding.trace_embed seedBinding.ports (Label.seed (F:=F)) (ArithmeticSeed.program (FamilyNormalization.common F))
    (NativeIO.workProgram (program F)) (RawEnumeration.frame (CanonicalReader.readyBank F w xs) pos) (seed_code F) htr
  exact ⟨t,ht,by simpa only [embed_seed,initial_bank,readyBank,cfg] using NativeIO.lift_work_trace (program F) w ip outRev he⟩

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (s : Bank) (pos : Port → ℤ) (ip : ℤ) (outRev : List Bool) :
    Trace F w 1 (cfg (.prepare (.rewind .done)) s pos ip outRev)
      (cfg (.seed (.pad false (.init (.erase 0)))) s pos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeIO.Active,cfg,workCfg,program]
  · exact .refl _

end TransposeFollowup.SchedulerSeed


namespace TransposeFollowup.SchedulerSeed
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) := CanonicalReader.coefficient F+17*FamilyNormalization.common F+128

theorem complete_trace (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn:1≤n)
    (hw:w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,Trace F w t
      (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.seed .done) (readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=CanonicalReader.complete_trace F w n hn hw pos outRev
  have te:=NativeIOEmbedding.trace_embed FamilyEnumeration.identityBinding.ports (Label.prepare (F:=F))
    (CanonicalReader.program F) (program F) (RawEnumeration.frame (RawEnumeration.initial []) pos) w (prepare_code F) ta
  have te':Trace F w a (cfg (start F) (RawEnumeration.initial []) pos 0 outRev)
      (cfg (.prepare (.rewind .done)) (CanonicalReader.readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev):=by
    simpa only [embed_prepare,start] using te
  have tj:=transfer_trace F w (CanonicalReader.readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev
  obtain ⟨b,hb,tb⟩:=seed_call F w xs (CanonicalReader.finalPositions F xs pos) w.length outRev
  have hnL:n≤w.length:=by rw [hw];exact DimensionCandidate.dimension_le_length n hn
  have hs:n.size≤n:=Nat.size_le.mpr Nat.lt_two_pow_self
  have hlL:xs.length≤w.length:=by omega
  have h1:1≤w.length:=hn.trans hnL
  refine ⟨xs,hx,hv,hl,a+1+b,?_,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans te' tj) tb⟩
  unfold ArithmeticSeed.budget at hb
  unfold coefficient
  nlinarith

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) := NativeMicrocode.initialEncoding (T:=Port) (start F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) := NativeIO.machine (nativeEncoding F) (program F)

theorem native_complete (F : Fin (r+1) → RationalMobius) (w : List Bool) (n : ℕ) (hn:1≤n)
    (hw:w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (nativeMachine F) w t (Transpose.init (nativeMachine F))=
        some ((cfg (.seed .done) (readyBank F w xs) (CanonicalReader.finalPositions F xs (fun _ => 0)) w.length []).denote
          (nativeEncoding F) (program F)) ∧
      Transpose.step (nativeMachine F) w
        ((cfg (.seed .done) (readyBank F w xs) (CanonicalReader.finalPositions F xs (fun _ => 0)) w.length []).denote
          (nativeEncoding F) (program F))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw (fun _ => 0) []
  refine ⟨xs,hx,hv,hl,t,ht,?_,?_⟩
  · have hi:(cfg (start F) (RawEnumeration.initial []) (fun _ => 0) 0 []).denote (nativeEncoding F) (program F)=
        Transpose.init (nativeMachine F):=by
      rw [RawEnumeration.initial_nil]
      exact NativeIO.blank_denote (nativeEncoding F) (program F) (start F) (NativeMicrocode.initialEncoding_start _)
    rw [← hi]
    exact NativeIO.trace_stepN (nativeEncoding F) (program F) w htr
  · apply (NativeIO.step_none_iff (nativeEncoding F) (program F) w _).mpr
    simp [NativeIO.Active,cfg,workCfg,program,FinitePortBinding.instruction,ArithmeticSeed.program]

theorem native_call {U J : Type*} {k q : ℕ} (F : Fin (r+1) → RationalMobius) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label F → J) (target : NativeIO.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc:∀ pc,program F pc≠.work .halt → program F pc≠.work .reject →
      target (labels pc)=NativeIOEmbedding.instruction ports labels (program F pc))
    (w : List Bool) (n : ℕ) (hn:1≤n) (hw:w.length=Transpose.inputLength n) (pos : Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F*w.length,
      Transpose.stepN (NativeIO.machine encoding target) w t
        ((NativeIOEmbedding.embed ports labels (cfg (start F) (RawEnumeration.initial []) pos 0 outRev) outerFrame).denote encoding target)=
        some ((NativeIOEmbedding.embed ports labels
          (cfg (.seed .done) (readyBank F w xs) (CanonicalReader.finalPositions F xs pos) w.length outRev) outerFrame).denote encoding target) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F w n hn hw pos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOEmbedding.native_call encoding ports labels (program F) target outerFrame w hc htr⟩

def labelEquiv (F : Fin (r+1) → RationalMobius) : Label F ≃
    CanonicalReader.Label F ⊕ ArithmeticSeed.Label (FamilyNormalization.common F) where
  toFun | .prepare pc => .inl pc | .seed pc => .inr pc
  invFun | .inl pc => .prepare pc | .inr pc => .seed pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc) <;> rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) : (nativeMachine F).k=42 ∧
    (nativeMachine F).g+1=5 ∧ (nativeMachine F).q+1=Fintype.card (CanonicalReader.Label F)+2*FamilyNormalization.common F+166 ∧
    (nativeEncoding F).label (start F)=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=42;decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [Fintype.card_congr (labelEquiv F),Fintype.card_sum,ArithmeticSeed.label_card]
    omega

end TransposeFollowup.SchedulerSeed
