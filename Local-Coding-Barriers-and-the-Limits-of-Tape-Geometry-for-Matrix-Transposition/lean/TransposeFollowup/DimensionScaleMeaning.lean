import TransposeFollowup.SignedLinearFormMeaning

/-! A source bank, three reusable form products, and eight separate image
components. The form order is lower numerator/denominator followed by upper
numerator/denominator. No image output is used as scratch storage. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

def stage (j : Fin 4) : Bool × Bool := ![(false,false),(false,true),(true,false),(true,true)] j
def upper (j : Fin 4) : Bool := (stage j).1
def denominator (j : Fin 4) : Bool := (stage j).2
def u (F : RationalMobius) (j : Fin 4) : ℤ := (SignedLinearForm.coefficients F (denominator j)).1
def v (F : RationalMobius) (j : Fin 4) : ℤ := (SignedLinearForm.coefficients F (denominator j)).2

inductive Port | source (p : SourceEndpoints.Port) | work (j : Fin 3) | out (j : Fin 4) (negative : Bool)
  deriving DecidableEq, Fintype

@[ext] structure Bank where
  source : SourceEndpoints.Bank
  work : Fin 3 → Tape Bool
  out : Fin 4 → Bool → Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .source p => s.source.tapes p | .work j => s.work j | .out j b => s.out j b

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank :=
  match p with
  | .source q => {s with source := s.source.set q w}
  | .work j => {s with work := Function.update s.work j w}
  | .out j b => {s with out := Function.update s.out j (Function.update (s.out j) b w)}

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q=Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set,Bank.tapes,Function.update]
  split_ifs <;> simp_all

@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p)=s := by
  cases p <;> simp [Bank.set,Bank.tapes]

def initial (n iw : List Bool) : Bank :=
  ⟨SourceEndpoints.initial n iw,fun _ => ⟨[],[]⟩,fun _ _ => ⟨[],[]⟩⟩

def sourceFinal (F : RationalMobius) (n iw : List Bool) : SourceEndpoints.Bank :=
  SourceEndpoints.final (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F)
    (SourceEndpoints.negative F) n iw

def sourceAnswer (F : RationalMobius) (n iw : List Bool) : Bool :=
  SourceEndpoints.answer (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F)
    (SourceEndpoints.negative F) n iw

def args (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : Fin 3 → List Bool :=
  SourceEndpoints.outputWords (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F)
    (SourceEndpoints.negative F) n iw (upper j)

def product (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (k : Fin 3) : List Bool :=
  SignedLinearForm.workWord (u F j) (v F j) (args F n iw j) k
def imageWord (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (b : Bool) : List Bool :=
  SignedLinearForm.outputWord (u F j) (v F j) (args F n iw j) b

def before (F : RationalMobius) (n iw : List Bool) (k : ℕ) : Bank :=
  ⟨sourceFinal F n iw,fun _ => ⟨[],[]⟩,
    fun j b => if j.val<k then Counter.marked (imageWord F n iw j b) else ⟨[],[]⟩⟩
def afterForm (F : RationalMobius) (n iw : List Bool) (j : Fin 4) : Bank :=
  {before F n iw (j.val+1) with work := fun k => Counter.marked (product F n iw j k)}
def erasing (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (k : ℕ) : Bank :=
  {afterForm F n iw j with work := fun t => if t.val<k then ⟨[],[]⟩ else Counter.marked (product F n iw j t)}
def final (F : RationalMobius) (n iw : List Bool) : Bank := afterForm F n iw 3

def projectForm (j : Fin 4) (s : Bank) : SignedLinearForm.Bank :=
  ⟨SourceEndpoints.outputBank s.source (upper j),s.source.base.zero,s.source.base.fuel,
    s.source.base.scratch,s.work,s.out j⟩

def placeForm (j : Fin 4) (b : SignedLinearForm.Bank) (s : Bank) : Bank :=
  let base := {s.source.base with zero := b.zero, fuel := b.fuel, scratch := b.scratch, out := if upper j then s.source.base.out else b.arg}
  ⟨⟨base,if upper j then b.arg else s.source.other⟩,b.work,Function.update s.out j b.out⟩

theorem placeForm_project (j : Fin 4) (s : Bank) : placeForm j (projectForm j s) s=s := by
  cases hj : upper j <;> simp [placeForm,projectForm,SourceEndpoints.outputBank,hj]

theorem placeForm_update (j : Fin 4) (s : Bank) (w : Fin 3 → Tape Bool) (o : Bool → Tape Bool) :
    placeForm j {projectForm j s with work := w, out := o} s=
      {s with work := w, out := Function.update s.out j o} := by
  cases hj : upper j <;> simp [placeForm,projectForm,SourceEndpoints.outputBank,hj]

theorem source_seed (F : RationalMobius) (n iw : List Bool) :
    (sourceFinal F n iw).base.zero=Counter.marked (ArithmeticSeed.zeros n.length) ∧
    (sourceFinal F n iw).base.fuel=Counter.marked [true] ∧
    (sourceFinal F n iw).base.scratch=BinaryCarry.preparedOutput := by
  cases h0 : SourceEndpoints.negative F false <;> cases h1 : SourceEndpoints.negative F true <;>
    simp [sourceFinal,SourceEndpoints.final,SourceEndpoints.place,SourceEndpoints.eraseStage,
      SourceEndpoints.afterLower,EndpointGuard.final,EndpointGuard.updated,EndpointClip.final,
      EndpointClip.computed,EndpointClip.initial,h0,h1]

theorem args_length (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) (k : Fin 3) : (args F n iw j k).length=n.length :=
  SourceEndpoints.outputWords_length _ _ _ _ _ hm hi _ k

theorem product_length (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) (k : Fin 3) : (product F n iw j k).length=n.length := by
  have hl := args_length F n iw hm hi j
  exact (SignedLinearForm.workWord_length _ _ _ (fun t => (hl t).trans (hl 0).symm) k).trans (hl 0)

theorem imageWord_length (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) (b : Bool) : (imageWord F n iw j b).length=n.length := by
  have hl := args_length F n iw hm hi j
  exact (SignedLinearForm.outputWord_length _ _ _ (fun t => (hl t).trans (hl 0).symm) b).trans (hl 0)

theorem project_initial (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    projectForm j (before F n iw j.val)=SignedLinearForm.initial (args F n iw j) := by
  have hs := source_seed F n iw
  have hl := args_length F n iw hm hi j 0
  apply SignedLinearForm.Bank.ext
  · funext k
    exact SourceEndpoints.final_words _ _ _ _ _ _ k
  · simpa only [projectForm,before,SignedLinearForm.initial,hl] using hs.1
  · exact hs.2.1
  · exact hs.2.2
  · rfl
  · funext b
    simp [projectForm,before,SignedLinearForm.initial]

theorem form_initial (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    placeForm j (SignedLinearForm.initial (args F n iw j)) (before F n iw j.val)=before F n iw j.val := by
  rw [← project_initial F n iw hm hi j,placeForm_project]

theorem form_final (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (j : Fin 4) :
    placeForm j (SignedLinearForm.final (u F j) (v F j) (args F n iw j)) (before F n iw j.val)=
      afterForm F n iw j := by
  have hf : SignedLinearForm.final (u F j) (v F j) (args F n iw j)=
      {projectForm j (before F n iw j.val) with work := fun k => Counter.marked (product F n iw j k), out := fun b => Counter.marked (imageWord F n iw j b)} := by
    rw [project_initial F n iw hm hi j]
    apply SignedLinearForm.Bank.ext <;> try rfl
    funext k
    fin_cases k <;> rfl
  rw [hf,placeForm_update]
  apply Bank.ext <;> try rfl
  funext k b
  fin_cases j <;> fin_cases k <;> rfl

theorem erasing_zero (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    erasing F n iw j 0=afterForm F n iw j := by simp [erasing,afterForm]
theorem erasing_source (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (k : Fin 3) :
    (erasing F n iw j k.val).tapes (.work k)=Counter.marked (product F n iw j k) := by
  simp [erasing,Bank.tapes]
theorem erasing_step (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (k : Fin 3) :
    (erasing F n iw j k.val).set (.work k) ⟨[],[]⟩=erasing F n iw j (k.val+1) := by
  apply Bank.ext <;> try rfl
  funext t
  fin_cases k <;> fin_cases t <;> rfl
theorem erasing_three (F : RationalMobius) (n iw : List Bool) (j : Fin 4) :
    erasing F n iw j 3=before F n iw (j.val+1) := by
  apply Bank.ext <;> try rfl
  funext k
  fin_cases k <;> rfl

end TransposeFollowup.SourceImages


/-! Finite control retains the source-open Boolean throughout four image
forms and nine real product erasures. All returns are paid jumps. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
set_option autoImplicit false

def sourceBinding : FinitePortBinding SourceEndpoints.Port Port where
  ports := ⟨Port.source,by intro p q h; exact Port.source.inj h⟩
  decode := fun p => match p with | .source q => some q | _ => none
  decode_spec := by
    intro p q
    change (match p with | .source r => some r | _ => none)=some q ↔ Port.source q=p
    cases p <;> simp [eq_comm]

def formPort (j : Fin 4) : SignedLinearForm.Port → Port
  | .arg k => .source (if upper j then .other k else .shared (.out k))
  | .zero => .source (.shared .zero) | .fuel => .source (.shared .fuel)
  | .scratch => .source (.shared .scratch) | .work k => .work k | .out b => .out j b

def formBinding (j : Fin 4) : FinitePortBinding SignedLinearForm.Port Port where
  ports := ⟨formPort j,by
    cases hj : upper j <;> intro p q h <;> cases p <;> cases q <;> simp_all [formPort]⟩
  decode := fun p => match p with
    | .source (.shared (.out k)) => if upper j then none else some (.arg k)
    | .source (.other k) => if upper j then some (.arg k) else none
    | .source (.shared .zero) => some .zero | .source (.shared .fuel) => some .fuel
    | .source (.shared .scratch) => some .scratch | .work k => some (.work k)
    | .out k b => if k=j then some (.out b) else none | _ => none
  decode_spec := by
    intro p q
    change (match p with
      | .source (.shared (.out k)) => if upper j then none else some (SignedLinearForm.Port.arg k)
      | .source (.other k) => if upper j then some (.arg k) else none
      | .source (.shared .zero) => some .zero | .source (.shared .fuel) => some .fuel
      | .source (.shared .scratch) => some .scratch | .work k => some (.work k)
      | .out k b => if k=j then some (.out b) else none | _ => none)=some q ↔ formPort j q=p
    cases hj : upper j
    all_goals cases p with
    | source p => cases p with
      | shared p => cases p <;> cases q <;> simp [formPort,hj,eq_comm]
      | other k => cases q <;> simp [formPort,hj,eq_comm]
    | work k => cases q <;> simp [formPort,hj,eq_comm]
    | out k b => cases q <;> simp [formPort,hj,eq_comm]

def eraseBinding (k : Fin 3) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => .work k,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=.work k then some 0 else none
  decode_spec := by
    intro p q
    change (if p=.work k then some (0 : Fin 1) else none)=some q ↔ Port.work k=p
    fin_cases q
    simp [eq_comm]

inductive Label (F : RationalMobius)
  | source (pc : SourceEndpoints.Label (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F))
  | form (saved : Bool) (j : Fin 4) (pc : SignedLinearForm.Label (u F j) (v F j))
  | erase (saved : Bool) (j : Fin 3) (k : Fin 3) (pc : NativeErase.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def prior (j : Fin 3) : Fin 4 := ⟨j.val,by omega⟩
def next (j : Fin 3) : Fin 4 := ⟨j.val+1,by omega⟩

def afterCall (F : RationalMobius) (saved : Bool) (j : Fin 4) : Label F :=
  if h : j.val<3 then .erase saved ⟨j.val,h⟩ 0 2 else .done saved
def afterErase (F : RationalMobius) (saved : Bool) (j k : Fin 3) : Label F :=
  if h : k.val<2 then .erase saved j ⟨k.val+1,by omega⟩ 2
  else .form saved (next j) (.init 0 (.init (.erase 0)))

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .source (.done saved) => .jump (.form saved 0 (.init 0 (.init (.erase 0))))
  | .source pc => sourceBinding.instruction Label.source
      (SourceEndpoints.program (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) (SourceEndpoints.negative F) pc)
  | .form saved j .done => .jump (afterCall F saved j)
  | .form saved j pc => (formBinding j).instruction (Label.form saved j) (SignedLinearForm.program (u F j) (v F j) pc)
  | .erase saved j k pc => if pc=0 then .jump (afterErase F saved j k)
      else (eraseBinding k).instruction (Label.erase saved j k) (NativeErase.program pc)
  | .done _ => .halt

theorem source_code (F : RationalMobius)
    (pc : SourceEndpoints.Label (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F))
    (hh : SourceEndpoints.program (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) (SourceEndpoints.negative F) pc≠.halt)
    (_ : SourceEndpoints.program (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) (SourceEndpoints.negative F) pc≠.reject) :
    program F (.source pc)=MicrocodeEmbedding.instruction sourceBinding.ports Label.source
      (SourceEndpoints.program (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) (SourceEndpoints.negative F) pc) := by
  cases pc <;> try exact sourceBinding.instruction_eq _ _
  exact False.elim (hh rfl)

theorem form_code (F : RationalMobius) (saved : Bool) (j : Fin 4)
    (pc : SignedLinearForm.Label (u F j) (v F j))
    (hh : SignedLinearForm.program (u F j) (v F j) pc≠.halt)
    (_ : SignedLinearForm.program (u F j) (v F j) pc≠.reject) :
    program F (.form saved j pc)=MicrocodeEmbedding.instruction (formBinding j).ports
      (Label.form saved j) (SignedLinearForm.program (u F j) (v F j) pc) := by
  cases pc <;> try exact (formBinding j).instruction_eq _ _
  exact False.elim (hh rfl)

theorem erase_code (F : RationalMobius) (saved : Bool) (j k : Fin 3) (pc : NativeErase.Label)
    (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program F (.erase saved j k pc)=MicrocodeEmbedding.instruction (eraseBinding k).ports
      (Label.erase saved j k) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s.tapes p).denote⟩,pos⟩
def zipperCfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port (Label F) :=
  ⟨⟨pc,s.tapes⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote,pos⟩

noncomputable def nativeEncoding (F : RationalMobius) := NativeMicrocode.initialEncoding (T := Port)
  (Label.source (F := F) (.lower (.inl (.grid (.init (.erase 0))))))
noncomputable def nativeMachine (F : RationalMobius) := NativeMicrocode.machine (nativeEncoding F) (program F)

end TransposeFollowup.SourceImages


/-! Framed calls into the source routine, each signed form, and the
single-word eraser. The source flag is retained only in finite labels. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_source (F : RationalMobius)
    (pc : SourceEndpoints.Label (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F))
    (b : SourceEndpoints.Bank) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed sourceBinding.ports (Label.source (F := F))
      (SourceEndpoints.cfg pc b (fun p => pos (sourceBinding.ports p))) (frame s pos)=
      cfg (.source pc) {s with source := b} pos := by
  unfold MicrocodeEmbedding.embed SourceEndpoints.cfg cfg frame
  simp only [← sourceBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_form (F : RationalMobius) (saved : Bool) (j : Fin 4)
    (pc : SignedLinearForm.Label (u F j) (v F j)) (b : SignedLinearForm.Bank)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (formBinding j).ports (Label.form saved j)
      (SignedLinearForm.cfg pc b (fun p => pos ((formBinding j).ports p))) (frame s pos)=
      cfg (.form saved j pc) (placeForm j b s) pos := by
  unfold MicrocodeEmbedding.embed SignedLinearForm.cfg cfg frame
  simp only [← (formBinding j).values_eq_extend]
  fin_cases j <;> congr 2 <;> funext p
  all_goals cases p with
  | source p => cases p with
    | shared p => cases p <;> rfl
    | other k => rfl
  | work k => rfl
  | out k b => fin_cases k <;> rfl

theorem embed_erase (F : RationalMobius) (saved : Bool) (j k : Fin 3) (pc : NativeErase.Label)
    (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding k).ports (Label.erase (F := F) saved j k)
      (NativeErase.cfg pc w (fun p => pos ((eraseBinding k).ports p))).denote (frame s pos)=
      cfg (.erase saved j k pc) (s.set (.work k) w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (eraseBinding k).values_eq_extend]
  congr 2 <;> funext p
  all_goals
    by_cases hp : p=.work k
    · subst p
      simp [eraseBinding,FinitePortBinding.values,Microcode.focus,Function.update] <;> rfl
    · simp [eraseBinding,FinitePortBinding.values,Function.update,hp]

abbrev Trace (F : RationalMobius) :=
  OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem jump_trace (F : RationalMobius) (pc next : Label F) (s : Bank) (pos : Port → ℤ)
    (h : program F pc=.jump next) : Trace F 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem source_call (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (s : Bank) (pos : Port → ℤ) :
    ∃ t≤SourceEndpoints.budget (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) n.length,
      Trace F t (cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) {s with source := SourceEndpoints.initial n iw} pos)
        (cfg (.source (.done (sourceAnswer F n iw))) {s with source := sourceFinal F n iw} pos) := by
  obtain ⟨t,ht,htr⟩ := SourceEndpoints.complete_trace (SourceEndpoints.magnitude F)
    (SourceEndpoints.denominator F) (SourceEndpoints.negative F) n iw hm hi
    (fun p => pos (sourceBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed sourceBinding.ports (Label.source (F := F))
    (SourceEndpoints.program (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) (SourceEndpoints.negative F))
    (program F) (frame s pos) (source_code F) htr
  exact ⟨t,ht,by simpa only [embed_source,sourceAnswer,sourceFinal] using he⟩

theorem form_call (F : RationalMobius) (saved : Bool) (j : Fin 4) (xs : Fin 3 → List Bool)
    (h : ∀ k,(xs k).length=(xs 0).length) (s : Bank) (pos : Port → ℤ) :
    ∃ t≤SignedLinearForm.budget (u F j) (v F j) (xs 0).length,
      Trace F t (cfg (.form saved j (.init 0 (.init (.erase 0)))) (placeForm j (SignedLinearForm.initial xs) s) pos)
        (cfg (.form saved j .done) (placeForm j (SignedLinearForm.final (u F j) (v F j) xs) s) pos) := by
  obtain ⟨t,ht,htr⟩ := SignedLinearForm.complete_trace (u F j) (v F j) xs h
    (fun p => pos ((formBinding j).ports p))
  have he := MicrocodeEmbedding.trace_embed (formBinding j).ports (Label.form saved j)
    (SignedLinearForm.program (u F j) (v F j)) (program F) (frame s pos) (form_code F saved j) htr
  exact ⟨t,ht,by simpa only [embed_form] using he⟩

theorem erase_call (F : RationalMobius) (saved : Bool) (j k : Fin 3)
    (xs : List Bool) (s : Bank) (hs : s.tapes (.work k)=Counter.marked xs) (pos : Port → ℤ) :
    ∃ t≤4*xs.length+4, Trace F t (cfg (.erase saved j k 2) s pos)
      (cfg (.erase saved j k 0) (s.set (.work k) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun p => pos ((eraseBinding k).ports p))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding k).ports (Label.erase saved j k)
    NativeErase.program (program F) (frame s pos) (erase_code F saved j k) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Bank.set_self] using he⟩

end TransposeFollowup.SourceImages


/-! Source extraction, individual image forms and the three-word cleanup
connect exact concrete banks. All return labels charge their own jump. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem source_stage (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ) :
    ∃ t≤SourceEndpoints.budget (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) n.length+1,
      Trace F t (cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) (initial n iw) pos)
        (cfg (.form (sourceAnswer F n iw) 0 (.init 0 (.init (.erase 0)))) (before F n iw 0) pos) := by
  obtain ⟨t,ht,htr⟩ := source_call F n iw hm hi (initial n iw) pos
  have hj := jump_trace F (.source (.done (sourceAnswer F n iw)))
    (.form (sourceAnswer F n iw) 0 (.init 0 (.init (.erase 0))))
    {initial n iw with source := sourceFinal F n iw} pos rfl
  exact ⟨t+1,Nat.add_le_add_right ht 1,by simpa [initial,before] using trace_trans htr hj⟩

theorem form_stage (F : RationalMobius) (saved : Bool) (n iw : List Bool)
    (hm : 0<n.length) (hi : iw.length=n.length) (j : Fin 4) (pos : Port → ℤ) :
    ∃ t≤SignedLinearForm.budget (u F j) (v F j) n.length+1,
      Trace F t (cfg (.form saved j (.init 0 (.init (.erase 0)))) (before F n iw j.val) pos)
        (cfg (afterCall F saved j) (afterForm F n iw j) pos) := by
  have hl := args_length F n iw hm hi j
  obtain ⟨t,ht,htr⟩ := form_call F saved j (args F n iw j)
    (fun k => (hl k).trans (hl 0).symm) (before F n iw j.val) pos
  rw [hl 0] at ht
  rw [form_initial F n iw hm hi j,form_final F n iw hm hi j] at htr
  have hj := jump_trace F (.form saved j .done) (afterCall F saved j) (afterForm F n iw j) pos rfl
  exact ⟨t+1,Nat.add_le_add_right ht 1,trace_trans htr hj⟩

theorem erase_stage (F : RationalMobius) (saved : Bool) (n iw : List Bool)
    (hm : 0<n.length) (hi : iw.length=n.length) (j k : Fin 3) (pos : Port → ℤ) :
    ∃ t≤4*n.length+5, Trace F t
      (cfg (.erase saved j k 2) (erasing F n iw (prior j) k.val) pos)
      (cfg (afterErase F saved j k) (erasing F n iw (prior j) (k.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := erase_call F saved j k (product F n iw (prior j) k)
    (erasing F n iw (prior j) k.val) (erasing_source _ _ _ _ _) pos
  rw [product_length F n iw hm hi] at ht
  rw [erasing_step] at htr
  have hj := jump_trace F (.erase saved j k 0) (afterErase F saved j k)
    (erasing F n iw (prior j) (k.val+1)) pos (by simp [program])
  exact ⟨t+1,by omega,trace_trans htr hj⟩

theorem cleanup (F : RationalMobius) (saved : Bool) (n iw : List Bool)
    (hm : 0<n.length) (hi : iw.length=n.length) (j : Fin 3) (pos : Port → ℤ) :
    ∃ t≤12*n.length+15, Trace F t
      (cfg (.erase saved j 0 2) (afterForm F n iw (prior j)) pos)
      (cfg (.form saved (next j) (.init 0 (.init (.erase 0)))) (before F n iw (next j).val) pos) := by
  obtain ⟨a,ha,h0⟩ := erase_stage F saved n iw hm hi j 0 pos
  obtain ⟨b,hb,h1⟩ := erase_stage F saved n iw hm hi j 1 pos
  obtain ⟨c,hc,h2⟩ := erase_stage F saved n iw hm hi j 2 pos
  have h := trace_trans h0 (trace_trans h1 h2)
  exact ⟨a+(b+c),by omega,by simpa [afterErase,erasing_zero,erasing_three,next,prior] using h⟩

end TransposeFollowup.SourceImages


/-! Both endpoints and all four image pairs are one paid computation.
Nine product erasures and every transfer are included. Final work products
remain stored; the caller does not promise free cleanup between rows. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def budget (F : RationalMobius) (m : ℕ) : ℕ :=
  SourceEndpoints.budget (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) m+
    2*(SignedLinearForm.budget F.integralA F.integralB m+SignedLinearForm.budget F.integralC F.integralD m)+36*m+50

theorem complete_trace (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ) :
    ∃ t≤budget F n.length, Trace F t
      (cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) (initial n iw) pos)
      (cfg (.done (sourceAnswer F n iw)) (final F n iw) pos) := by
  obtain ⟨a,ha,hs⟩ := source_stage F n iw hm hi pos
  obtain ⟨b,hb,h0⟩ := form_stage F (sourceAnswer F n iw) n iw hm hi 0 pos
  obtain ⟨c,hc,hc0⟩ := cleanup F (sourceAnswer F n iw) n iw hm hi 0 pos
  obtain ⟨d,hd,h1⟩ := form_stage F (sourceAnswer F n iw) n iw hm hi 1 pos
  obtain ⟨e,he,hc1⟩ := cleanup F (sourceAnswer F n iw) n iw hm hi 1 pos
  obtain ⟨f,hf,h2⟩ := form_stage F (sourceAnswer F n iw) n iw hm hi 2 pos
  obtain ⟨g,hg,hc2⟩ := cleanup F (sourceAnswer F n iw) n iw hm hi 2 pos
  obtain ⟨h,hh,h3⟩ := form_stage F (sourceAnswer F n iw) n iw hm hi 3 pos
  refine ⟨a+(b+(c+(d+(e+(f+(g+h)))))),?_,?_⟩
  · simp only [u,v,denominator,stage,SignedLinearForm.coefficients] at hb hd hf hh
    norm_num at hb hd hf hh
    dsimp [budget]
    omega
  · exact trace_trans hs (trace_trans h0 (trace_trans hc0 (trace_trans h1
      (trace_trans hc1 (trace_trans h2 (trace_trans hc2 h3))))))

theorem native_complete (F : RationalMobius) (n iw : List Bool) (hm : 0<n.length)
    (hi : iw.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget F n.length,
      Transpose.stepN (nativeMachine F) input t
        ((cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) (initial n iw) pos).denote
          (nativeEncoding F) (program F) inputPos outRev)=
        some ((cfg (.done (sourceAnswer F n iw)) (final F n iw) pos).denote
          (nativeEncoding F) (program F) inputPos outRev) ∧
      Transpose.step (nativeMachine F) input
        ((cfg (.done (sourceAnswer F n iw)) (final F n iw) pos).denote
          (nativeEncoding F) (program F) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hi pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding F) (program F) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding F) (program F) input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ} (F : RationalMobius)
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label F → J)
    (target : Microcode.Program U J) (frame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program F pc≠.halt → program F pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program F pc))
    (n iw : List Bool) (hm : 0<n.length) (hi : iw.length=n.length) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget F n.length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) (initial n iw) pos) frame).denote
            encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done (sourceAnswer F n iw)) (final F n iw) pos) frame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hi pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program F) target
    frame input inputPos outRev hc htr⟩

end TransposeFollowup.SourceImages


/-! The number of tapes and states is independent of dimension and width.
The budget includes source preparation, all four forms and nine erasures. -/

namespace TransposeFollowup.SourceImages
set_option autoImplicit false

def coefficientSum (F : RationalMobius) : ℕ :=
  2*F.integralA.natAbs+F.integralB.natAbs+2*F.integralC.natAbs+F.integralD.natAbs
def sourceSum (F : RationalMobius) : ℕ :=
  SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false+
    SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true

def labelEquiv (F : RationalMobius) : Label F ≃
    SourceEndpoints.Label (SourceEndpoints.magnitude F) (SourceEndpoints.denominator F) ⊕
    (Bool × (Σ j : Fin 4, SignedLinearForm.Label (u F j) (v F j))) ⊕
    (Bool × Fin 3 × Fin 3 × NativeErase.Label) ⊕ Bool where
  toFun
    | .source pc => .inl pc
    | .form saved j pc => .inr (.inl (saved,⟨j,pc⟩))
    | .erase saved j k pc => .inr (.inr (.inl (saved,j,k,pc)))
    | .done saved => .inr (.inr (.inr saved))
  invFun
    | .inl pc => .source pc
    | .inr (.inl (saved,⟨j,pc⟩)) => .form saved j pc
    | .inr (.inr (.inl (saved,j,k,pc))) => .erase saved j k pc
    | .inr (.inr (.inr saved)) => .done saved
  left_inv := by intro pc; cases pc <;> rfl
  right_inv := by rintro (pc | ⟨saved,⟨j,pc⟩⟩ | ⟨saved,j,k,pc⟩ | saved) <;> rfl

theorem label_card (F : RationalMobius) : Fintype.card (Label F)=
    198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
    396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*coefficientSum F+7157 := by
  have h := Fintype.card_congr (labelEquiv F)
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  have hm : (∑ j : Fin 4,(99*(2*(u F j).natAbs+(v F j).natAbs)+520))=198*coefficientSum F+2080 := by
    norm_num [Fin.sum_univ_succ,u,v,denominator,stage,SignedLinearForm.coefficients,coefficientSum]
    omega
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_sigma,Fintype.card_fin,Fintype.card_bool,
    he,SourceEndpoints.label_card,SignedLinearForm.label_card] at h
  rw [hm] at h
  exact h.trans (by ring)

theorem fixed_resources (F : RationalMobius) : (nativeMachine F).k=28 ∧
    (nativeMachine F).g+1=5 ∧ (nativeMachine F).q+1=
      198*(SourceEndpoints.magnitude F false+SourceEndpoints.denominator F false)+
      396*(SourceEndpoints.magnitude F true+SourceEndpoints.denominator F true)+396*coefficientSum F+7157 ∧
    (nativeEncoding F).label (.source (.lower (.inl (.grid (.init (.erase 0))))))=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=28
    decide +kernel
  · change Fintype.card (Label F)-1+1=_
    rw [label_card]
    omega

theorem budget_expansion (F : RationalMobius) (m : ℕ) :
    budget F m=436*m+1105+2*(sourceSum F+coefficientSum F)*(18*m+52) := by
  unfold budget SourceEndpoints.budget GuardedEndpoint.budget EndpointClip.budget
    EndpointGuard.budget SignedLinearForm.budget sourceSum coefficientSum
  ring

theorem total_budget (F : RationalMobius) (N : ℕ) (xs : List Bool)
    (hN : 1≤N) (hl : xs.length≤(N+1).size) :
    let T := sourceSum F+coefficientSum F
    N*(N*budget F (PaddedWord.word (PaddedWord.commonConstant F) id xs).length) ≤
      ((872+72*T)*(F.integerOperandConstant^2).size+10930+928*T)*Transpose.inputLength N := by
  let T := sourceSum F+coefficientSum F
  have he : budget F (PaddedWord.word (PaddedWord.commonConstant F) id xs).length=
      ((436+36*T)*PaddedWord.commonConstant F+1105+104*T)+(872+72*T)*xs.length := by
    rw [budget_expansion,PaddedWord.word_length]
    unfold T
    ring
  have h := dense_scan_budget ((436+36*T)*PaddedWord.commonConstant F+1105+104*T) (872+72*T) N hN
  rw [he]
  calc
    _ ≤ N*(N*(((436+36*T)*PaddedWord.commonConstant F+1105+104*T)+(872+72*T)*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    _ ≤ _ := by
      convert h using 1
      unfold PaddedWord.commonConstant
      ring

end TransposeFollowup.SourceImages


/-! One native call produces both clipped fractions, all eight exact
image-component words, and the original source-open flag. Fits follow
from the existing endpoint bounds; empty intersections are included. -/

namespace TransposeFollowup.SourceImages
open FixedTapeCompiler
set_option autoImplicit false

theorem final_source (F : RationalMobius) (n iw : List Bool) :
    (final F n iw).source=sourceFinal F n iw := rfl

theorem final_output (F : RationalMobius) (n iw : List Bool) (j : Fin 4) (b : Bool) :
    (final F n iw).out j b=Counter.marked (imageWord F n iw j b) := by
  simp [final,afterForm,before]

theorem source_words (F : RationalMobius) (n iw : List Bool) (up : Bool) (k : Fin 3) :
    SourceEndpoints.outputBank (final F n iw).source up k=
      Counter.marked (SourceEndpoints.outputWords (SourceEndpoints.magnitude F)
        (SourceEndpoints.denominator F) (SourceEndpoints.negative F) n iw up k) :=
  SourceEndpoints.final_words _ _ _ _ _ up k

theorem image_values (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (j : Fin 4) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    SignedComponents.Pair.mk (Counter.value (imageWord F n iw j false))
      (Counter.value (imageWord F n iw j true))=
      SignedLinearForm.imageComponent F (if upper j then F.rightPair i else F.leftPair i) (denominator j) := by
  dsimp only
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := by
    dsimp [n]
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  have hlen := args_length F n iw hm hl j
  have heq (k : Fin 3) : (args F n iw j k).length=(args F n iw j 0).length :=
    (hlen k).trans (hlen 0).symm
  have hmass := SignedLinearForm.endpoint_mass_fits F source i iw hl hv (upper j) (denominator j)
  change (SignedLinearForm.components (u F j) (v F j)
    (Counter.value (args F n iw j 0)) (Counter.value (args F n iw j 1))
    (Counter.value (args F n iw j 2))).mass<2^(args F n iw j 0).length at hmass
  change SignedComponents.Pair.mk
    (Counter.value (SignedLinearForm.outputWord (u F j) (v F j) (args F n iw j) false))
    (Counter.value (SignedLinearForm.outputWord (u F j) (v F j) (args F n iw j) true))=_
  rw [SignedLinearForm.outputWord_value _ _ _ heq hmass false,
    SignedLinearForm.outputWord_value _ _ _ heq hmass true]
  exact SignedLinearForm.endpoint_components F source i iw hl hv (upper j) (denominator j)

theorem rational_complete_trace (F : RationalMobius) (source : List Bool)
    (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    let sw := SourceEndpoints.outputWords (SourceEndpoints.magnitude F)
      (SourceEndpoints.denominator F) (SourceEndpoints.negative F) n iw
    ∃ t≤budget F n.length, ∃ w : Fin 4 → Bool → List Bool,
      Trace F t (cfg (.source (.lower (.inl (.grid (.init (.erase 0)))))) (initial n iw) pos)
        (cfg (.done ((F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight)) (final F n iw) pos) ∧
      (∀ up k,SourceEndpoints.outputBank (final F n iw).source up k=Counter.marked (sw up k)) ∧
      (∀ up,let p := if up then F.rightPair i else F.leftPair i
        (Counter.value (sw up 0),Counter.value (sw up 1),Counter.value (sw up 2))=
          (p.1.toNat,(-p.1).toNat,p.2.toNat)) ∧
      (∀ j b,(final F n iw).out j b=Counter.marked (w j b)) ∧
      (∀ j,SignedComponents.Pair.mk (Counter.value (w j false)) (Counter.value (w j true))=
        SignedLinearForm.imageComponent F (if upper j then F.rightPair i else F.leftPair i) (denominator j)) ∧
      (∀ j b,(w j b).length=n.length) := by
  dsimp only
  let n := PaddedWord.word (PaddedWord.commonConstant F) id source
  have hm : 0<n.length := by
    dsimp [n]
    rw [PaddedWord.word_length]
    unfold PaddedWord.commonConstant
    omega
  obtain ⟨t,ht,htr⟩ := complete_trace F n iw hm hl pos
  have ha : sourceAnswer F n iw=(F.componentRow i).sourceLeft.less (F.componentRow i).sourceRight :=
    SourceEndpoints.answer_rational F source i iw hl hv
  rw [ha] at htr
  exact ⟨t,ht,imageWord F n iw,htr,source_words F n iw,
    SourceEndpoints.rational_words F source i iw hl hv,final_output F n iw,
    image_values F source i iw hl hv,imageWord_length F n iw hm hl⟩

end TransposeFollowup.SourceImages


/-! Reference words for paid dimension scaling. The row mass bound proves
all four image-numerator products fit the common width, and their pairs are
exactly the lower/upper thresholds. DimensionScaleRun realizes this budget
with an actual native program. -/

namespace TransposeFollowup.DimensionScale
open FixedTapeCompiler SignedComponents
set_option autoImplicit false

def output (n x : List Bool) : List Bool :=
  RepeatedAdd.repeatWord x (Counter.value n) (ArithmeticSeed.zeros x.length)

/-- Native allowance: two copies, the counted adder, one fuel erasure and
four transfers. Its realization is proved in DimensionScaleRun. -/
def budget (n x : List Bool) : ℕ :=
  RepeatedAdd.budget n x+10*n.length+6*x.length+36

theorem budget_expansion (n x : List Bool) :
    budget n x=Counter.value n*(18*x.length+39)+14*n.length+6*x.length+44 := by
  unfold budget RepeatedAdd.budget
  ring

/-- N rows allow N additions per row. This sums the operation budgets;
composing row calls must still account for their workspace and outputs. -/
theorem total_budget (F : RationalMobius) (N : ℕ) (source x : List Bool)
    (hN : 1≤N) (hv : Counter.value source=N) (hl : source.length≤(N+1).size)
    (hx : x.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) :
    N*budget (PaddedWord.word (PaddedWord.commonConstant F) id source) x ≤
      (76*(F.integerOperandConstant^2).size+926)*Transpose.inputLength N := by
  let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
  have he : budget (PaddedWord.word (PaddedWord.commonConstant F) id source) x=
      N*(18*m+39)+20*m+44 := by
    rw [budget_expansion,PaddedWord.common_value,hv,hx]
    dsimp [m]
    ring
  have htail : 20*m+44≤N*(20*m+44) := Nat.le_mul_of_pos_left _ hN
  have hd := dense_scan_budget (38*PaddedWord.commonConstant F+83) 76 N hN
  rw [he]
  calc
    _ ≤ N*(N*(38*m+83)) := by apply Nat.mul_le_mul_left; nlinarith
    _ ≤ N*(N*((38*PaddedWord.commonConstant F+83)+76*(N+1).size)) := by
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul_left
      dsimp [m]
      rw [PaddedWord.word_length]
      omega
    _ ≤ _ := by
      have hc : 2*((38*PaddedWord.commonConstant F+83)+3*76)=
          76*(F.integerOperandConstant^2).size+926 := by
        unfold PaddedWord.commonConstant
        omega
      simpa only [hc] using hd

theorem output_length (n x : List Bool) : (output n x).length=x.length :=
  RepeatedAdd.repeatWord_length _ _ _ (by simp [ArithmeticSeed.zeros])

theorem output_value_mod (n x : List Bool) :
    Counter.value (output n x)=Counter.value n*Counter.value x%2^x.length := by
  have h := RepeatedAdd.output_value n (ArithmeticSeed.zeros x.length) x (by simp [ArithmeticSeed.zeros])
  simpa only [output,← NativeCounter.word_value,ArithmeticSeed.zeros,PaddedWord.value_zeroes,Nat.zero_add] using h

theorem output_value_exact (n x : List Bool) (hf : Counter.value n*Counter.value x<2^x.length) :
    Counter.value (output n x)=Counter.value n*Counter.value x := by
  rw [output_value_mod,Nat.mod_eq_of_lt hf]

def numeratorStage (upper : Bool) : Fin 4 := if upper then 2 else 0

def factor (F : RationalMobius) (source iw : List Bool) (upper sign : Bool) : List Bool :=
  SourceImages.imageWord F (PaddedWord.word (PaddedWord.commonConstant F) id source) iw (numeratorStage upper) sign

theorem factor_length (F : RationalMobius) (source iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length) (upper sign : Bool) :
    (factor F source iw upper sign).length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  apply SourceImages.imageWord_length _ _ _ _ hl
  rw [PaddedWord.word_length]
  unfold PaddedWord.commonConstant
  omega

theorem scaled_pair_expected (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper : Bool) :
    Pair.mk (Counter.value source*Counter.value (factor F source iw upper false))
      (Counter.value source*Counter.value (factor F source iw upper true))=
      if upper then (F.componentRow i).upper else (F.componentRow i).lower := by
  have h := SourceImages.image_values F source i iw hl hv (numeratorStage upper)
  have hs := congrArg (Pair.scale (Counter.value source)) h
  cases upper <;> simpa [numeratorStage,SourceImages.upper,SourceImages.denominator,SourceImages.stage,
    SignedLinearForm.imageComponent,RationalMobius.componentRow,Pair.scale,factor] using hs

theorem scaled_mass_fit (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper : Bool) :
    (Pair.mk (Counter.value source*Counter.value (factor F source iw upper false))
      (Counter.value source*Counter.value (factor F source iw upper true))).mass<
      2^(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  rw [scaled_pair_expected F source i iw hl hv upper]
  apply lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide) (PaddedWord.common_width_sufficient F source))
  have h := F.componentRow_comparison_fit i 0 (by omega)
  cases upper
  · exact h _ (by simp) _ (by simp)
  · exact h _ (by simp) _ (by simp)

theorem factor_product_fit (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper sign : Bool) :
    Counter.value (PaddedWord.word (PaddedWord.commonConstant F) id source)*
      Counter.value (factor F source iw upper sign)<2^(factor F source iw upper sign).length := by
  rw [PaddedWord.common_value,factor_length F source iw hl upper sign]
  have h := scaled_mass_fit F source i iw hl hv upper
  dsimp only [Pair.mass] at h
  cases sign <;> omega

theorem exact_scaled_pair (F : RationalMobius) (source : List Bool) (i : Fin (Counter.value source))
    (iw : List Bool) (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper : Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    Pair.mk (Counter.value (output n (factor F source iw upper false)))
      (Counter.value (output n (factor F source iw upper true)))=
      if upper then (F.componentRow i).upper else (F.componentRow i).lower := by
  dsimp only
  rw [output_value_exact _ _ (factor_product_fit F source i iw hl hv upper false),
    output_value_exact _ _ (factor_product_fit F source i iw hl hv upper true),PaddedWord.common_value]
  exact scaled_pair_expected F source i iw hl hv upper

end TransposeFollowup.DimensionScale


/-! Runtime scaling with a physical counter. The dimension and factor are
preserved; temporary fuel is initialized by copying and erased after use.
The machine has fixed finite control, independent of both input values. -/

namespace TransposeFollowup.DimensionScale
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

inductive Port | dimension | factor | zero | scratch | fuel | out
  deriving DecidableEq

instance : Fintype Port where
  elems := {.dimension,.factor,.zero,.scratch,.fuel,.out}
  complete := by intro p; cases p <;> simp

@[ext] structure Bank where
  dimension : Tape Bool
  factor : Tape Bool
  zero : Tape Bool
  scratch : Tape Bool
  fuel : Tape Bool
  out : Tape Bool

def Bank.tapes (s : Bank) : Port → Tape Bool
  | .dimension => s.dimension | .factor => s.factor | .zero => s.zero
  | .scratch => s.scratch | .fuel => s.fuel | .out => s.out

def Bank.set (s : Bank) (p : Port) (w : Tape Bool) : Bank := match p with
  | .dimension => {s with dimension := w} | .factor => {s with factor := w}
  | .zero => {s with zero := w} | .scratch => {s with scratch := w}
  | .fuel => {s with fuel := w} | .out => {s with out := w}

@[simp] theorem Bank.set_tapes (s : Bank) (p q : Port) (w : Tape Bool) :
    (s.set p w).tapes q=Function.update s.tapes p w q := by
  cases p <;> cases q <;> simp [Bank.set,Bank.tapes,Function.update]

@[simp] theorem Bank.set_self (s : Bank) (p : Port) : s.set p (s.tapes p)=s := by
  cases p <;> rfl

def initial (n x : List Bool) : Bank where
  dimension := Counter.marked n
  factor := Counter.marked x
  zero := Counter.marked (ArithmeticSeed.zeros x.length)
  scratch := BinaryCarry.preparedOutput
  fuel := ⟨[],[]⟩
  out := ⟨[],[]⟩

def fueled (n x : List Bool) : Bank := {initial n x with fuel := Counter.marked n}
def ready (n x : List Bool) : Bank :=
  {fueled n x with out := Counter.marked (ArithmeticSeed.zeros x.length)}
def dirty (n x : List Bool) : Bank :=
  {initial n x with fuel := Counter.marked (List.replicate n.length true), out := Counter.marked (output n x)}
def final (n x : List Bool) : Bank := {initial n x with out := Counter.marked (output n x)}

def pairBinding (a b : Port) (hab : a≠b) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![a,b], by intro j k h; fin_cases j <;> fin_cases k <;> simp_all⟩
  decode := fun p => if p=a then some 0 else if p=b then some 1 else none
  decode_spec := by
    intro p j
    change (if p=a then some 0 else if p=b then some 1 else none)=some j ↔ ![a,b] j=p
    fin_cases j <;> by_cases ha : p=a <;> by_cases hb : p=b <;> simp_all [eq_comm]

def fuelBinding := pairBinding .dimension .fuel (by decide)
def zeroBinding := pairBinding .zero .out (by decide)

def multiplyPort : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .out | .factor => .factor | .scratch => .scratch | .zero => .zero
def multiplyBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨multiplyPort, by intro p q h; cases p <;> cases q <;> simp_all [multiplyPort]⟩
  decode := fun p => match p with
    | .fuel => some .fuel | .out => some .acc | .factor => some .factor
    | .scratch => some .scratch | .zero => some .zero | .dimension => none
  decode_spec := by intro p t; cases p <;> cases t <;> decide +kernel

def eraseBinding : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => .fuel, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=.fuel then some 0 else none
  decode_spec := by intro p t; cases p <;> fin_cases t <;> decide +kernel

inductive Label
  | fuelCopy (pc : NativeMappedCopy.Label)
  | zeroCopy (pc : NativeMappedCopy.Label)
  | multiply (pc : RepeatedAdd.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .fuelCopy (.init (.erase 0))

def program : Microcode.Program Port Label
  | .fuelCopy (.seal .done) => .jump (.zeroCopy (.init (.erase 0)))
  | .fuelCopy pc => fuelBinding.instruction Label.fuelCopy (NativeMappedCopy.program id pc)
  | .zeroCopy (.seal .done) => .jump (.multiply (.counter 0))
  | .zeroCopy pc => zeroBinding.instruction Label.zeroCopy (NativeMappedCopy.program id pc)
  | .multiply (.counter pc) => if pc=12 then .jump (.erase 2)
      else multiplyBinding.instruction Label.multiply (RepeatedAdd.program (.counter pc))
  | .multiply pc => multiplyBinding.instruction Label.multiply (RepeatedAdd.program pc)
  | .erase pc => if pc=0 then .jump .done else eraseBinding.instruction Label.erase (NativeErase.program pc)
  | .done => .halt

theorem fuel_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.fuelCopy pc)=MicrocodeEmbedding.instruction fuelBinding.ports Label.fuelCopy (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem zero_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.zeroCopy pc)=MicrocodeEmbedding.instruction zeroBinding.ports Label.zeroCopy (NativeMappedCopy.program id pc) := by
  have hp : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem multiply_code (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt)
    (_ : RepeatedAdd.program pc≠.reject) :
    program (.multiply pc)=MicrocodeEmbedding.instruction multiplyBinding.ports Label.multiply (RepeatedAdd.program pc) := by
  have hp : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  cases pc <;> simp_all [program,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction eraseBinding.ports Label.erase (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,hp,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (s.tapes p).denote⟩,pos⟩
def zipperCfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc,s.tapes⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s.tapes p).denote,pos⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=6 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=156 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=6
    decide +kernel
  · change Fintype.card Label-1+1=156
    decide +kernel

end TransposeFollowup.DimensionScale


/-! Framed native calls preserve the immutable dimension, factor and templates.
The eraser returns genuinely blank fuel, including removal of both markers. -/

namespace TransposeFollowup.DimensionScale
open FixedTapeCompiler
open CopyMachine (Tape)
set_option autoImplicit false

theorem embed_copy (p q : Port) (hpq : p≠q)
    (labels : NativeMappedCopy.Label → Label) (pc : NativeMappedCopy.Label)
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

theorem embed_multiply (pc : RepeatedAdd.Label) (b : RepeatedAdd.Bank)
    (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed multiplyBinding.ports Label.multiply
      (RepeatedAdd.cfg pc b (fun t => pos (multiplyBinding.ports t))) (frame s pos)=
      cfg (.multiply pc)
        {s with fuel := b.fuel, out := b.acc, factor := b.factor, scratch := b.scratch, zero := b.zero} pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← multiplyBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_erase (pc : NativeErase.Label) (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed eraseBinding.ports Label.erase
      (NativeErase.cfg pc w (fun t => pos (eraseBinding.ports t))).denote (frame s pos)=
      cfg (.erase pc) (s.set .fuel w) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← eraseBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem mapped_call (p q : Port) (hpq : p≠q) (labels : NativeMappedCopy.Label → Label)
    (hc : ∀ pc, NativeMappedCopy.program id pc≠.halt → NativeMappedCopy.program id pc≠.reject →
      program (labels pc)=MicrocodeEmbedding.instruction (pairBinding p q hpq).ports
        labels (NativeMappedCopy.program id pc))
    (xs : List Bool) (s : Bank) (hs : s.tapes p=Counter.marked xs)
    (hq : s.tapes q=⟨[],[]⟩) (pos : Port → ℤ) :
    ∃ t≤6*xs.length+14, Trace t (cfg (labels (.init (.erase 0))) s pos)
      (cfg (labels (.seal .done)) (s.set q (Counter.marked xs)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun t => pos ((pairBinding p q hpq).ports t))
  have he := MicrocodeEmbedding.trace_embed (pairBinding p q hpq).ports labels
    (NativeMappedCopy.program id) program (frame s pos) hc htr
  exact ⟨t,ht,by simpa only [embed_copy,List.map_id,← hs,Bank.set_self,← hq] using he⟩

theorem multiply_call (n x : List Bool) (pos : Port → ℤ) :
    ∃ t≤RepeatedAdd.budget n x, Trace t
      (cfg (.multiply (.counter 0)) (ready n x) pos)
      (cfg (.multiply (.counter 12)) (dirty n x) pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.repeated_add_trace n (ArithmeticSeed.zeros x.length) x
    (by simp [ArithmeticSeed.zeros]) (fun p => pos (multiplyBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed multiplyBinding.ports Label.multiply
    RepeatedAdd.program program (frame (initial n x) pos) multiply_code htr
  exact ⟨t,ht,by simpa only [embed_multiply,RepeatedAdd.ready,ready,fueled,dirty,initial,
    output,ArithmeticSeed.zeros,Counter.marked,BinaryCarry.marked,BinaryCompare.marked] using he⟩

theorem erase_call (xs : List Bool) (s : Bank) (hs : s.tapes .fuel=Counter.marked xs)
    (pos : Port → ℤ) :
    ∃ t≤4*xs.length+4, Trace t (cfg (.erase 2) s pos)
      (cfg (.erase 0) (s.set .fuel ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun p => pos (eraseBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed eraseBinding.ports Label.erase
    NativeErase.program program (frame s pos) erase_code htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Bank.set_self] using he⟩

end TransposeFollowup.DimensionScale


/-! Complete native scaling: two copies, a physical-counter arithmetic call,
fuel erasure, and four charged transfers. Dimension and factor widths may
differ, including width zero. No fresh fuel is assumed between calls. -/

namespace TransposeFollowup.DimensionScale
open FixedTapeCompiler
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem complete_trace (n x : List Bool) (pos : Port → ℤ) :
    ∃ t≤budget n x, Trace t (cfg start (initial n x) pos) (cfg .done (final n x) pos) := by
  obtain ⟨a,ha,ta⟩ := mapped_call .dimension .fuel (by decide) Label.fuelCopy fuel_code
    n (initial n x) rfl rfl pos
  change Trace a (cfg start (initial n x) pos) (cfg (.fuelCopy (.seal .done)) (fueled n x) pos) at ta
  have ja := jump_trace (.fuelCopy (.seal .done)) (.zeroCopy (.init (.erase 0))) (fueled n x) pos rfl
  obtain ⟨b,hb,tb⟩ := mapped_call .zero .out (by decide) Label.zeroCopy zero_code
    (ArithmeticSeed.zeros x.length) (fueled n x) rfl rfl pos
  change Trace b (cfg (.zeroCopy (.init (.erase 0))) (fueled n x) pos)
    (cfg (.zeroCopy (.seal .done)) (ready n x) pos) at tb
  have jb := jump_trace (.zeroCopy (.seal .done)) (.multiply (.counter 0)) (ready n x) pos rfl
  obtain ⟨c,hc,tc⟩ := multiply_call n x pos
  have jc := jump_trace (.multiply (.counter 12)) (.erase 2) (dirty n x) pos (by simp [program])
  obtain ⟨d,hd,td⟩ := erase_call (List.replicate n.length true) (dirty n x) rfl pos
  change Trace d (cfg (.erase 2) (dirty n x) pos) (cfg (.erase 0) (final n x) pos) at td
  have jd := jump_trace (.erase 0) .done (final n x) pos (by simp [program])
  refine ⟨a+(1+(b+(1+(c+(1+(d+1)))))),?_,?_⟩
  · simp only [ArithmeticSeed.zeros,List.length_replicate] at hb hd
    unfold budget
    omega
  · exact trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb
      (trace_trans tc (trace_trans jc (trace_trans td jd))))))

theorem native_complete (n x : List Bool) (pos : Port → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget n x,
      Transpose.stepN nativeMachine input t
        ((cfg start (initial n x) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done (final n x) pos).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done (final n x) pos).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace n x pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h
  exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (n x : List Bool) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t≤budget n x,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (initial n x) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final n x) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace n x pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

/-- The returned temporary counter is blank; only the designated output
changes from the initial bank. This also specifies the reusable templates. -/
theorem final_tapes (n x : List Bool) (p : Port) :
    (final n x).tapes p=if p=.out then Counter.marked (output n x) else (initial n x).tapes p := by
  cases p <;> rfl

theorem complete_exact_trace (n x : List Bool)
    (hf : Counter.value n*Counter.value x<2^x.length) (pos : Port → ℤ) :
    ∃ (t : ℕ) (y : List Bool), t≤budget n x ∧ y.length=x.length ∧
      Counter.value y=Counter.value n*Counter.value x ∧
      Trace t (cfg start (initial n x) pos)
        (cfg .done {initial n x with out := Counter.marked y} pos) := by
  obtain ⟨t,ht,htr⟩ := complete_trace n x pos
  exact ⟨t,output n x,ht,output_length n x,output_value_exact n x hf,htr⟩

end TransposeFollowup.DimensionScale


/-! The actual native scaler computes each row-threshold component. The
common-width bounds discharge overflow; it is not an extra precondition. -/

namespace TransposeFollowup.DimensionScale
open FixedTapeCompiler SignedComponents
set_option autoImplicit false

theorem threshold_component (F : RationalMobius) (source : List Bool)
    (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper sign : Bool) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    let p := if upper then (F.componentRow i).upper else (F.componentRow i).lower
    Counter.value (output n (factor F source iw upper sign))=
      if sign then p.negative else p.positive := by
  have h := exact_scaled_pair F source i iw hl hv upper
  cases sign
  · exact congrArg Pair.positive h
  · exact congrArg Pair.negative h

theorem threshold_complete_trace (F : RationalMobius) (source : List Bool)
    (i : Fin (Counter.value source)) (iw : List Bool)
    (hl : iw.length=(PaddedWord.word (PaddedWord.commonConstant F) id source).length)
    (hv : Counter.value iw=i.val) (upper sign : Bool) (pos : Port → ℤ) :
    let n := PaddedWord.word (PaddedWord.commonConstant F) id source
    let x := factor F source iw upper sign
    let p := if upper then (F.componentRow i).upper else (F.componentRow i).lower
    ∃ (t : ℕ) (y : List Bool), t≤budget n x ∧ y.length=n.length ∧
      Counter.value y=(if sign then p.negative else p.positive) ∧
      Trace t (cfg start (initial n x) pos)
        (cfg .done {initial n x with out := Counter.marked y} pos) := by
  dsimp only
  obtain ⟨t,ht,htr⟩ := complete_trace (PaddedWord.word (PaddedWord.commonConstant F) id source)
    (factor F source iw upper sign) pos
  refine ⟨t,output _ _,ht,?_,threshold_component F source i iw hl hv upper sign,htr⟩
  rw [output_length,factor_length F source iw hl upper sign]

end TransposeFollowup.DimensionScale
