import TransposeFollowup.GeneratorRowsPreparedGeometry
import TransposeFollowup.RadiusClockRun
import TransposeFollowup.PortBindingFrame
import TransposeFollowup.PortBindingValues
import TransposeFollowup.NativeIOFusionRun
import TransposeFollowup.NativeTimedWalk
import TransposeFollowup.ExcursionIntervalTransfer
import TransposeFollowup.NativeInputRewindCalls
import TransposeFollowup.NativeIOFusionEmbedding
import TransposeFollowup.NativeIOFusionRecover
import TransposeFollowup.TimedRowWalk
import TransposeFollowup.GeneratorCleanupCost
import TransposeFollowup.SequentialFiveRun
import TransposeFollowup.BitPlaneRun
import TransposeFollowup.SequentialFiveCompletion
import TransposeFollowup.StationaryTapesRun
import TransposeFollowup.CanonicalExcursion
import TransposeFollowup.NativeRunLimits

/-! Ten additional scratch tapes; the retained dimension and existing row
clock are shared with RadiusClock by static injective wiring. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
abbrev Port (q : ℕ):=GeneratorRows.Port q ⊕ Fin 10

def genBinding (q : ℕ) : FinitePortBinding OpcodeGenerator.Port (Port q) where
  ports:=⟨fun p => .inl (.inl p),by intro p t h;exact Sum.inl.inj (Sum.inl.inj h)⟩
  decode | .inl (.inl p) => some p | _ => none
  decode_spec:=by
    intro p t
    change (match p with | .inl (.inl p) => some p | _ => none)=some t ↔
      (Sum.inl (Sum.inl t) : Port q)=p
    rcases p with ((p|p)|p) <;> simp [eq_comm]

def rowBinding (q : ℕ) : FinitePortBinding (RowLoop.Port q) (Port q) where
  ports:=⟨fun p => .inl ((GeneratorRows.rowBinding q).ports p),by
    intro p t h;exact (GeneratorRows.rowBinding q).ports.injective (Sum.inl.inj h)⟩
  decode | .inl p => (GeneratorRows.rowBinding q).decode p | .inr _ => none
  decode_spec:=by
    intro p t
    change (match p with | .inl p => (GeneratorRows.rowBinding q).decode p | .inr _ => none)=some t ↔
      (Sum.inl ((GeneratorRows.rowBinding q).ports t) : Port q)=p
    cases p with
    | inl p => simpa using (GeneratorRows.rowBinding q).decode_spec p t
    | inr p => simp

def auxPort : Fin 10 → RadiusBuilder.Port:=
  ![.bits,.product,.counter,.number,.zero,.result,.one,.fuel,.left,.right]

def setupPort (q : ℕ) : RadiusClock.Port → Port q
  | .inl .source => .inl (.inl (.enumeration .source))
  | .inl .bits => .inr 0 | .inl .product => .inr 1 | .inl .counter => .inr 2
  | .inl .number => .inr 3 | .inl .zero => .inr 4 | .inl .result => .inr 5
  | .inl .one => .inr 6 | .inl .fuel => .inr 7 | .inl .left => .inr 8 | .inl .right => .inr 9
  | .inr _ => .inl (.inr none)

theorem setupPort_injective (q : ℕ) : Function.Injective (setupPort q) := by
  intro a b h
  rcases a with (a|a) <;> rcases b with (b|b)
  · cases a <;> cases b <;> simp_all [setupPort]
  · cases a <;> cases b <;> simp_all [setupPort]
  · cases a;cases b <;> simp_all [setupPort]
  · cases a;cases b;rfl

def setupDecode (q : ℕ) : Port q → Option RadiusClock.Port
  | .inl (.inl p) => if p=(.enumeration .source) then some (.inl .source) else none
  | .inl (.inr none) => some (.inr ())
  | .inl (.inr (some _)) => none
  | .inr p => some (.inl (auxPort p))

theorem setup_decode_spec (q : ℕ) (p : Port q) (t : RadiusClock.Port) :
    setupDecode q p=some t ↔ setupPort q t=p := by
  rcases p with ((p|p)|p)
  · by_cases h : p=(.enumeration .source)
    · subst p
      rcases t with (t|t)
      · cases t <;> simp [setupDecode,setupPort]
      · cases t;simp [setupDecode,setupPort]
    · rcases t with (t|t)
      · cases t <;> simp [setupDecode,setupPort,h,Ne.symm h]
      · cases t;simp [setupDecode,setupPort,h]
  · cases p with
    | none =>
      rcases t with (t|t)
      · cases t <;> simp [setupDecode,setupPort]
      · cases t;simp [setupDecode,setupPort]
    | some p =>
      rcases t with (t|t)
      · cases t <;> simp [setupDecode,setupPort]
      · cases t;simp [setupDecode,setupPort]
  · fin_cases p <;> rcases t with (t|t)
    all_goals cases t <;> simp [setupDecode,setupPort,auxPort]

def setupBinding (q : ℕ) : FinitePortBinding RadiusClock.Port (Port q) where
  ports:=⟨setupPort q,setupPort_injective q⟩
  decode:=setupDecode q
  decode_spec:=setup_decode_spec q

theorem retained_dimension {r : ℕ} (F : Fin (r+1) → RationalMobius) (w xs : List Bool) :
    OpcodeGenerator.finalBank F w xs (.enumeration .source)=Counter.marked xs := by rfl

end TransposeFollowup.PaidGeneratorRows


/-! One native mixed controller: raw generation, paid clock setup, then
the existing fused row consumer. No clock is supplied at entry. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ} {F : Fin (r+1) → RationalMobius}

inductive Label (F : Fin (r+1) → RationalMobius) (K : ℕ)
  | generate (pc : OpcodeGenerator.Label F)
  | setup (pc : RadiusClock.Label K)
  | consume (pc : RowLoop.Label (rationalPageCount F))
  deriving DecidableEq,Fintype

def start (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K:=.generate (OpcodeGenerator.start F)

def program (F : Fin (r+1) → RationalMobius) (K : ℕ) : NativeIO.Program (Port (rationalPageCount F)) (Label F K)
  | .generate pc => if pc=.schedule .done then .work (.jump (.setup (RadiusClock.start K)))
      else NativeIOEmbedding.boundInstruction (genBinding (rationalPageCount F)) Label.generate (OpcodeGenerator.program F pc)
  | .setup .done => .work (.jump (.consume (.rewind .left)))
  | .setup pc => .work ((setupBinding (rationalPageCount F)).instruction Label.setup (RadiusClock.program K pc))
  | .consume pc => .work ((rowBinding (rationalPageCount F)).instruction Label.consume
      (NativeIO.workProgram (RowLoop.program (rationalPageCount F)) pc))

def selected (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K → Bool
  | .consume pc => RowLoop.selected (rationalPageCount F) pc | _ => false

def setupIO (K : ℕ) : NativeIO.Program RadiusClock.Port (RadiusClock.Label K):=
  fun pc => .work (RadiusClock.program K pc)

theorem gen_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : OpcodeGenerator.Label F)
    (hh : OpcodeGenerator.program F pc≠.work .halt) (_ : OpcodeGenerator.program F pc≠.work .reject) :
    program F K (.generate pc)=NativeIOEmbedding.instruction (genBinding (rationalPageCount F)).ports Label.generate
      (OpcodeGenerator.program F pc) := by
  by_cases h : pc=.schedule .done
  · subst pc;exact False.elim (hh rfl)
  · simp only [program,h,ite_false,NativeIOEmbedding.bound_instruction_eq]

theorem setup_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : RadiusClock.Label K)
    (hh : setupIO K pc≠.work .halt) (_ : setupIO K pc≠.work .reject) :
    program F K (.setup pc)=NativeIOEmbedding.instruction (setupBinding (rationalPageCount F)).ports Label.setup
      (setupIO K pc) := by
  cases pc <;> first | exact False.elim (hh rfl) |
    simp only [program,setupIO,NativeIOEmbedding.instruction,FinitePortBinding.instruction_eq]

theorem row_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : RowLoop.Label (rationalPageCount F)) :
    NativeIO.workProgram (program F K) (.consume pc)=
      MicrocodeEmbedding.instruction (rowBinding (rationalPageCount F)).ports Label.consume
        (NativeIO.workProgram (RowLoop.program (rationalPageCount F)) pc) := by
  simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

def frame (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    MicrocodeEmbedding.Frame (Port (rationalPageCount F)) :=
  ⟨Sum.elim (Sum.elim g.work.core.tapes (PageClock.bank clock)) (fun _ => (⟨[],[]⟩ : Tape Bool).denote),
    Sum.elim (Sum.elim g.work.pos cpos) apos⟩

def join {K : ℕ} (pc : Label F K) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIO.Config (Port (rationalPageCount F)) (Label F K) :=
  ⟨⟨⟨pc,(frame g clock cpos apos).tapes⟩,(frame g clock cpos apos).pos⟩,g.inputPos,g.outRev⟩

def rowJoin {K : ℕ} (pc : RowLoop.Label (rationalPageCount F))
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIO.Config (Port (rationalPageCount F)) (Label F K) :=
  let c:=GeneratorRows.rowJoin pc g data clock dpos cpos
  ⟨⟨⟨.consume pc,Sum.elim c.work.core.tapes (fun _ => (⟨[],[]⟩ : Tape Bool).denote)⟩,
    Sum.elim c.work.pos apos⟩,g.inputPos,g.outRev⟩

abbrev Trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool):=
  OperationalTrace.Trace (NativeIOFusion.step (program F K) (selected F K) w)
    (NativeIOFusion.Active (program F K) (selected F K))

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) (K : ℕ):=
  NativeMicrocode.initialEncoding (T:=Port (rationalPageCount F)) (start F K)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) (K : ℕ):=
  NativeIOFusion.machine (nativeEncoding F K) (program F K) (selected F K)

end TransposeFollowup.PaidGeneratorRows


/-! Exact framed interfaces for raw generation and paid clock setup. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ} {F : Fin (r+1) → RationalMobius}

theorem embed_gen (K : ℕ) (g base : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIOEmbedding.embed (genBinding (rationalPageCount F)).ports (Label.generate (K:=K)) g (frame base clock cpos apos)=
      join (.generate g.work.core.pc) g clock cpos apos := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed frame join
  simp only [← (genBinding (rationalPageCount F)).values_eq_extend]
  congr 2
  · congr 1;funext p;rcases p with ((p|p)|p) <;> rfl
  · funext p;rcases p with ((p|p)|p) <;> rfl

theorem embed_setup (K : ℕ) (pc : RadiusClock.Label K) (s : RadiusClock.Bank)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIOEmbedding.embed (setupBinding (rationalPageCount F)).ports Label.setup
      (⟨RadiusClock.cfg pc s (fun p => (frame g clock cpos apos).pos ((setupBinding (rationalPageCount F)).ports p)),
        g.inputPos,g.outRev⟩ : NativeIO.Config RadiusClock.Port (RadiusClock.Label K)) (frame g clock cpos apos)=
      (⟨⟨⟨.setup pc,(setupBinding (rationalPageCount F)).values (fun p => (s p).denote)
          (frame g clock cpos apos).tapes⟩,(frame g clock cpos apos).pos⟩,g.inputPos,g.outRev⟩ :
          NativeIO.Config (Port (rationalPageCount F)) (Label F K)) := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed RadiusClock.cfg
  simp only [← (setupBinding (rationalPageCount F)).values_eq_extend,FinitePortBinding.values_project]

theorem setup_initial (K : ℕ) (xs : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (hg : g.work.core.tapes (.enumeration .source)=(Counter.marked xs).denote)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIOEmbedding.embed (setupBinding (rationalPageCount F)).ports Label.setup
      (⟨RadiusClock.cfg (RadiusClock.start K) (RadiusClock.initial xs)
        (fun p => (frame g ⟨[],[]⟩ cpos apos).pos ((setupBinding (rationalPageCount F)).ports p)),g.inputPos,g.outRev⟩ :
        NativeIO.Config RadiusClock.Port (RadiusClock.Label K)) (frame g ⟨[],[]⟩ cpos apos)=
      join (.setup (RadiusClock.start K)) g ⟨[],[]⟩ cpos apos := by
  rw [embed_setup]
  have hp : (fun p => (RadiusClock.initial xs p).denote)=
      (fun p => (frame g ⟨[],[]⟩ cpos apos).tapes ((setupBinding (rationalPageCount F)).ports p)) := by
    funext p
    rcases p with (p|p)
    · cases p <;> first | exact hg.symm | rfl
    · cases p;rfl
  rw [hp,FinitePortBinding.values_project]
  rfl

theorem setup_final (K : ℕ) (xs : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (hg : g.work.core.tapes (.enumeration .source)=(Counter.marked xs).denote)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    NativeIOEmbedding.embed (setupBinding (rationalPageCount F)).ports Label.setup
      (⟨RadiusClock.cfg .done (RadiusClock.final K xs)
        (fun p => (frame g ⟨[],[]⟩ cpos apos).pos ((setupBinding (rationalPageCount F)).ports p)),g.inputPos,g.outRev⟩ :
        NativeIO.Config RadiusClock.Port (RadiusClock.Label K)) (frame g ⟨[],[]⟩ cpos apos)=
      join (.setup .done) g (Counter.marked (RadiusClock.word K xs)) cpos apos := by
  rw [embed_setup]
  have ht : (setupBinding (rationalPageCount F)).values (fun p => (RadiusClock.final K xs p).denote)
      (frame g ⟨[],[]⟩ cpos apos).tapes=(frame g (Counter.marked (RadiusClock.word K xs)) cpos apos).tapes := by
    funext p
    rcases p with ((p|p)|p)
    · by_cases hp : p=(.enumeration .source)
      · subst p;exact hg.symm
      · simp [setupBinding,setupDecode,FinitePortBinding.values,frame,hp]
    · cases p <;> rfl
    · fin_cases p <;> rfl
  rw [ht]
  rfl

theorem generated_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (gpos : OpcodeGenerator.Port → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (apos : Fin 10 → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length,Trace F K w t
      (join (start F K) (GeneratorRows.first F gpos outRev) ⟨[],[]⟩ cpos apos)
      (join (.generate (.schedule .done)) (GeneratorRows.last F w xs gpos outRev) ⟨[],[]⟩ cpos apos) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=OpcodeGenerator.complete_trace F w n hn hw gpos outRev
  have he:=NativeIOFusionCalls.unselected_trace (genBinding (rationalPageCount F)).ports (Label.generate (K:=K))
    (OpcodeGenerator.program F) (program F K) (selected F K) (frame (GeneratorRows.first F gpos outRev) ⟨[],[]⟩ cpos apos)
    w (fun _ => rfl) (gen_code F K) htr
  exact ⟨xs,hx,hv,hl,t,ht,by simpa only [embed_gen,GeneratorRows.first,GeneratorRows.last,start,
    OpcodeGenerator.cfg,OpcodeGenerator.workCfg] using he⟩

theorem setup_call (F : Fin (r+1) → RationalMobius) (K : ℕ) (xs : List Bool) (hx : 0<Counter.value xs)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (hg : g.work.core.tapes (.enumeration .source)=(Counter.marked xs).denote)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool) :
    ∃ t ≤ RadiusClock.budget K xs,Trace F K w t
      (join (.setup (RadiusClock.start K)) g ⟨[],[]⟩ cpos apos)
      (join (.setup .done) g (Counter.marked (RadiusClock.word K xs)) cpos apos) := by
  obtain ⟨t,ht,htr⟩:=RadiusClock.complete_trace K xs hx
    (fun p => (frame g ⟨[],[]⟩ cpos apos).pos ((setupBinding (rationalPageCount F)).ports p))
  have hi:=NativeIO.lift_work_trace (setupIO K) w g.inputPos g.outRev htr
  have he:=NativeIOFusionCalls.unselected_trace (setupBinding (rationalPageCount F)).ports (Label.setup (F:=F))
    (setupIO K) (program F K) (selected F K) (frame g ⟨[],[]⟩ cpos apos) w (fun _ => rfl) (setup_code F K) hi
  exact ⟨t,ht,by simpa only [setup_initial K xs g hg,setup_final K xs g hg] using he⟩

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc next : Label F K)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (clock : Tape Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool)
    (hcode : program F K pc=.work (.jump next)) (hsel : selected F K pc=false) :
    Trace F K w 1 (join pc g clock cpos apos) (join next g clock cpos apos) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,join,hcode]
  · rw [NativeIOFusion.step_unselected _ _ _ _ hsel]
    simp only [NativeIO.step,join,hcode,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

end TransposeFollowup.PaidGeneratorRows


/-! Reuse the fused row loop, preserving the generated stream and all
additional setup scratch tapes. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ} {F : Fin (r+1) → RationalMobius}

theorem row_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (outerFrame : MicrocodeEmbedding.Frame (Port (rationalPageCount F))) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    {n : ℕ} {c d : NativeIO.Config (RowLoop.Port (rationalPageCount F)) (RowLoop.Label (rationalPageCount F))}
    (h : RowLoop.Trace (rationalPageCount F) w n c d) :
    Trace F K w n
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Label.consume c.work outerFrame,ip,outRev⟩
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Label.consume d.work outerFrame,ip,outRev⟩ :=
  NativeIOFusionCalls.work_trace (rowBinding (rationalPageCount F)).ports Label.consume
    (NativeIO.workProgram (RowLoop.program (rationalPageCount F))) (program F K)
    (RowLoop.selected (rationalPageCount F)) (selected F K) outerFrame w ip outRev (fun _ => rfl)
    (fun pc _ _ => row_code F K pc) (fun _ _ _ _ _ _ => row_code F K _)
    (NativeIOFusion.only_work_trace _ (RowLoop.only_work _) _ w h)

theorem row_values {A : Type*} (q : ℕ) (s : RowLoop.Port q → A)
    (base : GeneratorRows.Port q → A) (aux : Fin 10 → A) :
    (rowBinding q).values s (Sum.elim base aux)=Sum.elim ((GeneratorRows.rowBinding q).values s base) aux := by
  funext p;cases p <;> rfl

theorem embed_row (K : ℕ) (pc : RowLoop.Label (rationalPageCount F))
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (data clock base : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos basePos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    (⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports (Label.consume (K:=K))
      (RowLoop.cfg pc data clock dpos cpos g.inputPos g.outRev).work (frame g base basePos apos),g.inputPos,g.outRev⟩ :
      NativeIO.Config (Port (rationalPageCount F)) (Label F K))=rowJoin pc g data clock dpos cpos apos := by
  have old:=GeneratorRows.embed_row pc g data clock base dpos cpos basePos
  unfold MicrocodeEmbedding.embed RowLoop.cfg frame rowJoin
  simp only [← (rowBinding (rationalPageCount F)).values_eq_extend,row_values]
  congr 2
  · congr 1
    have ht:=congrArg (fun c => c.work.core.tapes) old
    unfold MicrocodeEmbedding.embed RowLoop.cfg GeneratorRows.frame GeneratorClock.frame ReusablePageClock.cfg at ht
    simp only [← (GeneratorRows.rowBinding (rationalPageCount F)).values_eq_extend] at ht
    exact congrArg (fun tapes => Sum.elim tapes (fun _ : Fin 10 => (⟨[],[]⟩ : Tape Bool).denote)) ht
  · have hp:=congrArg (fun c => c.work.pos) old
    unfold MicrocodeEmbedding.embed RowLoop.cfg GeneratorRows.frame GeneratorClock.frame ReusablePageClock.cfg at hp
    simp only [← (GeneratorRows.rowBinding (rationalPageCount F)).values_eq_extend] at hp
    exact congrArg (fun pos => Sum.elim pos apos) hp

theorem rowJoin_eq (K : ℕ) (pc : RowLoop.Label (rationalPageCount F))
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ)
    (ht : g.work.core.tapes VertexScheduler.outputPort=data.denote) (hp : g.work.pos VertexScheduler.outputPort=dpos 0) :
    rowJoin (K:=K) pc g data clock dpos cpos apos=join (.consume pc) g clock cpos apos := by
  unfold rowJoin GeneratorRows.rowJoin join frame
  rw [← ht,← hp,Function.update_eq_self,Function.update_eq_self]

theorem consume_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (n : ℕ) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool)
    (hg : g.work.core.tapes VertexScheduler.outputPort=(⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote) :
    ∃ t ≤ 16*n*rationalPageCount F+4*n*clock.length+12*n+5,Trace F K w t
      (join (.consume (.rewind .left)) g (Counter.marked clock) cpos apos)
      (join (.consume .done) g (Counter.marked clock) (RowLoop.finishPos (GeneratedRowClock.rows F n) clock cpos) apos) := by
  obtain ⟨t,ht,htr⟩:=RowLoop.rewound_stream (GeneratedRowLoop.page_count_positive F (by omega))
    (GeneratedRowClock.rows F n) clock (fun _ => g.work.pos VertexScheduler.outputPort) cpos w g.inputPos g.outRev
  have he:=row_trace F K (frame g (Counter.marked clock) cpos apos) w g.inputPos g.outRev htr
  simp only [embed_row] at he
  have hb : RowLoop.bits (GeneratedRowClock.rows F n)=GeneratedRowClock.bits F n :=
    (GeneratedRowClock.bits_eq_rows F n).symm
  have hl : (GeneratedRowClock.rows F n).length=2*n := by simp [GeneratedRowClock.rows]
  have hc : 2*(RowLoop.bits (GeneratedRowClock.rows F n)).length+
      (GeneratedRowClock.rows F n).length*RowLoop.period (rationalPageCount F) clock+5=
      16*n*rationalPageCount F+4*n*clock.length+12*n+5 := by
    rw [hb,hl,GeneratedRowClock.bits_length]
    unfold RowLoop.period
    ring
  rw [hc] at ht
  rw [hb,rowJoin_eq _ _ g _ _ _ _ _ hg rfl,rowJoin_eq _ _ g _ _ _ _ _ hg rfl] at he
  exact ⟨t,ht,he⟩

end TransposeFollowup.PaidGeneratorRows


/-! The actual fixed native machine starts with blank work tapes, reads
raw input, generates its opcode stream, builds its clock, and consumes all
rows. The bound includes both phase transfers and every setup operation. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

def coefficient (F : Fin (r+1) → RationalMobius) (K : ℕ) : ℕ :=
  OpcodeGenerator.coefficient F+RadiusClock.linearConstant K+28*K+16*rationalPageCount F+19

theorem setup_budget_linear (K n : ℕ) (hn : 1 ≤ n) (xs : List Bool)
    (hv : Counter.value xs=n) (hl : xs.length=n.size) :
    RadiusClock.budget K xs ≤ RadiusClock.linearConstant K*Transpose.inputLength n := by
  have hs : xs.length ≤ Counter.value xs := by rw [hl,hv];exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hb:=RadiusClock.budget_linear K xs (by omega) hs
  rw [hv] at hb
  have hp : n*Transpose.entryBits n ≤ Transpose.inputLength n := by
    exact Nat.mul_le_mul_right _ (show n ≤ n*n by nlinarith)
  exact hb.trans (Nat.mul_le_mul_left _ hp)

theorem complete_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (gpos : OpcodeGenerator.Port → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (apos : Fin 10 → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F K*w.length,Trace F K w t
      (join (start F K) (GeneratorRows.first F gpos outRev) ⟨[],[]⟩ cpos apos)
      (join (.consume .done) (GeneratorRows.last F w xs gpos outRev) (Counter.marked (RadiusClock.word K xs))
        (RowLoop.finishPos (GeneratedRowClock.rows F n) (RadiusClock.word K xs) cpos) apos) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=generated_trace F K w n hn hw gpos cpos apos outRev
  let g:=GeneratorRows.last F w xs gpos outRev
  have j1:=transfer_trace F K (.generate (.schedule .done)) (.setup (RadiusClock.start K)) g ⟨[],[]⟩ cpos apos w rfl rfl
  have hg : g.work.core.tapes (.enumeration .source)=(Counter.marked xs).denote := by rfl
  obtain ⟨b,hb,tb⟩:=setup_call F K xs (by omega) g hg cpos apos w
  have j2:=transfer_trace F K (.setup .done) (.consume (.rewind .left)) g
    (Counter.marked (RadiusClock.word K xs)) cpos apos w rfl rfl
  have hout : g.work.core.tapes VertexScheduler.outputPort=
      (⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote := by
    simpa only [hv] using GeneratorRows.last_output F w xs gpos outRev
  obtain ⟨c,hc,tc⟩:=consume_trace F K g n (RadiusClock.word K xs) cpos apos w hout
  refine ⟨xs,hx,hv,hl,_,?_,trace_trans ta (trace_trans j1 (trace_trans tb (trace_trans j2 tc)))⟩
  have hbP:=setup_budget_linear K n hn xs hv hl
  have hnP:=DimensionCandidate.dimension_le_length n hn
  have hP : 1 ≤ Transpose.inputLength n:=hn.trans hnP
  have hq:=Nat.mul_le_mul_left (rationalPageCount F) hnP
  have hR:=Nat.mul_le_mul_left n (RadiusClock.radius_le K xs (by omega))
  rw [RadiusClock.word_length] at hc
  rw [hv] at hR
  rw [hw] at ha ⊢
  unfold coefficient Transpose.inputLength at *
  nlinarith

theorem initial_blank (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    join (start F K) (GeneratorRows.first F (fun _ => 0) []) ⟨[],[]⟩ (fun _ => 0) (fun _ => 0)=
      (⟨NativeMicrocode.blankConfig (start F K),0,[]⟩ : NativeIO.Config (Port (rationalPageCount F)) (Label F K)) := by
  unfold join frame GeneratorRows.first OpcodeGenerator.cfg OpcodeGenerator.workCfg NativeMicrocode.blankConfig
  rw [RawEnumeration.initial_nil]
  congr 2
  · congr 1
    funext p
    rcases p with ((p|p)|p)
    · rfl
    · cases p <;> rfl
    · rfl
  · funext p;rcases p with ((p|p)|p) <;> rfl

theorem final_halts (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (clock : Tape Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) :
    Transpose.step (nativeMachine F K) w
      (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (join (.consume .done) g clock cpos apos))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,join,program,NativeIO.workProgram,RowLoop.program,FinitePortBinding.instruction]

theorem native_complete (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F K*w.length,
      Transpose.stepN (nativeMachine F K) w t (Transpose.init (nativeMachine F K))=
        some (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
          (join (.consume .done) (GeneratorRows.last F w xs (fun _ => 0) []) (Counter.marked (RadiusClock.word K xs))
            (RowLoop.finishPos (GeneratedRowClock.rows F n) (RadiusClock.word K xs) (fun _ => 0)) (fun _ => 0))) ∧
      Transpose.step (nativeMachine F K) w
        (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
          (join (.consume .done) (GeneratorRows.last F w xs (fun _ => 0) []) (Counter.marked (RadiusClock.word K xs))
            (RowLoop.finishPos (GeneratedRowClock.rows F n) (RadiusClock.word K xs) (fun _ => 0)) (fun _ => 0)))=none := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=complete_trace F K w n hn hw (fun _ => 0) (fun _ => 0) (fun _ => 0) []
  have he:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w htr
  rw [initial_blank,NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)] at he
  exact ⟨xs,hx,hv,hl,t,ht,he,final_halts F K w _ _ _ _⟩

theorem fixed_resources (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    (nativeMachine F K).k=53+rationalPageCount F ∧ (nativeMachine F K).g+1=5 ∧
    (nativeEncoding F K).label (start F K)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Port (rationalPageCount F))=53+rationalPageCount F
  have hg : Fintype.card OpcodeGenerator.Port=42:=by decide +kernel
  simp [Port,GeneratorRows.Port,GeneratorClock.Port,ReusablePageClock.Port,PageClock.Port,hg]
  omega

end TransposeFollowup.PaidGeneratorRows


/-! The source return label is not a successor of a fused read. This permits
its replacement by a continuation without changing any source transition. -/
namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem selected_next_ne_done (pc : Label q) (hs : selected q pc=true) (t : Port q)
    (next : Sym Bool → Label q) (h : NativeIO.workProgram (program q) pc=.read t next) (s : Sym Bool) :
    next s≠.done := by
  cases pc with
  | body pc =>
    have hb : ∀ ops,pc≠.clock ops (.inr .done) := by
      intro ops he
      subst pc
      simp [selected,RowClock.selected,FusedPageClock.selected] at hs
    rw [body_code_except pc hb] at h
    cases hi : NativeIO.workProgram (RowClock.program q) pc with
    | read u f =>
      simp only [hi,MicrocodeEmbedding.instruction,Microcode.Instruction.read.injEq] at h
      rcases h with ⟨_,rfl⟩
      intro he
      cases he
    | _ => simp [hi,MicrocodeEmbedding.instruction] at h
  | _ => simp [selected] at hs

end TransposeFollowup.RowLoop

namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem selected_next_ne_done (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : Label F K)
    (hs : selected F K pc=true) (t : Port (rationalPageCount F))
    (next : Sym Bool → Label F K) (h : NativeIO.workProgram (program F K) pc=.read t next) (s : Sym Bool) :
    next s≠.consume .done := by
  cases pc with
  | consume pc =>
    rw [row_code] at h
    cases hi : NativeIO.workProgram (RowLoop.program (rationalPageCount F)) pc with
    | read u f =>
      simp only [hi,MicrocodeEmbedding.instruction,Microcode.Instruction.read.injEq] at h
      rcases h with ⟨_,rfl⟩
      intro he
      exact RowLoop.selected_next_ne_done pc hs u f hi s (Label.consume.inj he)
    | _ => simp [hi,MicrocodeEmbedding.instruction] at h
  | _ => simp [selected] at hs

end TransposeFollowup.PaidGeneratorRows


/-! The clock setup and both phase transfers are charged before the first
row guard. The generated stream, positions, and external IO are retained. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine Transpose.Tape.TSDiagram
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

theorem rewind_to_guard (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (n : ℕ) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool)
    (hg : g.work.core.tapes VertexScheduler.outputPort=(⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote) :
    ∃ t ≤ 8*n*rationalPageCount F+4,Trace F K w t
      (join (.consume (.rewind .left)) g (Counter.marked clock) cpos apos)
      (rowJoin .guard g ⟨[],symbols (GeneratedRowClock.bits F n)⟩ (Counter.marked clock)
        (fun _ => g.work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length) cpos apos) := by
  obtain ⟨t,ht,ha⟩:=RowLoop.rewind_trace (GeneratedRowClock.bits F n) (Counter.marked clock)
    (fun _ => g.work.pos VertexScheduler.outputPort) cpos w g.inputPos g.outRev
  have hb:=RowLoop.rewind_transfer ⟨[],symbols (GeneratedRowClock.bits F n)⟩ (Counter.marked clock)
    (fun _ => g.work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length) cpos w g.inputPos g.outRev
  have h:=row_trace F K (frame g (Counter.marked clock) cpos apos) w g.inputPos g.outRev (trace_trans ha hb)
  simp only [embed_row] at h
  rw [rowJoin_eq K _ g _ _ _ _ _ hg rfl] at h
  rw [GeneratedRowClock.bits_length] at ht
  exact ⟨t+1,by nlinarith,h⟩

theorem entry_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (gpos : OpcodeGenerator.Port → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (apos : Fin 10 → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      Trace F K w t
        (join (start F K) (GeneratorRows.first F gpos outRev) ⟨[],[]⟩ cpos apos)
        (rowJoin .guard (GeneratorRows.last F w xs gpos outRev) ⟨[],symbols (GeneratedRowClock.bits F n)⟩
          (Counter.marked (SevenPhaseClock.word (K*blockSize 3 n)))
          (fun _ => gpos VertexScheduler.outputPort) cpos apos) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=generated_trace F K w n hn hw gpos cpos apos outRev
  let g:=GeneratorRows.last F w xs gpos outRev
  have j1:=transfer_trace F K (.generate (.schedule .done)) (.setup (RadiusClock.start K)) g ⟨[],[]⟩ cpos apos w rfl rfl
  have hg : g.work.core.tapes (.enumeration .source)=(Counter.marked xs).denote := by rfl
  obtain ⟨b,hb,tb⟩:=setup_call F K xs (by omega) g hg cpos apos w
  have j2:=transfer_trace F K (.setup .done) (.consume (.rewind .left)) g
    (Counter.marked (RadiusClock.word K xs)) cpos apos w rfl rfl
  have hout : g.work.core.tapes VertexScheduler.outputPort=
      (⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote := by
    simpa only [hv] using GeneratorRows.last_output F w xs gpos outRev
  obtain ⟨c,hc,tc⟩:=rewind_to_guard F K g n (RadiusClock.word K xs) cpos apos w hout
  have hp : (fun _ : Fin 1 => g.work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length)=
      (fun _ => gpos VertexScheduler.outputPort) := by
    funext p
    simpa only [hv] using GeneratorRows.output_start_pos F w xs gpos outRev
  rw [hp] at tc
  have htr:=trace_trans ta (trace_trans j1 (trace_trans tb (trace_trans j2 tc)))
  have hclock : RadiusClock.word K xs=SevenPhaseClock.word (K*blockSize 3 n) := by
    simp only [RadiusClock.word,RadiusClock.radius,hv]
  rw [hclock] at htr
  refine ⟨xs,hx,hv,hl,_,?_,htr⟩
  have hbP:=setup_budget_linear K n hn xs hv hl
  rw [hw] at ha ⊢
  nlinarith

end TransposeFollowup.PaidGeneratorRows


namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem row_prefix (F : Fin (r+1) → RationalMobius) (K : ℕ) (outerFrame : MicrocodeEmbedding.Frame (Port (rationalPageCount F)))
    (w : List Bool) (ip : ℤ) (outRev : List Bool) {n : ℕ}
    {c d : NativeIO.Config (RowLoop.Port (rationalPageCount F)) (RowLoop.Label (rationalPageCount F))}
    (h : RowLoop.Trace (rationalPageCount F) w n c d) (s : ℕ) (hs : s ≤ n) :
    NativeIOFusion.run (program F K) (selected F K) w s
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Label.consume c.work outerFrame,ip,outRev⟩=
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Label.consume
        (NativeIOFusion.run (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F)) w s c).work outerFrame,ip,outRev⟩ := by
  have ht:=NativeIOFusion.only_work_trace _ (RowLoop.only_work _) _ w h
  have he:=NativeIOFusionCalls.work_prefix (rowBinding (rationalPageCount F)).ports Label.consume
    (NativeIO.workProgram (RowLoop.program (rationalPageCount F))) (program F K)
    (RowLoop.selected (rationalPageCount F)) (selected F K) outerFrame w ip outRev (fun _ => rfl)
    (fun pc _ _ => row_code F K pc) (fun _ _ _ _ _ _ => row_code F K _) ht s hs
  simpa only [NativeIOFusion.only_work_run _ (RowLoop.only_work _)] using he

theorem stream_prefix (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (front tail : List (OpcodeDecoder.Ops (rationalPageCount F))) (pre : List (Sym Bool)) (clock : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool) :
    Trace F K w (front.length*RowLoop.period (rationalPageCount F) clock)
      (rowJoin .guard g ⟨pre,symbols (RowLoop.bits (front++tail))⟩ (Counter.marked clock) dpos cpos apos)
      (rowJoin .guard g ⟨(symbols (RowLoop.bits front)).reverse++pre,symbols (RowLoop.bits tail)⟩ (Counter.marked clock)
        (NativeZipper.shiftPositions dpos (2*(rationalPageCount F:ℤ)*front.length)) (RowLoop.finishPos front clock cpos) apos) := by
  have h:=row_trace F K (frame g (Counter.marked clock) cpos apos) w g.inputPos g.outRev
    (RowLoop.stream_prefix (GeneratedRowLoop.page_count_positive F (by omega)) front tail pre clock dpos cpos w g.inputPos g.outRev)
  simpa only [embed_row] using h

theorem native_stream_trajectory (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (front tail : List (OpcodeDecoder.Ops (rationalPageCount F))) (ops : OpcodeDecoder.Ops (rationalPageCount F))
    (pre : List (Sym Bool)) (clock : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (apos : Fin 10 → ℤ) (w : List Bool)
    (s : ℕ) (hs : s ≤ RowLoop.period (rationalPageCount F) clock) (p : Fin (rationalPageCount F)) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F K) w)
      (front.length*RowLoop.period (rationalPageCount F) clock+s)
      (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
        (rowJoin .guard g ⟨pre,symbols (RowLoop.bits (front++ops::tail))⟩ (Counter.marked clock) dpos cpos apos))).workPos
          ((nativeEncoding F K).port (.inl (.inr (some p))))=
      RowLoop.finishPos front clock cpos (some p)+(ops p).direction*((clock.take (s-(4*rationalPageCount F+2))).count true) := by
  have hq:=GeneratedRowLoop.page_count_positive F (by omega)
  have ht:=RowLoop.complete_trace hq (front++ops::tail) pre clock dpos cpos w g.inputPos g.outRev
  have hb : front.length*RowLoop.period (rationalPageCount F) clock+s ≤
      (front++ops::tail).length*RowLoop.period (rationalPageCount F) clock+1 := by
    simp only [List.length_append,List.length_cons]
    nlinarith [Nat.zero_le (tail.length*RowLoop.period (rationalPageCount F) clock)]
  have he:=row_prefix F K (frame g (Counter.marked clock) cpos apos) w g.inputPos g.outRev ht
    (front.length*RowLoop.period (rationalPageCount F) clock+s) hb
  simp only [embed_row] at he
  unfold nativeMachine
  rw [NativeIOFusion.run_denote,he]
  simp only [NativeIOFusion.denote,Equiv.symm_apply_apply,MicrocodeEmbedding.embed]
  change Function.extend (rowBinding (rationalPageCount F)).ports _ _
    ((rowBinding (rationalPageCount F)).ports (.inr (some p)))=_
  rw [MicrocodeEmbedding.extend_at]
  have h:=RowLoop.native_stream_trajectory hq front tail ops pre clock dpos cpos w g.inputPos g.outRev s hs p
  unfold RowLoop.nativeMachine at h
  rw [NativeIOFusion.run_denote] at h
  simpa only [NativeIOFusion.denote,Equiv.symm_apply_apply] using h

end TransposeFollowup.PaidGeneratorRows


/-! Row boundaries and every intermediate page position in the same raw-input
run, starting from the original machine's blank initial configuration. -/
namespace TransposeFollowup.PaidGeneratorRows
open FixedTapeCompiler CopyMachine Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {r : ℕ}

theorem native_geometry (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    let clock:=SevenPhaseClock.word (K*blockSize 3 n)
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      (∀ front tail,GeneratedRowClock.rows F n=front++tail →
        Transpose.stepN (nativeMachine F K) w (a+front.length*RowLoop.period (rationalPageCount F) clock)
          (Transpose.init (nativeMachine F K))=
          some (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
            (rowJoin .guard (GeneratorRows.last F w xs (fun _ => 0) [])
              ⟨(symbols (RowLoop.bits front)).reverse,symbols (RowLoop.bits tail)⟩
              (Counter.marked clock) (NativeZipper.shiftPositions (fun _ => 0)
                (2*(rationalPageCount F:ℤ)*front.length)) (RowLoop.finishPos front clock (fun _ => 0)) (fun _ => 0)))) ∧
      (∀ front tail ops,GeneratedRowClock.rows F n=front++ops::tail →
        ∀ s,s ≤ RowLoop.period (rationalPageCount F) clock → ∀ p : Fin (rationalPageCount F),
          (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F K) w)
            (a+(front.length*RowLoop.period (rationalPageCount F) clock+s))
            (Transpose.init (nativeMachine F K))).workPos
              ((nativeEncoding F K).port (.inl (.inr (some p))))=
            RowLoop.finishPos front clock (fun _ => 0) (some p)+
              (ops p).direction*((clock.take (s-(4*rationalPageCount F+2))).count true)) := by
  dsimp only
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=entry_trace F K w n hn hw (fun _ => 0) (fun _ => 0) (fun _ => 0) []
  have hi : NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
      (join (start F K) (GeneratorRows.first F (fun _ => 0) []) ⟨[],[]⟩ (fun _ => 0) (fun _ => 0))=
      Transpose.init (nativeMachine F K) := by
    rw [initial_blank,NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
      (start F K) (NativeMicrocode.initialEncoding_start _)]
    rfl
  refine ⟨xs,hx,hv,hl,a,ha,?_,?_⟩
  · intro front tail he
    have hb : GeneratedRowClock.bits F n=RowLoop.bits (front++tail) := by
      rw [GeneratedRowClock.bits_eq_rows,he]
      rfl
    have tp:=stream_prefix F K (GeneratorRows.last F w xs (fun _ => 0) []) front tail []
      (SevenPhaseClock.word (K*blockSize 3 n)) (fun _ => 0) (fun _ => 0) (fun _ => 0) w
    have ta':=ta
    rw [hb] at ta'
    have h:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w
      (NativeCountedLoop.trace_trans ta' tp)
    rw [hi] at h
    simpa only [nativeMachine,List.append_nil] using h
  · intro front tail ops he s hs p
    have hb : GeneratedRowClock.bits F n=RowLoop.bits (front++ops::tail) := by
      rw [GeneratedRowClock.bits_eq_rows,he]
      rfl
    have hr:=OperationalTrace.trace_run ta
    rw [← hi]
    unfold nativeMachine
    rw [OperationalTrace.run_add,NativeIOFusion.run_denote (nativeEncoding F K) (program F K) (selected F K) w a]
    simp only [NativeIOFusion.run]
    rw [hr,hb]
    simpa only [nativeMachine] using native_stream_trajectory F K (GeneratorRows.last F w xs (fun _ => 0) [])
      front tail ops [] (SevenPhaseClock.word (K*blockSize 3 n)) (fun _ => 0) (fun _ => 0) (fun _ => 0) w s hs p

end TransposeFollowup.PaidGeneratorRows


/-! The paths below are the original native TM paths from blank tapes.
The setup offset and decoder delays are retained in the timed walk. -/
namespace TransposeFollowup.PaidGeneratorRows
open Classical FixedTapeCompiler CopyMachine Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {r : ℕ}

noncomputable def paths (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :
    Fin (nativeMachine F K).k → ℕ → ℤ := fun p t =>
  (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F K) w) t
    (Transpose.init (nativeMachine F K))).workPos p

noncomputable def pagePorts (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    Fin (rationalPageCount F) ↪ Fin (nativeMachine F K).k where
  toFun p:=(nativeEncoding F K).port (.inl (.inr (some p)))
  inj':=by
    intro p q h
    exact Option.some.inj (Sum.inr.inj (Sum.inl.inj ((nativeEncoding F K).port.injective h)))

theorem native_row_walk (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      ∀ p t,a ≤ t → t ≤ a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) →
        paths F K w (pagePorts F K p) t=
          TimedRowWalk.walk (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
            (GeneratorRows.fetchDelay F) a (GeneratedRowClock.rows F n) p t := by
  obtain ⟨xs,_hx,_hv,_hl,a,ha,_boundaries,hpaths⟩:=native_geometry F K w n hn hw
  have hp : RowLoop.period (rationalPageCount F) (SevenPhaseClock.word (K*blockSize 3 n))=
      GeneratorRows.stride F (K*blockSize 3 n) := by
    unfold RowLoop.period GeneratorRows.stride
    rw [SevenPhaseClock.word_length]
    omega
  have hne : GeneratedRowClock.rows F n≠[]:=by simp [GeneratedRowClock.rows];omega
  refine ⟨a,ha,?_⟩
  intro p t hl hu
  apply TimedRowWalk.rowwise_eq (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
    (GeneratorRows.fetchDelay F) a (by unfold GeneratorRows.stride GeneratorRows.fetchDelay;omega)
    (by unfold GeneratorRows.stride;omega) (GeneratedRowClock.rows F n) hne p (paths F K w (pagePorts F K p)) _ t hl
    (by simpa only [GeneratedRowClock.rows,List.length_ofFn] using hu)
  intro front tail ops he s hs
  have h:=hpaths front tail ops he s (by rwa [hp]) p
  rw [hp,TimedRowWalk.finishPos_eq,SevenPhaseClock.count_ramp] at h
  simpa only [paths,show pagePorts F K p=(nativeEncoding F K).port (.inl (.inr (some p))) from rfl,
    GeneratorRows.fetchDelay,zero_add,add_assoc] using h

end TransposeFollowup.PaidGeneratorRows


namespace TransposeFollowup.PaidGeneratorRows
open Classical FixedTapeCompiler Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {c : ℕ}

theorem native_layout (F : Fin (c+1) → RationalMobius) (K : ℕ) (hK : 0<K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      Nonempty (ExcursionLayout (overlapGraph (rationalFamilyMaps F) n) (blockSize 3 n) K (nativeMachine F K).k
        (a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n)) (paths F K w)) := by
  obtain ⟨a,ha,hwalk⟩:=native_row_walk F K w n hn hw
  have hr : 0<blockSize 3 n:=by have := one_le_blockSize (by omega : 1 ≤ 3) hn;omega
  have hs : GeneratorRows.fetchDelay F+7*(K*blockSize 3 n) ≤ GeneratorRows.stride F (K*blockSize 3 n) := by
    unfold GeneratorRows.fetchDelay GeneratorRows.stride
    omega
  let D:=overlapPages (rationalFamilyMaps F) n
  let A:=D.timedLayout (blockSize 3 n) K (GeneratorRows.stride F (K*blockSize 3 n)) a (GeneratorRows.fetchDelay F) hr hK hs
  refine ⟨a,ha,⟨A.transfer_on_excursions (pagePorts F K) (le_refl _) ?_⟩⟩
  intro e t hl hu
  have hlow : a ≤ t := by
    change a+GeneratorRows.stride F (K*blockSize 3 n)*(D.src e).val+GeneratorRows.fetchDelay F+K*blockSize 3 n ≤ t at hl
    omega
  have hhigh : t ≤ a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) :=
    le_of_lt (lt_of_le_of_lt hu (A.close_before_end e))
  rw [hwalk (A.page e) t hlow hhigh]
  exact GeneratorRows.generated_walk_eq F n (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n)) a
    (GeneratorRows.fetchDelay F) (Nat.mul_pos hK hr) (by omega) (A.page e) t

end TransposeFollowup.PaidGeneratorRows


/-! Zero-slack CutIneq for a fully paid native execution from blank tapes.
The expanding-family and fixed head/stretch budgets remain hypotheses.
This is geometry of the prefix, not yet its arbitrary-payload composition. -/
namespace TransposeFollowup.PaidGeneratorRows
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {c : ℕ}

theorem native_cutIneq (F : Fin (c+1) → RationalMobius) (K : ℕ) (hK : 0<K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (eta : ℝ) (heta : 0<eta)
    (hexp : ∀ S : Finset (Fin (2*n)),2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 4 ≤ (4*K-1:ℕ)*eta) (hheads : 4*(rationalPageCount F:ℝ) ≤ 3*(nativeMachine F K).k*eta) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      CutIneq n 3 (blockSize 3 n) (a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n)) 0 0 (paths F K w) := by
  obtain ⟨a,ha,⟨A⟩⟩:=native_layout F K hK w n hn hw
  refine ⟨a,ha,?_⟩
  exact A.cutIneq eta heta (by simpa only [Fintype.card_fin] using hexp) (rationalPageCount F)
    (overlapPages (rationalFamilyMaps F) n).degree_le_pages hstretch hheads
    (by simpa only [Fintype.card_fin] using (show 2 ≤ 2*n by omega)) n 3
    (by simpa only [Fintype.card_fin] using (show n ≤ 2*(2*n) by omega)) (blockSize_mul_ge (by omega : 1 ≤ 3))

theorem native_horizon_linear (F : Fin (c+1) → RationalMobius) (K n a : ℕ) (hn : 1 ≤ n)
    (ha : a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*Transpose.inputLength n+8*n*rationalPageCount F+6) :
    a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) ≤ coefficient F K*Transpose.inputLength n := by
  have hr:=blockSize_le (n:=n) (by omega : 1 ≤ 3)
  have hm:=Nat.mul_le_mul_left (n*K) hr
  have hnP:=DimensionCandidate.dimension_le_length n hn
  have hP : 1 ≤ Transpose.inputLength n:=hn.trans hnP
  have hq:=Nat.mul_le_mul_left (rationalPageCount F) hnP
  unfold GeneratorRows.stride coefficient
  unfold Transpose.inputLength at ha hnP hP hq ⊢
  nlinarith

theorem native_canonical_cut (F : Fin (c+1) → RationalMobius) (K : ℕ) (hK : 0<K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (eta : ℝ) (heta : 0<eta)
    (hexp : ∀ S : Finset (Fin (2*n)),2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 4 ≤ (4*K-1:ℕ)*eta) (hheads : 4*(rationalPageCount F:ℝ) ≤ 3*(nativeMachine F K).k*eta) :
    ∃ T ≤ coefficient F K*w.length,CutIneq n 3 (blockSize 3 n) T 0 0 (paths F K w) := by
  obtain ⟨a,ha,hcut⟩:=native_cutIneq F K hK w n hn hw eta heta hexp hstretch hheads
  refine ⟨a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n),?_,hcut⟩
  rw [hw] at ha ⊢
  exact native_horizon_linear F K n a hn ha

end TransposeFollowup.PaidGeneratorRows


/-! The paid prefix followed by physical input rewind, on the same tapes.
The prefix's sole halting return is replaced by one paid transfer. -/
namespace TransposeFollowup.PaidReady
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}
abbrev Port (F : Fin (r+1) → RationalMobius) := PaidGeneratorRows.Port (rationalPageCount F)
abbrev Label (F : Fin (r+1) → RationalMobius) (K : ℕ) := PaidGeneratorRows.Label F K ⊕ NativeInputRewind.Label

def binding (F : Fin (r+1) → RationalMobius) : FinitePortBinding (Port F) (Port F) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros;simp [eq_comm]

def start (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K:=.inl (PaidGeneratorRows.start F K)

def program (F : Fin (r+1) → RationalMobius) (K : ℕ) : NativeIO.Program (Port F) (Label F K)
  | .inl pc => if pc=.consume .done then .work (.jump (.inr .left))
      else NativeIOEmbedding.boundInstruction (binding F) Sum.inl (PaidGeneratorRows.program F K pc)
  | .inr pc => NativeIOEmbedding.boundInstruction (binding F) Sum.inr (NativeInputRewind.program (Port F) pc)

def selected (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K → Bool
  | .inl pc => PaidGeneratorRows.selected F K pc
  | .inr _ => false

def prefixCfg {F : Fin (r+1) → RationalMobius} {K : ℕ}
    (c : NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)) : NativeIO.Config (Port F) (Label F K) :=
  ⟨⟨⟨.inl c.work.core.pc,c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩

abbrev Trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program F K) (selected F K) w)
    (NativeIOFusion.Active (program F K) (selected F K))
noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) (K : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Port F) (start F K)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) (K : ℕ) :=
  NativeIOFusion.machine (nativeEncoding F K) (program F K) (selected F K)

theorem prefix_code_except (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidGeneratorRows.Label F K)
    (hp : pc≠.consume .done) :
    program F K (.inl pc)=NativeIOEmbedding.instruction (binding F).ports Sum.inl (PaidGeneratorRows.program F K pc) := by
  simp only [program,hp,ite_false,NativeIOEmbedding.bound_instruction_eq]

theorem prefix_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidGeneratorRows.Label F K)
    (hh : PaidGeneratorRows.program F K pc≠.work .halt) (_ : PaidGeneratorRows.program F K pc≠.work .reject) :
    program F K (.inl pc)=NativeIOEmbedding.instruction (binding F).ports Sum.inl (PaidGeneratorRows.program F K pc) := by
  apply prefix_code_except F K pc
  intro he
  subst pc
  exact hh rfl

theorem prefix_read_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidGeneratorRows.Label F K)
    (hs : PaidGeneratorRows.selected F K pc=true) (t : Port F) (next : CopyMachine.Sym Bool → PaidGeneratorRows.Label F K)
    (h : NativeIO.workProgram (PaidGeneratorRows.program F K) pc=.read t next) (s : CopyMachine.Sym Bool) :
    NativeIO.workProgram (program F K) (.inl (next s))=
      MicrocodeEmbedding.instruction (binding F).ports Sum.inl (NativeIO.workProgram (PaidGeneratorRows.program F K) (next s)) :=
  NativeIOFusionEmbedding.work_code (binding F).ports Sum.inl (PaidGeneratorRows.program F K) (program F K) _
    (prefix_code_except F K _ (PaidGeneratorRows.selected_next_ne_done F K pc hs t next h s))

theorem reset_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : NativeInputRewind.Label) :
    program F K (.inr pc)=NativeIOEmbedding.instruction (binding F).ports Sum.inr (NativeInputRewind.program (Port F) pc) := by
  simp only [program,NativeIOEmbedding.bound_instruction_eq]

theorem embed_prefix (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (c : NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)) (frame : MicrocodeEmbedding.Frame (Port F)) :
    NativeIOEmbedding.embed (binding F).ports Sum.inl c frame=prefixCfg c := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed prefixCfg
  simp only [← (binding F).values_eq_extend]
  rfl

theorem prefix_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    {t : ℕ} {c d : NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)}
    (h : PaidGeneratorRows.Trace F K w t c d) : Trace F K w t (prefixCfg c) (prefixCfg d) := by
  have he:=NativeIOFusionEmbedding.trace_embed (binding F).ports Sum.inl (PaidGeneratorRows.program F K) (program F K)
    (PaidGeneratorRows.selected F K) (selected F K) ⟨c.work.core.tapes,c.work.pos⟩ w (fun _ => rfl)
    (prefix_code F K) (prefix_read_code F K) h
  simpa only [embed_prefix] using he

theorem prefix_run (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    {t : ℕ} {c d : NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)}
    (h : PaidGeneratorRows.Trace F K w t c d) (s : ℕ) (hs : s ≤ t) :
    NativeIOFusion.run (program F K) (selected F K) w s (prefixCfg c)=
      prefixCfg (NativeIOFusion.run (PaidGeneratorRows.program F K) (PaidGeneratorRows.selected F K) w s c) := by
  have he:=NativeIOFusionEmbedding.run_prefix (binding F).ports Sum.inl (PaidGeneratorRows.program F K) (program F K)
    (PaidGeneratorRows.selected F K) (selected F K) ⟨c.work.core.tapes,c.work.pos⟩ w (fun _ => rfl)
    (prefix_code F K) (prefix_read_code F K) h s hs
  simpa only [embed_prefix] using he

end TransposeFollowup.PaidReady


/-! One paid native run from blank tapes through the prefix and input reset.
The full prefix workspace is retained exactly; no cleanup or payload
execution is inferred from restoring the input head. -/
namespace TransposeFollowup.PaidReady
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

def sourceFinal (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :=
  PaidGeneratorRows.join (K:=K) (.consume .done) (GeneratorRows.last F w xs (fun _ => 0) [])
    (Counter.marked (RadiusClock.word K xs))
    (RowLoop.finishPos (GeneratedRowClock.rows F n) (RadiusClock.word K xs) (fun _ => 0)) (fun _ => 0)

def finalFrame (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    MicrocodeEmbedding.Frame (Port F) :=
  ⟨(sourceFinal F K w n xs).work.core.tapes,(sourceFinal F K w n xs).work.pos⟩

def finalConfig (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    NativeIO.Config (Port F) (Label F K) :=
  NativeInputRewind.atLabel (.inr .done) (finalFrame F K w n xs) 0 []

def coefficient (F : Fin (r+1) → RationalMobius) (K : ℕ) := PaidGeneratorRows.coefficient F K+6

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (frame : MicrocodeEmbedding.Frame (Port F)) (ip : ℤ) (w outRev : List Bool) :
    Trace F K w 1 (NativeInputRewind.atLabel (.inl (.consume .done)) frame ip outRev)
      (NativeInputRewind.atLabel (.inr .left) frame ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,NativeInputRewind.atLabel,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,NativeInputRewind.atLabel,program,ite_true,NativeMicrocode.step,
      NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

theorem reset_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (frame : MicrocodeEmbedding.Frame (Port F)) (w outRev : List Bool) :
    Trace F K w (2*w.length+3) (NativeInputRewind.atLabel (.inr .left) frame w.length outRev)
      (NativeInputRewind.atLabel (.inr .done) frame 0 outRev) :=
  NativeInputRewind.framed_trace Sum.inr (program F K) (selected F K) frame w outRev
    (fun _ => rfl) (fun pc _ _ => reset_code F K pc)

theorem complete_trace (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ a ≤ PaidGeneratorRows.coefficient F K*w.length,
      PaidGeneratorRows.Trace F K w a
        ⟨NativeMicrocode.blankConfig (PaidGeneratorRows.start F K),0,[]⟩ (sourceFinal F K w n xs) ∧
      Trace F K w (a+2*w.length+4)
        ⟨NativeMicrocode.blankConfig (start F K),0,[]⟩ (finalConfig F K w n xs) := by
  obtain ⟨xs,hx,hv,hl,a,ha,htr⟩:=PaidGeneratorRows.complete_trace F K w n hn hw (fun _ => 0) (fun _ => 0) (fun _ => 0) []
  rw [PaidGeneratorRows.initial_blank] at htr
  have he:=prefix_trace F K w htr
  have hj:=transfer_trace F K (finalFrame F K w n xs) w.length w []
  have hr:=reset_trace F K (finalFrame F K w n xs) w []
  have hstart : prefixCfg (⟨NativeMicrocode.blankConfig (PaidGeneratorRows.start F K),0,[]⟩ :
      NativeIO.Config (Port F) (PaidGeneratorRows.Label F K))=
      (⟨NativeMicrocode.blankConfig (start F K),0,[]⟩ : NativeIO.Config (Port F) (Label F K)) := rfl
  have hend : prefixCfg (sourceFinal F K w n xs)=
      NativeInputRewind.atLabel (.inl (.consume .done)) (finalFrame F K w n xs) w.length [] := rfl
  change Trace F K w a _ (prefixCfg (sourceFinal F K w n xs)) at he
  rw [hstart,hend] at he
  have h:=trace_trans he (trace_trans hj hr)
  refine ⟨xs,hx,hv,hl,a,ha,htr,?_⟩
  convert h using 1 <;> first | omega | rfl

theorem total_linear (F : Fin (r+1) → RationalMobius) (K n a : ℕ) (hn : 1 ≤ n)
    (ha : a ≤ PaidGeneratorRows.coefficient F K*Transpose.inputLength n) :
    a+2*Transpose.inputLength n+4 ≤ coefficient F K*Transpose.inputLength n := by
  have hP:=hn.trans (DimensionCandidate.dimension_le_length n hn)
  unfold coefficient
  nlinarith

theorem final_halts (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    Transpose.step (nativeMachine F K) w
      (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K w n xs))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,finalConfig,NativeInputRewind.atLabel,program,NativeInputRewind.program,
    NativeIOEmbedding.boundInstruction,FinitePortBinding.instruction]

theorem native_complete (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ coefficient F K*w.length,
      Transpose.stepN (nativeMachine F K) w t (Transpose.init (nativeMachine F K))=
        some (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K w n xs)) ∧
      Transpose.step (nativeMachine F K) w
        (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K w n xs))=none := by
  obtain ⟨xs,hx,hv,hl,a,ha,_hprefix,htr⟩:=complete_trace F K w n hn hw
  have he:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w htr
  rw [NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)] at he
  refine ⟨xs,hx,hv,hl,a+2*w.length+4,?_,he,final_halts F K w n xs⟩
  rw [hw] at ha ⊢
  exact total_linear F K n a hn ha

theorem output_contract (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    (finalConfig F K w n xs).inputPos=0 ∧ (finalConfig F K w n xs).outRev=[] ∧
    (finalConfig F K w n xs).work.core.tapes=(sourceFinal F K w n xs).work.core.tapes ∧
    (finalConfig F K w n xs).work.pos=(sourceFinal F K w n xs).work.pos := ⟨rfl,rfl,rfl,rfl⟩

theorem fixed_resources (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    (nativeMachine F K).k=53+rationalPageCount F ∧ (nativeMachine F K).g+1=5 ∧
    (nativeEncoding F K).label (start F K)=0 := by
  exact ⟨(PaidGeneratorRows.fixed_resources F K).1,rfl,NativeMicrocode.initialEncoding_start _⟩

end TransposeFollowup.PaidReady


/-! Exact preservation of the original prefix's native paths at every
successful execution time, then its timed row walk in the reset machine. -/
namespace TransposeFollowup.PaidReady
open Classical FixedTapeCompiler CopyMachine Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {r : ℕ}

noncomputable def paths (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :
    Fin (nativeMachine F K).k → ℕ → ℤ := fun p t =>
  (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F K) w) t (Transpose.init (nativeMachine F K))).workPos p

noncomputable def pagePorts (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    Fin (rationalPageCount F) ↪ Fin (nativeMachine F K).k where
  toFun p:=(nativeEncoding F K).port (.inl (.inr (some p)))
  inj':=by
    intro p q h
    exact Option.some.inj (Sum.inr.inj (Sum.inl.inj ((nativeEncoding F K).port.injective h)))

theorem prefix_positions (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    (t : ℕ) (d : Transpose.Config (PaidGeneratorRows.nativeMachine F K))
    (ht : Transpose.stepN (PaidGeneratorRows.nativeMachine F K) w t
      (Transpose.init (PaidGeneratorRows.nativeMachine F K))=some d)
    (s : ℕ) (hs : s ≤ t) (p : Port F) :
    paths F K w ((nativeEncoding F K).port p) s=
      PaidGeneratorRows.paths F K w ((PaidGeneratorRows.nativeEncoding F K).port p) s := by
  have hi:=NativeIOFusion.blank_denote (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) (PaidGeneratorRows.start F K) (NativeMicrocode.initialEncoding_start _)
  unfold PaidGeneratorRows.nativeMachine at ht
  rw [← hi] at ht
  have htr:=NativeIOFusion.trace_of_stepN (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) w t _ d ht
  have hp:=prefix_run F K w htr s hs
  have hj:=NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)
  unfold paths PaidGeneratorRows.paths
  unfold nativeMachine PaidGeneratorRows.nativeMachine
  rw [← hi,← hj]
  rw [NativeIOFusion.run_denote,NativeIOFusion.run_denote]
  simp only [NativeIOFusion.denote,Equiv.symm_apply_apply]
  change (NativeIOFusion.run (program F K) (selected F K) w s
      (prefixCfg (⟨NativeMicrocode.blankConfig (PaidGeneratorRows.start F K),0,[]⟩ :
        NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)))).work.pos p=_
  rw [hp]
  rfl

theorem native_row_walk (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      ∀ p t,a ≤ t → t ≤ a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) →
        paths F K w (pagePorts F K p) t=
          TimedRowWalk.walk (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
            (GeneratorRows.fetchDelay F) a (GeneratedRowClock.rows F n) p t := by
  obtain ⟨xs,_hx,_hv,_hl,a,ha,boundaries,hpaths⟩:=PaidGeneratorRows.native_geometry F K w n hn hw
  have hp : RowLoop.period (rationalPageCount F) (SevenPhaseClock.word (K*blockSize 3 n))=
      GeneratorRows.stride F (K*blockSize 3 n) := by
    unfold RowLoop.period GeneratorRows.stride
    rw [SevenPhaseClock.word_length]
    omega
  have hend:=boundaries (GeneratedRowClock.rows F n) [] (by simp)
  rw [hp] at hend
  have hlen : (GeneratedRowClock.rows F n).length=2*n := by simp [GeneratedRowClock.rows]
  rw [hlen] at hend
  have hne : GeneratedRowClock.rows F n≠[]:=by simp [GeneratedRowClock.rows];omega
  refine ⟨a,ha,?_⟩
  intro p t hl hu
  rw [show pagePorts F K p=(nativeEncoding F K).port (.inl (.inr (some p))) from rfl,
    prefix_positions F K w _ _ hend t (by nlinarith)]
  apply TimedRowWalk.rowwise_eq (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
    (GeneratorRows.fetchDelay F) a (by unfold GeneratorRows.stride GeneratorRows.fetchDelay;omega)
    (by unfold GeneratorRows.stride;omega) (GeneratedRowClock.rows F n) hne p
    (PaidGeneratorRows.paths F K w ((PaidGeneratorRows.nativeEncoding F K).port (.inl (.inr (some p))))) _ t hl
    (by simpa only [GeneratedRowClock.rows,List.length_ofFn] using hu)
  intro front tail ops he s hs
  have h:=hpaths front tail ops he s (by rwa [hp]) p
  rw [hp,TimedRowWalk.finishPos_eq,SevenPhaseClock.count_ramp] at h
  simpa only [PaidGeneratorRows.paths,GeneratorRows.fetchDelay,zero_add,add_assoc] using h

end TransposeFollowup.PaidReady


/-! The completed generated-row stream has zero net displacement on every
page. This concerns the actual endpoint, with all native row pauses paid. -/
namespace TransposeFollowup.GeneratedRowClock
open Classical FixedTapeCompiler
open scoped BigOperators
set_option autoImplicit false
variable {c : ℕ}

theorem displacement_zero (F : Fin c → RationalMobius) (n R : ℕ) (p : Fin (rationalPageCount F)) :
    TimedRowWalk.displacement R (rows F n) p=0 := by
  unfold TimedRowWalk.displacement rows
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,rationalPageOpcode_eq]
  rw [NestedMatchingPages.opcode_weight_sum]
  simp

theorem finish_positions (F : Fin c → RationalMobius) (n R : ℕ)
    (pos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    RowLoop.finishPos (rows F n) (SevenPhaseClock.word R) pos=pos := by
  funext p
  cases p with
  | none => exact RowLoop.finish_clock _ _ _
  | some p => rw [TimedRowWalk.finishPos_eq,displacement_zero,add_zero]

end TransposeFollowup.GeneratedRowClock

namespace TransposeFollowup.PaidReady
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem final_page_positions (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (xs : List Bool) (p : ReusablePageClock.Port (rationalPageCount F)) :
    (finalConfig F K w n xs).work.pos (.inl (.inr p))=0 := by
  change RowLoop.finishPos (GeneratedRowClock.rows F n) (RadiusClock.word K xs) (fun _ => 0) p=0
  unfold RadiusClock.word
  rw [GeneratedRowClock.finish_positions]

theorem final_page_tapes (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (xs : List Bool) (p : Fin (rationalPageCount F)) :
    (finalConfig F K w n xs).work.core.tapes (.inl (.inr (some p)))=(⟨[],[]⟩ : Tape Bool).denote := rfl

theorem final_scratch (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (w : List Bool) (n : ℕ) (xs : List Bool) (p : Fin 10) :
    (finalConfig F K w n xs).work.core.tapes (.inr p)=(⟨[],[]⟩ : Tape Bool).denote ∧
      (finalConfig F K w n xs).work.pos (.inr p)=0 := ⟨rfl,rfl⟩

end TransposeFollowup.PaidReady


/-! Cleanup of the entire paid-prefix workspace on its existing tapes.
Generator cleanup is followed by a paid handoff to the clock eraser. Page
tapes and radius scratch are blank already and remain untouched. -/
namespace TransposeFollowup.PaidCleanup
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r q : ℕ}
abbrev Port (q : ℕ) := PaidGeneratorRows.Port q
abbrev Label := GeneratorCleanup.Label ⊕ NativeErase.Label

def clockBinding (q : ℕ) : FinitePortBinding (Fin 1) (Port q) where
  ports:=⟨fun _ => .inl (.inr none),fun _ _ _ => Subsingleton.elim _ _⟩
  decode | .inl (.inr none) => some 0 | _ => none
  decode_spec:=by
    intro p t
    fin_cases t
    change (match p with | .inl (.inr none) => some (0 : Fin 1) | _ => none)=some 0 ↔
      (Sum.inl (Sum.inr none) : Port q)=p
    rcases p with ((p|(_|p))|p) <;> simp

def start : Label := .inl GeneratorCleanup.start
def finish : Label := .inr 0

def program (q : ℕ) : Microcode.Program (Port q) Label
  | .inl pc => if pc=.done then .jump (.inr 2) else
      (PaidGeneratorRows.genBinding q).instruction Sum.inl (GeneratorCleanup.program pc)
  | .inr pc => (clockBinding q).instruction Sum.inr (NativeErase.program pc)

def join (pc : Label) (s : GeneratorCleanup.Bank) (pos : GeneratorCleanup.Port → ℤ)
    (clock : Tape Bool) : NativeMicrocode.Config (Port q) Label :=
  ⟨⟨pc,Sum.elim (Sum.elim (fun p => (s p).denote) (PageClock.bank clock))
      (fun _ => (⟨[],[]⟩ : Tape Bool).denote)⟩,
    Sum.elim (Sum.elim pos (fun _ => 0)) (fun _ => 0)⟩

def frame (s : GeneratorCleanup.Bank) (pos : GeneratorCleanup.Port → ℤ) (clock : Tape Bool) :
    MicrocodeEmbedding.Frame (Port q) := ⟨(join finish s pos clock).core.tapes,(join finish s pos clock).pos⟩

def initial (F : Fin (r+1) → RationalMobius) (K : ℕ) (w xs : List Bool) :=
  join (q:=rationalPageCount F) start (OpcodeGenerator.finalBank F w xs)
    (OpcodeGenerator.finalPositions F xs (fun _ => 0)) (Counter.marked (RadiusClock.word K xs))

abbrev Trace (q : ℕ) :=
  OperationalTrace.Trace (NativeMicrocode.step (program q)) (NativeMicrocode.Active (program q))

theorem generator_code (q : ℕ) (pc : GeneratorCleanup.Label)
    (hh : GeneratorCleanup.program pc≠.halt) (_ : GeneratorCleanup.program pc≠.reject) :
    program q (.inl pc)=MicrocodeEmbedding.instruction (PaidGeneratorRows.genBinding q).ports Sum.inl
      (GeneratorCleanup.program pc) := by
  have hp : pc≠.done := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

theorem clock_code (q : ℕ) (pc : NativeErase.Label) :
    program q (.inr pc)=MicrocodeEmbedding.instruction (clockBinding q).ports Sum.inr (NativeErase.program pc) := by
  simp only [program,FinitePortBinding.instruction_eq]

theorem embed_generator (pc : GeneratorCleanup.Label) (s base : GeneratorCleanup.Bank)
    (pos framePos : GeneratorCleanup.Port → ℤ) (clock : Tape Bool) :
    MicrocodeEmbedding.embed (PaidGeneratorRows.genBinding q).ports Sum.inl (GeneratorCleanup.cfg pc s pos)
      (frame base framePos clock)=join (.inl pc) s pos clock := by
  unfold MicrocodeEmbedding.embed GeneratorCleanup.cfg frame join
  simp only [← (PaidGeneratorRows.genBinding q).values_eq_extend]
  congr 2 <;> funext p <;> rcases p with ((p|p)|p) <;> rfl

theorem embed_clock (pc : NativeErase.Label) (clock base : Tape Bool) :
    MicrocodeEmbedding.embed (clockBinding q).ports Sum.inr (NativeErase.cfg pc clock (fun _ => 0)).denote
      (frame (fun _ => ⟨[],[]⟩) (fun _ => 0) base)=
      join (.inr pc) (fun _ => ⟨[],[]⟩) (fun _ => 0) clock := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame join
  simp only [← (clockBinding q).values_eq_extend]
  congr 2 <;> funext p <;> rcases p with ((p|(_|p))|p) <;> rfl

theorem blank_join : join (q:=q) finish (fun _ => ⟨[],[]⟩) (fun _ => 0) ⟨[],[]⟩=
    NativeMicrocode.blankConfig finish := by
  unfold join NativeMicrocode.blankConfig
  congr 2 <;> funext p <;> rcases p with ((p|(_|p))|p) <;> rfl

theorem transfer_trace (clock : Tape Bool) :
    Trace q 1 (join (.inl .done) (fun _ => ⟨[],[]⟩) (fun _ => 0) clock)
      (join (.inr 2) (fun _ => ⟨[],[]⟩) (fun _ => 0) clock) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,join,program]
  · change Trace q 0 (NativeMicrocode.step (program q) _) _
    simp only [NativeMicrocode.step,Microcode.actualStep,join,program,ite_true]
    exact .refl _

theorem complete_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w xs : List Bool) :
    ∃ t ≤ GeneratorCleanup.budget F w xs+4*(RadiusClock.word K xs).length+5,
      Trace (rationalPageCount F) t (initial F K w xs) (NativeMicrocode.blankConfig finish) := by
  let clock:=Counter.marked (RadiusClock.word K xs)
  obtain ⟨a,ha,ta⟩:=GeneratorCleanup.complete_trace F w xs
  have te:=MicrocodeEmbedding.trace_embed (PaidGeneratorRows.genBinding (rationalPageCount F)).ports Sum.inl
    GeneratorCleanup.program (program (rationalPageCount F))
    (frame (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs (fun _ => 0)) clock)
    (generator_code (rationalPageCount F)) ta
  simp only [embed_generator] at te
  have tj:=transfer_trace (q:=rationalPageCount F) clock
  obtain ⟨b,hb,tb⟩:=NativeErase.erase_trace (RadiusClock.word K xs) (fun _ => 0)
  have tf:=MicrocodeEmbedding.trace_embed (clockBinding (rationalPageCount F)).ports Sum.inr NativeErase.program
    (program (rationalPageCount F)) (frame (fun _ => ⟨[],[]⟩) (fun _ => 0) clock)
    (fun pc _ _ => clock_code _ pc) tb
  simp only [embed_clock,show (Sum.inr (0 : NativeErase.Label) : Label)=finish from rfl,blank_join] at tf
  exact ⟨a+1+b,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans te tj) tf⟩

theorem initial_tapes (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    (initial F K w xs).core.tapes=(PaidReady.finalConfig F K w n xs).work.core.tapes := rfl

theorem initial_positions (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    (initial F K w xs).pos=(PaidReady.finalConfig F K w n xs).work.pos := by
  funext p
  rcases p with ((p|p)|p)
  · rfl
  · exact (PaidReady.final_page_positions F K w n xs p).symm
  · rfl

def coefficient (F : Fin (r+1) → RationalMobius) (K : ℕ) := GeneratorCleanup.coefficient F+28*K+5

theorem linear_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size) :
    ∃ t ≤ coefficient F K*w.length,Trace (rationalPageCount F) t
      (initial F K w xs) (NativeMicrocode.blankConfig finish) := by
  obtain ⟨t,ht,htr⟩:=complete_trace F K w xs
  have hg:=GeneratorCleanup.budget_linear F w xs n hn hw hv hl
  have hr:=RadiusClock.radius_le K xs (by omega)
  have hnL:=DimensionCandidate.dimension_le_length n hn
  have hL : 1≤w.length := by omega
  have hne : n*Transpose.entryBits n≤w.length := by
    rw [hw,Transpose.inputLength]
    calc
      n*Transpose.entryBits n=1*(n*Transpose.entryBits n) := by ring
      _≤n*(n*Transpose.entryBits n) := Nat.mul_le_mul_right _ hn
      _=n*n*Transpose.entryBits n := by ring
  have hr' : RadiusClock.radius K xs≤K*w.length := by
    rw [hv] at hr
    exact hr.trans (Nat.mul_le_mul_left K hne)
  rw [RadiusClock.word_length] at ht
  refine ⟨t,?_,htr⟩
  unfold coefficient
  nlinarith

noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) start
noncomputable def nativeMachine (q : ℕ) := NativeMicrocode.machine (nativeEncoding q) (program q)

theorem native_linear (F : Fin (r+1) → RationalMobius) (K : ℕ) (w xs : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) (hv : Counter.value xs=n) (hl : xs.length=n.size)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ coefficient F K*w.length,
      Transpose.stepN (nativeMachine (rationalPageCount F)) input t
        ((initial F K w xs).denote (nativeEncoding _) (program _) ip outRev)=
        some ((NativeMicrocode.blankConfig finish).denote (nativeEncoding _) (program _) ip outRev) ∧
      Transpose.step (nativeMachine (rationalPageCount F)) input
        ((NativeMicrocode.blankConfig finish).denote (nativeEncoding _) (program _) ip outRev)=none := by
  obtain ⟨t,ht,htr⟩:=linear_trace F K w xs n hn hw hv hl
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding _) (program _) input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding _) (program _) input ip outRev _).mpr
  simp [NativeMicrocode.Active,NativeMicrocode.blankConfig,finish,program,FinitePortBinding.instruction,
    NativeErase.program,Microcode.EraseFamily.program,Microcode.EraseFamily.instruction]

theorem fixed_resources (q : ℕ) : (nativeMachine q).k=53+q ∧ (nativeMachine q).g+1=5 ∧
    (nativeMachine q).q+1=100 ∧ (nativeEncoding q).label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card (Port q)=53+q
    have h : Fintype.card OpcodeGenerator.Port=42 := by decide +kernel
    simp [Port,PaidGeneratorRows.Port,GeneratorRows.Port,GeneratorClock.Port,h]
    omega
  · change Fintype.card Label-1+1=100
    decide +kernel

end TransposeFollowup.PaidCleanup


/-! Extend the actual paid prefix by its complete workspace cleanup.
The source's sole halt is replaced by a paid handoff. Selected fused reads
and their successor instructions are preserved exactly. -/
namespace TransposeFollowup.PaidReady
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem selected_next_ne_done (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : Label F K)
    (hs : selected F K pc=true) (t : Port F) (next : Sym Bool → Label F K)
    (h : NativeIO.workProgram (program F K) pc=.read t next) (s : Sym Bool) :
    next s≠.inr .done := by
  cases pc with
  | inr pc => simp [selected] at hs
  | inl pc =>
    have hp : pc≠.consume .done := by
      intro he;subst pc
      simp [selected,PaidGeneratorRows.selected,RowLoop.selected] at hs
    rw [NativeIOFusionEmbedding.work_code (binding F).ports Sum.inl (PaidGeneratorRows.program F K)
      (program F K) pc (prefix_code_except F K pc hp)] at h
    cases hi : NativeIO.workProgram (PaidGeneratorRows.program F K) pc with
    | read u f =>
      simp only [hi,MicrocodeEmbedding.instruction,Microcode.Instruction.read.injEq] at h
      rcases h with ⟨_,rfl⟩
      simp
    | _ => simp [hi,MicrocodeEmbedding.instruction] at h

end TransposeFollowup.PaidReady

namespace TransposeFollowup.PaidClean
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}
abbrev Port (F : Fin (r+1) → RationalMobius) := PaidReady.Port F
abbrev Label (F : Fin (r+1) → RationalMobius) (K : ℕ) := PaidReady.Label F K ⊕ PaidCleanup.Label

def start (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K := .inl (PaidReady.start F K)
def finish (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K := .inr PaidCleanup.finish

def program (F : Fin (r+1) → RationalMobius) (K : ℕ) : NativeIO.Program (Port F) (Label F K)
  | .inl pc => if pc=.inr .done then .work (.jump (.inr PaidCleanup.start)) else
      NativeIOEmbedding.boundInstruction (PaidReady.binding F) Sum.inl (PaidReady.program F K pc)
  | .inr pc => .work ((PaidReady.binding F).instruction Sum.inr (PaidCleanup.program (rationalPageCount F) pc))

def selected (F : Fin (r+1) → RationalMobius) (K : ℕ) : Label F K → Bool
  | .inl pc => PaidReady.selected F K pc
  | .inr _ => false

def prefixCfg {F : Fin (r+1) → RationalMobius} {K : ℕ}
    (c : NativeIO.Config (Port F) (PaidReady.Label F K)) : NativeIO.Config (Port F) (Label F K) :=
  ⟨⟨⟨.inl c.work.core.pc,c.work.core.tapes⟩,c.work.pos⟩,c.inputPos,c.outRev⟩

def cleanupCfg {F : Fin (r+1) → RationalMobius} {K : ℕ}
    (c : NativeMicrocode.Config (Port F) PaidCleanup.Label) (ip : ℤ) (outRev : List Bool) :
    NativeIO.Config (Port F) (Label F K) :=
  ⟨⟨⟨.inr c.core.pc,c.core.tapes⟩,c.pos⟩,ip,outRev⟩

def cleanupIO (q : ℕ) : NativeIO.Program (PaidCleanup.Port q) PaidCleanup.Label :=
  fun pc => .work (PaidCleanup.program q pc)

abbrev Trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program F K) (selected F K) w)
    (NativeIOFusion.Active (program F K) (selected F K))

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) (K : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Port F) (start F K)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) (K : ℕ) :=
  NativeIOFusion.machine (nativeEncoding F K) (program F K) (selected F K)

theorem prefix_code_except (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidReady.Label F K)
    (hp : pc≠.inr .done) :
    program F K (.inl pc)=NativeIOEmbedding.instruction (PaidReady.binding F).ports Sum.inl (PaidReady.program F K pc) := by
  simp only [program,hp,ite_false,NativeIOEmbedding.bound_instruction_eq]

theorem prefix_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidReady.Label F K)
    (hh : PaidReady.program F K pc≠.work .halt) (_ : PaidReady.program F K pc≠.work .reject) :
    program F K (.inl pc)=NativeIOEmbedding.instruction (PaidReady.binding F).ports Sum.inl (PaidReady.program F K pc) := by
  apply prefix_code_except F K pc
  intro h;subst pc;exact hh rfl

theorem prefix_read_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidReady.Label F K)
    (hs : PaidReady.selected F K pc=true) (t : Port F) (next : Sym Bool → PaidReady.Label F K)
    (h : NativeIO.workProgram (PaidReady.program F K) pc=.read t next) (s : Sym Bool) :
    NativeIO.workProgram (program F K) (.inl (next s))=
      MicrocodeEmbedding.instruction (PaidReady.binding F).ports Sum.inl
        (NativeIO.workProgram (PaidReady.program F K) (next s)) :=
  NativeIOFusionEmbedding.work_code (PaidReady.binding F).ports Sum.inl (PaidReady.program F K) (program F K) _
    (prefix_code_except F K _ (PaidReady.selected_next_ne_done F K pc hs t next h s))

theorem cleanup_code (F : Fin (r+1) → RationalMobius) (K : ℕ) (pc : PaidCleanup.Label) :
    program F K (.inr pc)=NativeIOEmbedding.instruction (PaidReady.binding F).ports Sum.inr
      (cleanupIO (rationalPageCount F) pc) := by
  simp only [program,cleanupIO,NativeIOEmbedding.instruction,FinitePortBinding.instruction_eq]

theorem embed_prefix (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (c : NativeIO.Config (Port F) (PaidReady.Label F K)) (frame : MicrocodeEmbedding.Frame (Port F)) :
    NativeIOEmbedding.embed (PaidReady.binding F).ports Sum.inl c frame=prefixCfg (K:=K) c := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed prefixCfg
  simp only [← (PaidReady.binding F).values_eq_extend]
  rfl

theorem embed_cleanup (F : Fin (r+1) → RationalMobius) (K : ℕ)
    (c : NativeMicrocode.Config (Port F) PaidCleanup.Label) (ip : ℤ) (outRev : List Bool)
    (frame : MicrocodeEmbedding.Frame (Port F)) :
    NativeIOEmbedding.embed (PaidReady.binding F).ports Sum.inr (⟨c,ip,outRev⟩ : NativeIO.Config _ _) frame=
      cleanupCfg (K:=K) c ip outRev := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed cleanupCfg
  simp only [← (PaidReady.binding F).values_eq_extend]
  rfl

theorem prefix_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    {t : ℕ} {c d : NativeIO.Config (Port F) (PaidReady.Label F K)}
    (h : PaidReady.Trace F K w t c d) : Trace F K w t (prefixCfg c) (prefixCfg d) := by
  have he:=NativeIOFusionEmbedding.trace_embed (PaidReady.binding F).ports Sum.inl (PaidReady.program F K) (program F K)
    (PaidReady.selected F K) (selected F K) ⟨c.work.core.tapes,c.work.pos⟩ w (fun _ => rfl)
    (prefix_code F K) (prefix_read_code F K) h
  simpa only [embed_prefix] using he

theorem prefix_run (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    {t : ℕ} {c d : NativeIO.Config (Port F) (PaidReady.Label F K)}
    (h : PaidReady.Trace F K w t c d) (s : ℕ) (hs : s≤t) :
    NativeIOFusion.run (program F K) (selected F K) w s (prefixCfg c)=
      prefixCfg (NativeIOFusion.run (PaidReady.program F K) (PaidReady.selected F K) w s c) := by
  have he:=NativeIOFusionEmbedding.run_prefix (PaidReady.binding F).ports Sum.inl (PaidReady.program F K) (program F K)
    (PaidReady.selected F K) (selected F K) ⟨c.work.core.tapes,c.work.pos⟩ w (fun _ => rfl)
    (prefix_code F K) (prefix_read_code F K) h s hs
  simpa only [embed_prefix] using he

theorem cleanup_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    {t : ℕ} {c d : NativeMicrocode.Config (Port F) PaidCleanup.Label}
    (h : PaidCleanup.Trace (rationalPageCount F) t c d) :
    Trace F K w t (cleanupCfg c ip outRev) (cleanupCfg d ip outRev) := by
  have hi:=NativeIO.lift_work_trace (cleanupIO (rationalPageCount F)) w ip outRev h
  have he:=NativeIOFusionCalls.unselected_trace (PaidReady.binding F).ports Sum.inr (cleanupIO (rationalPageCount F))
    (program F K) (selected F K) ⟨c.core.tapes,c.pos⟩ w (fun _ => rfl) (fun pc _ _ => cleanup_code F K pc) hi
  simpa only [embed_cleanup] using he

end TransposeFollowup.PaidClean


/-! The actual blank-start paid prefix now returns with every work tape
blank, every work head at zero, the input head reset and no output. All
cleanup and both stages' handoffs are charged in the linear time bound. -/
namespace TransposeFollowup.PaidClean
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {r : ℕ}

def finalConfig (F : Fin (r+1) → RationalMobius) (K : ℕ) : NativeIO.Config (Port F) (Label F K) :=
  ⟨NativeMicrocode.blankConfig (finish F K),0,[]⟩

def coefficient (F : Fin (r+1) → RationalMobius) (K : ℕ) :=
  PaidReady.coefficient F K+PaidCleanup.coefficient F K+1

theorem cleanup_entry (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    cleanupCfg (K:=K) (PaidCleanup.initial F K w xs) 0 []=
      NativeInputRewind.atLabel (.inr PaidCleanup.start) (PaidReady.finalFrame F K w n xs) 0 [] := by
  change (⟨⟨⟨.inr PaidCleanup.start,(PaidCleanup.initial F K w xs).core.tapes⟩,
    (PaidCleanup.initial F K w xs).pos⟩,0,[]⟩ : NativeIO.Config (Port F) (Label F K))=_
  rw [PaidCleanup.initial_tapes F K w n xs,PaidCleanup.initial_positions F K w n xs]
  rfl

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ) (xs : List Bool) :
    Trace F K w 1 (prefixCfg (PaidReady.finalConfig F K w n xs))
      (cleanupCfg (PaidCleanup.initial F K w xs) 0 []) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,prefixCfg,PaidReady.finalConfig,NativeInputRewind.atLabel,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    have he : NativeIO.step (program F K) w (prefixCfg (PaidReady.finalConfig F K w n xs))=
        cleanupCfg (PaidCleanup.initial F K w xs) 0 [] := by
      rw [cleanup_entry F K w n xs]
      rfl
    rw [he]
    exact .refl _

theorem complete_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ a ≤ PaidReady.coefficient F K*w.length,
      PaidReady.Trace F K w a ⟨NativeMicrocode.blankConfig (PaidReady.start F K),0,[]⟩
        (PaidReady.finalConfig F K w n xs) ∧
    ∃ b ≤ PaidCleanup.coefficient F K*w.length,
      Trace F K w (a+1+b) ⟨NativeMicrocode.blankConfig (start F K),0,[]⟩ (finalConfig F K) := by
  obtain ⟨xs,hx,hv,hl,a,ha,_hg,ta⟩:=PaidReady.complete_trace F K w n hn hw
  have hap : a+2*w.length+4≤PaidReady.coefficient F K*w.length := by
    rw [hw] at ha ⊢
    exact PaidReady.total_linear F K n a hn ha
  obtain ⟨b,hb,tb⟩:=PaidCleanup.linear_trace F K w xs n hn hw hv hl
  have te:=prefix_trace F K w ta
  have tj:=transfer_trace F K w n xs
  have tf:=cleanup_trace F K w 0 [] tb
  exact ⟨xs,hx,hv,hl,a+2*w.length+4,hap,ta,b,hb,trace_trans (trace_trans te tj) tf⟩

theorem total_linear (F : Fin (r+1) → RationalMobius) (K : ℕ) (P a b : ℕ) (hP : 1≤P)
    (ha : a≤PaidReady.coefficient F K*P) (hb : b≤PaidCleanup.coefficient F K*P) :
    a+1+b≤coefficient F K*P := by
  unfold coefficient
  nlinarith

theorem linear_trace (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ t ≤ coefficient F K*w.length,
      Trace F K w t ⟨NativeMicrocode.blankConfig (start F K),0,[]⟩ (finalConfig F K) := by
  obtain ⟨xs,_hx,_hv,_hl,a,ha,_ta,b,hb,htr⟩:=complete_trace F K w n hn hw
  have hP : 1≤w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  exact ⟨a+1+b,total_linear F K w.length a b hP ha hb,htr⟩

theorem final_halts (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :
    Transpose.step (nativeMachine F K) w
      (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,finalConfig,NativeMicrocode.blankConfig,finish,program,PaidCleanup.finish,
    PaidCleanup.program,FinitePortBinding.instruction,NativeErase.program,
    Microcode.EraseFamily.program,Microcode.EraseFamily.instruction]

theorem native_complete (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) (n : ℕ)
    (hn : 1≤n) (hw : w.length=Transpose.inputLength n) :
    ∃ t ≤ coefficient F K*w.length,
      Transpose.stepN (nativeMachine F K) w t (Transpose.init (nativeMachine F K))=
        some (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K)) ∧
      Transpose.step (nativeMachine F K) w
        (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K))=none := by
  obtain ⟨t,ht,htr⟩:=linear_trace F K w n hn hw
  have he:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w htr
  rw [NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)] at he
  exact ⟨t,ht,he,final_halts F K w⟩

theorem reset_contract (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    (finalConfig F K).inputPos=0 ∧ (finalConfig F K).outRev=[] ∧
    (∀ p,(finalConfig F K).work.core.tapes p=(⟨[],[]⟩ : Tape Bool).denote) ∧
    (∀ p,(finalConfig F K).work.pos p=0) := ⟨rfl,rfl,fun _ => rfl,fun _ => rfl⟩

theorem native_reset_contract (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    let c:=NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K) (finalConfig F K)
    c.inPos=0 ∧ c.outRev=[] ∧ (∀ p z,c.work p z=0) ∧ (∀ p,c.workPos p=0) := by
  refine ⟨rfl,rfl,?_,fun _ => rfl⟩
  intro p z
  change NativeMicrocode.symbolCode (AbsoluteTape.cells AbsoluteTape.blank 0 z)=0
  rw [AbsoluteTape.blank_cells]
  rfl

theorem fixed_resources (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    (nativeMachine F K).k=53+rationalPageCount F ∧ (nativeMachine F K).g+1=5 ∧
    (nativeMachine F K).q+1=((PaidReady.nativeMachine F K).q+1)+100 ∧
      (nativeEncoding F K).label (start F K)=0 := by
  refine ⟨(PaidReady.fixed_resources F K).1,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label F K)-1+1=(Fintype.card (PaidReady.Label F K)-1+1)+100
  have h : Fintype.card PaidCleanup.Label=100 := by decide +kernel
  have hp : 0<Fintype.card (PaidReady.Label F K) := Fintype.card_pos_iff.mpr ⟨PaidReady.start F K⟩
  have hsum : Fintype.card (Label F K)=Fintype.card (PaidReady.Label F K)+Fintype.card PaidCleanup.Label :=
    Fintype.card_sum
  rw [hsum,h]
  omega

end TransposeFollowup.PaidClean


/-! The cleaned prefix preserves the original paid generator's absolute
trajectories at every successful prefix time. Cleanup changes subsequent
motion only; none of the earlier excursion witnesses is lost. -/
namespace TransposeFollowup.PaidClean
open Classical FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

noncomputable def paths (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool) :
    Fin (nativeMachine F K).k → ℕ → ℤ := fun p t =>
  (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F K) w) t (Transpose.init (nativeMachine F K))).workPos p

noncomputable def pagePorts (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    Fin (rationalPageCount F) ↪ Fin (nativeMachine F K).k where
  toFun p:=(nativeEncoding F K).port (.inl (.inr (some p)))
  inj':=by
    intro p q h
    exact Option.some.inj (Sum.inr.inj (Sum.inl.inj ((nativeEncoding F K).port.injective h)))

theorem prefix_stepN (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    (t : ℕ) (d : Transpose.Config (PaidGeneratorRows.nativeMachine F K))
    (ht : Transpose.stepN (PaidGeneratorRows.nativeMachine F K) w t
      (Transpose.init (PaidGeneratorRows.nativeMachine F K))=some d) :
    ∃ e,Transpose.stepN (nativeMachine F K) w t (Transpose.init (nativeMachine F K))=some e := by
  have hi:=NativeIOFusion.blank_denote (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) (PaidGeneratorRows.start F K) (NativeMicrocode.initialEncoding_start _)
  unfold PaidGeneratorRows.nativeMachine at ht
  rw [← hi] at ht
  have htr:=NativeIOFusion.trace_of_stepN (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) w t _ d ht
  have he:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w
    (prefix_trace F K w (PaidReady.prefix_trace F K w htr))
  change Transpose.stepN (nativeMachine F K) w t
    (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
      ⟨NativeMicrocode.blankConfig (start F K),0,[]⟩)=some _ at he
  rw [NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)] at he
  exact ⟨_,he⟩

theorem prefix_positions (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    (t : ℕ) (d : Transpose.Config (PaidGeneratorRows.nativeMachine F K))
    (ht : Transpose.stepN (PaidGeneratorRows.nativeMachine F K) w t
      (Transpose.init (PaidGeneratorRows.nativeMachine F K))=some d)
    (s : ℕ) (hs : s≤t) (p : Port F) :
    paths F K w ((nativeEncoding F K).port p) s=
      PaidGeneratorRows.paths F K w ((PaidGeneratorRows.nativeEncoding F K).port p) s := by
  have hi:=NativeIOFusion.blank_denote (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) (PaidGeneratorRows.start F K) (NativeMicrocode.initialEncoding_start _)
  unfold PaidGeneratorRows.nativeMachine at ht
  rw [← hi] at ht
  have htr:=NativeIOFusion.trace_of_stepN (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) w t _ d ht
  have hp:=prefix_run F K w (PaidReady.prefix_trace F K w htr) s hs
  have hr:=PaidReady.prefix_run F K w htr s hs
  have hj:=NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)
  unfold paths PaidGeneratorRows.paths
  unfold nativeMachine PaidGeneratorRows.nativeMachine
  rw [← hi,← hj]
  rw [NativeIOFusion.run_denote,NativeIOFusion.run_denote]
  simp only [NativeIOFusion.denote,Equiv.symm_apply_apply]
  change (NativeIOFusion.run (program F K) (selected F K) w s
      (prefixCfg (PaidReady.prefixCfg (⟨NativeMicrocode.blankConfig (PaidGeneratorRows.start F K),0,[]⟩ :
        NativeIO.Config (Port F) (PaidGeneratorRows.Label F K))))).work.pos p=_
  rw [hp]
  change (NativeIOFusion.run (PaidReady.program F K) (PaidReady.selected F K) w s
      (PaidReady.prefixCfg (⟨NativeMicrocode.blankConfig (PaidGeneratorRows.start F K),0,[]⟩ :
        NativeIO.Config (Port F) (PaidGeneratorRows.Label F K)))).work.pos p=_
  rw [hr]
  rfl

end TransposeFollowup.PaidClean


/-! The fully paid prefix followed by an arbitrary original-model payload.
Prefix storage is erased and reset before the payload starts; both tape banks are blank.
The handoff is one native transition, and payload steps are unchanged. -/
namespace TransposeFollowup.PaidPayload
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

noncomputable def prefixProgram (F : Fin (r+1) → RationalMobius) (K : ℕ) : SequentialFive.Program where
  k:=(PaidClean.nativeMachine F K).k
  q:=(PaidClean.nativeMachine F K).q
  delta:=(PaidClean.nativeMachine F K).δ

def payloadProgram (M : Transpose.TM) : SequentialFive.Program where
  k:=(BitPlaneMachine.machine M).k
  q:=(BitPlaneMachine.machine M).q
  delta:=(BitPlaneMachine.machine M).δ

theorem prefix_tm (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    (prefixProgram F K).tm=PaidClean.nativeMachine F K := rfl

theorem payload_tm (M : Transpose.TM) : (payloadProgram M).tm=BitPlaneMachine.machine M := rfl

noncomputable def machine (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) : Transpose.TM :=
  SequentialFive.machine (prefixProgram F K) (payloadProgram M)

def coefficient (F : Fin (r+1) → RationalMobius) (K : ℕ) : ℕ := PaidClean.coefficient F K+1

theorem prefix_blank_frame (F : Fin (r+1) → RationalMobius) (K : ℕ) :
    SequentialFive.frameOf (prefixProgram F K)
      (NativeIOFusion.denote (PaidClean.nativeEncoding F K) (PaidClean.program F K) (PaidClean.selected F K)
        (PaidClean.finalConfig F K))=SequentialFive.blankFrame (prefixProgram F K) := by
  unfold SequentialFive.frameOf SequentialFive.blankFrame
  congr 1
  funext p z
  exact (PaidClean.native_reset_contract F K).2.2.1 p z

/-- The cleared prefix bank stays blank, with stationary zero heads,
through every successful payload segment. Both the cleanup and handoff
precede this exact simulation. -/
theorem execute_with_blank_prefix (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM)
    (w : List Bool) (n : ℕ) (hn : 1≤n) (hw : w.length=Transpose.inputLength n)
    (b : ℕ) (cb : Transpose.Config (BitPlaneMachine.machine M))
    (hb : Transpose.stepN (BitPlaneMachine.machine M) w b (Transpose.init (BitPlaneMachine.machine M))=some cb) :
    ∃ a ≤ PaidClean.coefficient F K*w.length,
      Transpose.stepN (machine F K M) w (a+1+b) (Transpose.init (machine F K M))=
        some (SequentialFive.embedRight (prefixProgram F K) (payloadProgram M)
          (SequentialFive.blankFrame (prefixProgram F K)) cb) := by
  obtain ⟨a,ha,he,hh⟩:=PaidClean.native_complete F K w n hn hw
  have h:=SequentialFive.execute (prefixProgram F K) (payloadProgram M) w a b _ cb he hh rfl rfl hb
  rw [prefix_blank_frame] at h
  exact ⟨a,ha,h⟩

theorem preserves_computation (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM)
    (w out : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (t : ℕ) (h : Transpose.ComputesWithin M w out t) :
    Transpose.ComputesWithin (machine F K M) w out (coefficient F K*w.length+t) := by
  obtain ⟨a,ha,he,hh⟩:=PaidClean.native_complete F K w n hn hw
  have hc:=SequentialFive.computesWithin (prefixProgram F K) (payloadProgram M) w out a t _
    he hh rfl rfl (BitPlaneMachine.computesWithin M w out t h)
  obtain ⟨s,hs,c,hstep,hhalt,hout⟩:=hc
  refine ⟨s,?_,c,hstep,hhalt,hout⟩
  have hP : 1 ≤ w.length := by rw [hw];exact hn.trans (DimensionCandidate.dimension_le_length n hn)
  unfold coefficient
  nlinarith

theorem preserves_transposesWithin (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM)
    (T : ℕ → ℕ) (h : Transpose.TransposesWithin M T) :
    Transpose.TransposesWithin (machine F K M) (fun P => coefficient F K*P+T P) := by
  intro n hn A
  have hw : (Transpose.encode n (Transpose.entryBits n) A).length=Transpose.inputLength n := by
    rw [Transpose.Tape.Impl.length_encode]
    rfl
  have ht:=preserves_computation F K M _ _ n hn hw _ (h n hn A)
  simpa only [hw] using ht

theorem fixed_resources (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) :
    (machine F K M).k=53+rationalPageCount F+M.k*max 1 M.g.size ∧ (machine F K M).g+1=5 := by
  have h:=(PaidClean.fixed_resources F K).1
  change (PaidClean.nativeMachine F K).k+M.k*max 1 M.g.size=53+rationalPageCount F+M.k*max 1 M.g.size ∧ 5=5
  rw [h]
  exact ⟨rfl,rfl⟩

end TransposeFollowup.PaidPayload


namespace TransposeFollowup.PaidReady
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

theorem prefix_stepN (F : Fin (r+1) → RationalMobius) (K : ℕ) (w : List Bool)
    (t : ℕ) (d : Transpose.Config (PaidGeneratorRows.nativeMachine F K))
    (ht : Transpose.stepN (PaidGeneratorRows.nativeMachine F K) w t
      (Transpose.init (PaidGeneratorRows.nativeMachine F K))=some d) :
    ∃ e,Transpose.stepN (nativeMachine F K) w t (Transpose.init (nativeMachine F K))=some e := by
  have hi:=NativeIOFusion.blank_denote (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) (PaidGeneratorRows.start F K) (NativeMicrocode.initialEncoding_start _)
  unfold PaidGeneratorRows.nativeMachine at ht
  rw [← hi] at ht
  have htr:=NativeIOFusion.trace_of_stepN (PaidGeneratorRows.nativeEncoding F K) (PaidGeneratorRows.program F K)
    (PaidGeneratorRows.selected F K) w t _ d ht
  have he:=NativeIOFusion.trace_stepN (nativeEncoding F K) (program F K) (selected F K) w (prefix_trace F K w htr)
  change Transpose.stepN (nativeMachine F K) w t
    (NativeIOFusion.denote (nativeEncoding F K) (program F K) (selected F K)
      ⟨NativeMicrocode.blankConfig (start F K),0,[]⟩)=some _ at he
  rw [NativeIOFusion.blank_denote (nativeEncoding F K) (program F K) (selected F K)
    (start F K) (NativeMicrocode.initialEncoding_start _)] at he
  exact ⟨_,he⟩

end TransposeFollowup.PaidReady

namespace TransposeFollowup.PaidPayload
open Classical FixedTapeCompiler CopyMachine Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {r : ℕ}

noncomputable def paths (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (w : List Bool) :
    Fin (machine F K M).k → ℕ → ℤ := fun p t => (Transpose.Tape.run (machine F K M) w t).workPos p

noncomputable def leftPorts (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) :
    Fin (PaidClean.nativeMachine F K).k ↪ Fin (machine F K M).k where
  toFun p:=SequentialFive.ports (prefixProgram F K) (payloadProgram M) (.inl p)
  inj':=by intro p q h;exact Sum.inl.inj ((SequentialFive.ports _ _).injective h)

noncomputable def pagePorts (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) :
    Fin (rationalPageCount F) ↪ Fin (machine F K M).k where
  toFun p:=leftPorts F K M (PaidClean.pagePorts F K p)
  inj':=by intro p q h;exact (PaidClean.pagePorts F K).injective ((leftPorts F K M).injective h)

theorem operational_run (M : Transpose.TM) (w : List Bool) (t : ℕ) :
    OperationalTrace.run (Transpose.Tape.Impl.next M w) t (Transpose.init M)=Transpose.Tape.run M w t := by
  rw [Transpose.Tape.Impl.run_eq_iterate,NativeMicrocode.operationalRun_eq_iterate]

theorem prefix_positions (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (w : List Bool)
    (T : ℕ) (d : Transpose.Config (PaidClean.nativeMachine F K))
    (ht : Transpose.stepN (PaidClean.nativeMachine F K) w T (Transpose.init (PaidClean.nativeMachine F K))=some d)
    (t : ℕ) (htT : t ≤ T) (p : Fin (PaidClean.nativeMachine F K).k) :
    paths F K M w (leftPorts F K M p) t=PaidClean.paths F K w p t := by
  have h:=SequentialFive.prefix_run (prefixProgram F K) (payloadProgram M) w T t d ht htT
  unfold paths machine
  rw [h]
  change Sum.elim (Transpose.Tape.run (prefixProgram F K).tm w t).workPos (fun _ => 0)
    ((SequentialFive.ports (prefixProgram F K) (payloadProgram M)).symm
      (SequentialFive.ports (prefixProgram F K) (payloadProgram M) (.inl p)))=_
  rw [Equiv.symm_apply_apply]
  change (Transpose.Tape.run (PaidClean.nativeMachine F K) w t).workPos p=PaidClean.paths F K w p t
  rw [PaidClean.paths,operational_run]

theorem original_prefix_positions (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (w : List Bool)
    (T : ℕ) (d : Transpose.Config (PaidGeneratorRows.nativeMachine F K))
    (ht : Transpose.stepN (PaidGeneratorRows.nativeMachine F K) w T (Transpose.init (PaidGeneratorRows.nativeMachine F K))=some d)
    (t : ℕ) (htT : t ≤ T) (p : PaidClean.Port F) :
    paths F K M w (leftPorts F K M ((PaidClean.nativeEncoding F K).port p)) t=
      PaidGeneratorRows.paths F K w ((PaidGeneratorRows.nativeEncoding F K).port p) t := by
  obtain ⟨e,he⟩:=PaidClean.prefix_stepN F K w T d ht
  exact (prefix_positions F K M w T e he t htT ((PaidClean.nativeEncoding F K).port p)).trans
    (PaidClean.prefix_positions F K w T d ht t htT p)

theorem native_row_walk (F : Fin (r+1) → RationalMobius) (K : ℕ) (M : Transpose.TM)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      (∃ d,Transpose.stepN (PaidClean.nativeMachine F K) w (a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n))
        (Transpose.init (PaidClean.nativeMachine F K))=some d) ∧
      ∀ p t,a ≤ t → t ≤ a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) →
        paths F K M w (pagePorts F K M p) t=
          TimedRowWalk.walk (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
            (GeneratorRows.fetchDelay F) a (GeneratedRowClock.rows F n) p t := by
  obtain ⟨xs,_hx,_hv,_hl,a,ha,boundaries,hpaths⟩:=PaidGeneratorRows.native_geometry F K w n hn hw
  have hp : RowLoop.period (rationalPageCount F) (SevenPhaseClock.word (K*blockSize 3 n))=
      GeneratorRows.stride F (K*blockSize 3 n) := by
    unfold RowLoop.period GeneratorRows.stride
    rw [SevenPhaseClock.word_length]
    omega
  have hend:=boundaries (GeneratedRowClock.rows F n) [] (by simp)
  rw [hp] at hend
  have hlen : (GeneratedRowClock.rows F n).length=2*n := by simp [GeneratedRowClock.rows]
  rw [hlen,Nat.mul_comm (2*n) (GeneratorRows.stride F (K*blockSize 3 n))] at hend
  have hne : GeneratedRowClock.rows F n≠[]:=by simp [GeneratedRowClock.rows];omega
  refine ⟨a,ha,PaidClean.prefix_stepN F K w _ _ hend,?_⟩
  intro p t hl hu
  change paths F K M w (leftPorts F K M ((PaidClean.nativeEncoding F K).port (.inl (.inr (some p))))) t=_
  refine (original_prefix_positions F K M w _ _ hend t hu (.inl (.inr (some p)))).trans ?_
  apply TimedRowWalk.rowwise_eq (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n))
    (GeneratorRows.fetchDelay F) a (by unfold GeneratorRows.stride GeneratorRows.fetchDelay;omega)
    (by unfold GeneratorRows.stride;omega) (GeneratedRowClock.rows F n) hne p
    (PaidGeneratorRows.paths F K w ((PaidGeneratorRows.nativeEncoding F K).port (.inl (.inr (some p))))) _ t hl
    (by simpa only [GeneratedRowClock.rows,List.length_ofFn] using hu)
  intro front tail ops he s hs
  have h:=hpaths front tail ops he s (by rwa [hp]) p
  rw [hp,TimedRowWalk.finishPos_eq,SevenPhaseClock.count_ramp] at h
  simpa only [PaidGeneratorRows.paths,GeneratorRows.fetchDelay,zero_add,add_assoc] using h

end TransposeFollowup.PaidPayload


/-! The composed machine retains the prefix excursion layout. Its horizon
can extend through arbitrary later computation, with the actual head count. -/
namespace TransposeFollowup.PaidPayload
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {c : ℕ}

theorem native_layout (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (hK : 0<K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) :
    ∃ a ≤ (OpcodeGenerator.coefficient F+RadiusClock.linearConstant K)*w.length+8*n*rationalPageCount F+6,
      (∃ d,Transpose.stepN (PaidClean.nativeMachine F K) w (a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n))
        (Transpose.init (PaidClean.nativeMachine F K))=some d) ∧
      Nonempty (ExcursionLayout (overlapGraph (rationalFamilyMaps F) n) (blockSize 3 n) K (machine F K M).k
        (a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n)) (paths F K M w)) := by
  obtain ⟨a,ha,hrun,hwalk⟩:=native_row_walk F K M w n hn hw
  have hr : 0<blockSize 3 n:=by have := one_le_blockSize (by omega : 1 ≤ 3) hn;omega
  have hs : GeneratorRows.fetchDelay F+7*(K*blockSize 3 n) ≤ GeneratorRows.stride F (K*blockSize 3 n) := by
    unfold GeneratorRows.fetchDelay GeneratorRows.stride
    omega
  let D:=overlapPages (rationalFamilyMaps F) n
  let A:=D.timedLayout (blockSize 3 n) K (GeneratorRows.stride F (K*blockSize 3 n)) a (GeneratorRows.fetchDelay F) hr hK hs
  refine ⟨a,ha,hrun,⟨A.transfer_on_excursions (pagePorts F K M) (le_refl _) ?_⟩⟩
  intro e t hl hu
  have hlow : a ≤ t := by
    change a+GeneratorRows.stride F (K*blockSize 3 n)*(D.src e).val+GeneratorRows.fetchDelay F+K*blockSize 3 n ≤ t at hl
    omega
  have hhigh : t ≤ a+GeneratorRows.stride F (K*blockSize 3 n)*(2*n) :=
    le_of_lt (lt_of_le_of_lt hu (A.close_before_end e))
  rw [hwalk (A.page e) t hlow hhigh]
  exact GeneratorRows.generated_walk_eq F n (K*blockSize 3 n) (GeneratorRows.stride F (K*blockSize 3 n)) a
    (GeneratorRows.fetchDelay F) (Nat.mul_pos hK hr) (by omega) (A.page e) t

theorem cut_after_prefix (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (hK : 0<K)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (eta : ℝ) (heta : 0<eta)
    (hexp : ∀ S : Finset (Fin (2*n)),2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 4 ≤ (4*K-1:ℕ)*eta) (hheads : 4*(rationalPageCount F:ℝ) ≤ 3*(machine F K M).k*eta)
    (a : ℕ) (ca : Transpose.Config (PaidClean.nativeMachine F K))
    (ha : Transpose.stepN (PaidClean.nativeMachine F K) w a (Transpose.init (PaidClean.nativeMachine F K))=some ca)
    (hh : Transpose.step (PaidClean.nativeMachine F K) w ca=none) (T : ℕ) (hT : a ≤ T) :
    CutIneq n 3 (blockSize 3 n) T 0 0 (paths F K M w) := by
  obtain ⟨s,_hs,⟨d,hd⟩,⟨D⟩⟩:=native_layout F K M hK w n hn hw
  have hsa:=SequentialFive.successful_time_le_halting (PaidClean.nativeMachine F K) w a _ ca d ha hh hd
  let E:=D.transfer_on_excursions (Function.Embedding.refl _) (hsa.trans hT) (by intros;rfl)
  exact E.cutIneq eta heta (by simpa only [Fintype.card_fin] using hexp) (rationalPageCount F)
    (overlapPages (rationalFamilyMaps F) n).degree_le_pages hstretch hheads
    (by simpa only [Fintype.card_fin] using (show 2 ≤ 2*n by omega)) n 3
    (by simpa only [Fintype.card_fin] using (show n ≤ 2*(2*n) by omega)) (blockSize_mul_ge (by omega : 1 ≤ 3))

end TransposeFollowup.PaidPayload


/-! Computation and the cut inequality at the same actual halting time.
The expansion and geometric parameter hypotheses remain explicit. -/
namespace TransposeFollowup.PaidPayload
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {c : ℕ}

theorem preserves_computation_with_cut (F : Fin (c+1) → RationalMobius) (K : ℕ)
    (M : Transpose.TM) (hK : 0<K) (w out : List Bool) (n : ℕ)
    (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) (eta : ℝ) (heta : 0<eta)
    (hexp : ∀ S : Finset (Fin (2*n)),2*S.card ≤ 2*n →
      eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card)
    (hstretch : 4 ≤ (4*K-1:ℕ)*eta)
    (hheads : 4*(rationalPageCount F:ℝ) ≤ 3*(machine F K M).k*eta)
    (t : ℕ) (h : Transpose.ComputesWithin M w out t) :
    ∃ T ≤ coefficient F K*w.length+t, ∃ d : Transpose.Config (machine F K M),
      Transpose.stepN (machine F K M) w T (Transpose.init (machine F K M))=some d ∧
      Transpose.step (machine F K M) w d=none ∧ d.outRev.reverse=out ∧
      CutIneq n 3 (blockSize 3 n) T 0 0 (paths F K M w) := by
  obtain ⟨a,_ha,he,hh⟩:=PaidClean.native_complete F K w n hn hw
  obtain ⟨T,hT,d,hd,hhalt,hout⟩:=preserves_computation F K M w out n hn hw t h
  have hp:=SequentialFive.stepN_left (prefixProgram F K) (payloadProgram M) w a
    (Transpose.init (prefixProgram F K).tm) _ (SequentialFive.blankFrame (payloadProgram M)) he
  rw [SequentialFive.initial_embed] at hp
  have haT:=SequentialFive.successful_time_le_halting (machine F K M) w T a d _ hd hhalt hp
  exact ⟨T,hT,d,hd,hhalt,hout,
    cut_after_prefix F K M hK w n hn hw eta heta hexp hstretch hheads a _ he hh T haT⟩

end TransposeFollowup.PaidPayload


/-! Fixed numerical parameters for the native padding construction. The
expanding rational map family remains an explicit mathematical input. -/
namespace TransposeFollowup.PaidPadding
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
set_option autoImplicit false
variable {c : ℕ}

noncomputable abbrev machine (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (extra : ℕ) :=
  PaidPayload.machine F K (StationaryTapes.machine M extra)

noncomputable abbrev paths (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM)
    (extra : ℕ) (w : List Bool) :=
  PaidPayload.paths F K (StationaryTapes.machine M extra) w

theorem fixed_resources (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (extra : ℕ) :
    (machine F K M extra).k=53+rationalPageCount F+(M.k+extra)*max 1 M.g.size ∧
      (machine F K M extra).g+1=5 :=
  PaidPayload.fixed_resources F K (StationaryTapes.machine M extra)

theorem extra_le_heads (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (extra : ℕ) :
    extra ≤ (machine F K M extra).k := by
  rw [(fixed_resources F K M extra).1]
  have h : 1 ≤ max 1 M.g.size:=Nat.le_max_left _ _
  nlinarith

theorem exists_parameters (F : Fin (c+1) → RationalMobius)
    (eta : ℝ) (heta : 0<eta) :
    ∃ K extra : ℕ,0<K ∧ 4 ≤ (4*K-1:ℕ)*eta ∧
      ∀ M : Transpose.TM, 4*(rationalPageCount F:ℝ) ≤ 3*(machine F K M extra).k*eta := by
  obtain ⟨K,extra,hK,hs,he⟩:=exists_padding_parameters eta heta (rationalPageCount F) 0
  simp only [Nat.zero_add] at he
  refine ⟨K,extra,hK,hs,?_⟩
  intro M
  have hk : (extra:ℝ) ≤ (machine F K M extra).k:=by exact_mod_cast extra_le_heads F K M extra
  have hm:=mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 3*eta)
  nlinarith

theorem preserves_computation (F : Fin (c+1) → RationalMobius) (K : ℕ)
    (M : Transpose.TM) (extra : ℕ) (w out : List Bool) (n : ℕ)
    (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n) (t : ℕ)
    (h : Transpose.ComputesWithin M w out t) :
    Transpose.ComputesWithin (machine F K M extra) w out (PaidPayload.coefficient F K*w.length+t) :=
  PaidPayload.preserves_computation F K (StationaryTapes.machine M extra) w out n hn hw t
    (StationaryTapes.computesWithin M extra w out t h)

theorem preserves_transposesWithin (F : Fin (c+1) → RationalMobius) (K : ℕ)
    (M : Transpose.TM) (extra : ℕ) (T : ℕ → ℕ) (h : Transpose.TransposesWithin M T) :
    Transpose.TransposesWithin (machine F K M extra) (fun P => PaidPayload.coefficient F K*P+T P) :=
  PaidPayload.preserves_transposesWithin F K (StationaryTapes.machine M extra) T
    (StationaryTapes.transposesWithin M extra T h)

/-- K and the extra tape count are selected before the payload machine, dimension, input,
output, expansion check and time bound. Only expansion remains a premise. -/
theorem uniform_computation_with_cut (F : Fin (c+1) → RationalMobius)
    (eta : ℝ) (heta : 0<eta) :
    ∃ K extra : ℕ,∀ (M : Transpose.TM) (n : ℕ),1 ≤ n → ∀ (w out : List Bool),w.length=Transpose.inputLength n →
      (∀ S : Finset (Fin (2*n)),2*S.card ≤ 2*n →
        eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) n) S).card) →
      ∀ (t : ℕ),Transpose.ComputesWithin M w out t →
      ∃ T ≤ PaidPayload.coefficient F K*w.length+t,∃ d : Transpose.Config (machine F K M extra),
        Transpose.stepN (machine F K M extra) w T (Transpose.init (machine F K M extra))=some d ∧
        Transpose.step (machine F K M extra) w d=none ∧ d.outRev.reverse=out ∧
        CutIneq n 3 (blockSize 3 n) T 0 0 (paths F K M extra w) := by
  obtain ⟨K,extra,hK,hs,hh⟩:=exists_parameters F eta heta
  refine ⟨K,extra,?_⟩
  intro M n hn w out hw hexp t ht
  exact PaidPayload.preserves_computation_with_cut F K (StationaryTapes.machine M extra) hK
    w out n hn hw eta heta hexp hs (hh M) t (StationaryTapes.computesWithin M extra w out t ht)

end TransposeFollowup.PaidPadding


/-! Fixed native machines preserving arbitrary linear-time tasks and
satisfying M* on their actual runs, conditional only on map expansion. -/
namespace TransposeFollowup.PaidPadding
open Classical FixedTapeCompiler Transpose.Tape Transpose.Tape.Impl Transpose.Tape.TSDiagram
open Filter Topology
set_option autoImplicit false
variable {c : ℕ}

theorem cellBits_eq (F : Fin (c+1) → RationalMobius) (K : ℕ) (M : Transpose.TM) (extra : ℕ) :
    cellBits (machine F K M extra)=3 := by
  unfold cellBits
  rw [(fixed_resources F K M extra).2]
  decide +kernel

/-- The machine parameters precede every choice of task instances and
linear time coefficient. Every horizon is an actual halting time with the
demanded output, and every limit assertion concerns this same machine. -/
theorem uniform_linear_tasks_macrostar (F : Fin (c+1) → RationalMobius) (M : Transpose.TM)
    (eta : ℝ) (heta : 0<eta) :
    ∃ K extra : ℕ,∀ (ns : ℕ → ℕ),Tendsto ns atTop atTop → (∀ i,1 ≤ ns i) →
      ∀ (ws outs : ℕ → List Bool),(∀ i,(ws i).length=Transpose.inputLength (ns i)) →
      ∀ (a : ℕ),(∀ i,Transpose.ComputesWithin M (ws i) (outs i) (a*Transpose.inputLength (ns i))) →
      (∀ i (S : Finset (Fin (2*ns i))),2*S.card ≤ 2*ns i →
        eta*S.card ≤ (outsideNeighbors (overlapGraph (rationalFamilyMaps F) (ns i)) S).card) →
      ∃ Ts : ℕ → ℕ,
        (∀ i,Ts i ≤ (PaidPayload.coefficient F K+a)*Transpose.inputLength (ns i) ∧
          ∃ d : Transpose.Config (machine F K M extra),
            Transpose.stepN (machine F K M extra) (ws i) (Ts i) (Transpose.init (machine F K M extra))=some d ∧
            Transpose.step (machine F K M extra) (ws i) d=none ∧ d.outRev.reverse=outs i ∧
            CutIneq (ns i) 3 (blockSize 3 (ns i)) (Ts i) 0 0 (paths F K M extra (ws i))) ∧
        NativeRunLimits.Conclusion (machine F K M extra) ns ws Ts (PaidPayload.coefficient F K+a) := by
  obtain ⟨K,extra,hcompile⟩:=uniform_computation_with_cut F eta heta
  refine ⟨K,extra,?_⟩
  intro ns hns hn ws outs hw a hc he
  have hr:=fun i => hcompile M (ns i) (hn i) (ws i) (outs i) (hw i) (he i)
    (a*Transpose.inputLength (ns i)) (hc i)
  choose Ts ht ds hs hh ho hcut using hr
  have htime : ∀ i,Ts i ≤ (PaidPayload.coefficient F K+a)*Transpose.inputLength (ns i) := by
    intro i
    simpa only [hw i,Nat.add_mul] using ht i
  refine ⟨Ts,fun i => ⟨htime i,ds i,hs i,hh i,ho i,hcut i⟩,?_⟩
  apply NativeRunLimits.of_cut _ ns hns ws Ts _ htime
  intro i
  rw [cellBits_eq]
  exact hcut i

end TransposeFollowup.PaidPadding
