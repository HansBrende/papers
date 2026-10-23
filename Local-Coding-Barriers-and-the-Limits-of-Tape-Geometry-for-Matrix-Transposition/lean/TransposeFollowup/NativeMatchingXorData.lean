import TransposeFollowup.NativeMatchingXorPayload
import TransposeFollowup.NativeMatchingXorPages
import TransposeFollowup.NativeMatchingXorOutput
import TransposeFollowup.NativeMatchingXorPrefixRewind
import TransposeFollowup.NativeIOEmbedding

/-! The complete prepared-data executor for a fixed family of matching pages.
Copy and positioning, every page/reset, target rewind, and raw output are paid
native calls. Prepared tag tapes and source data are preserved. -/
namespace TransposeFollowup.NativeMatchingXorData
open FixedTapeCompiler CopyMachine
open NativeMatchingXorPages (Port ValidTags output)
set_option autoImplicit false

def payloadBinding {q : ℕ} (pivot : Fin q) : FinitePortBinding (Fin 3) (Port q) where
  ports := ⟨![.source,.target,.tagA pivot],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  decode := fun p => match p with
    | .source => some 0 | .target => some 1
    | .tagA i => if i=pivot then some 2 else none | .tagB _ => none
  decode_spec := by
    intro p t
    change _ ↔ (![Port.source,Port.target,Port.tagA pivot] : Fin 3 → Port q) t=p
    cases p <;> fin_cases t <;> simp [eq_comm]

def allBinding (q : ℕ) : FinitePortBinding (Port q) (Port q) where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p t; simp [eq_comm]

def targetBinding (q : ℕ) : FinitePortBinding (Fin 1) (Port q) where
  ports := ⟨fun _ => .target,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => match p with | .target => some 0 | _ => none
  decode_spec := by intro p t; cases p <;> fin_cases t <;> simp; rfl

inductive Label (q : ℕ)
  | payload (pc : NativeMatchingXorPayload.Label)
  | pages (pc : NativeMatchingXorPages.Label q)
  | back (pc : NativeSealBack.Label)
  | emit (pc : NativeMatchingXorOutput.Label)
  deriving DecidableEq, Fintype

def start (q : ℕ) : Label q := .payload NativeMatchingXorPayload.start

def program {q : ℕ} (pivot : Fin q) : NativeIO.Program (Port q) (Label q)
  | .payload pc => if pc=.rewind .done then .work (.jump (.pages (NativeMatchingXorPages.start q)))
      else .work ((payloadBinding pivot).instruction Label.payload (NativeMatchingXorPayload.program pc))
  | .pages pc => if pc=.next (Fin.last q) then .work (.jump (.back .back))
      else .work ((allBinding q).instruction Label.pages (NativeMatchingXorPages.program q pc))
  | .back pc => if pc=.done then .work (.jump (.emit .read))
      else .work ((targetBinding q).instruction Label.back (NativeSealBack.program pc))
  | .emit pc => NativeIOEmbedding.boundInstruction (targetBinding q) Label.emit
      (NativeMatchingXorOutput.program pc)

def workCfg {q : ℕ} (pc : Label q) (source target : Tape Bool) (a b : Fin q → List Bool)
    (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) (Label q) :=
  ⟨⟨pc,fun p => (NativeMatchingXorPages.bank source target a b p).denote⟩,pos⟩

def cfg {q : ℕ} (pc : Label q) (source target : Tape Bool) (a b : Fin q → List Bool)
    (pos : Port q → ℤ) (ip : ℤ) (outRev : List Bool) : NativeIO.Config (Port q) (Label q) :=
  ⟨workCfg pc source target a b pos,ip,outRev⟩

def positioned {q : ℕ} (pos : Port q → ℤ) (n : ℕ) : Port q → ℤ :=
  Function.update pos .target (pos .target+n)

theorem payload_code {q : ℕ} (pivot : Fin q) (pc : NativeMatchingXorPayload.Label)
    (hh : NativeMatchingXorPayload.program pc≠.halt)
    (_ : NativeMatchingXorPayload.program pc≠.reject) :
    NativeIO.workProgram (program pivot) (.payload pc)=
      MicrocodeEmbedding.instruction (payloadBinding pivot).ports Label.payload
        (NativeMatchingXorPayload.program pc) := by
  have h : pc≠.rewind .done := by intro h; subst pc; exact hh rfl
  simp [NativeIO.workProgram,program,h,FinitePortBinding.instruction_eq]

theorem pages_code {q : ℕ} (pivot : Fin q) (pc : NativeMatchingXorPages.Label q)
    (hh : NativeMatchingXorPages.program q pc≠.halt)
    (_ : NativeMatchingXorPages.program q pc≠.reject) :
    NativeIO.workProgram (program pivot) (.pages pc)=
      MicrocodeEmbedding.instruction (allBinding q).ports Label.pages
        (NativeMatchingXorPages.program q pc) := by
  have h : pc≠.next (Fin.last q) := by
    intro h; subst pc; apply hh; simp [NativeMatchingXorPages.program]
  simp [NativeIO.workProgram,program,h,FinitePortBinding.instruction_eq]

theorem back_code {q : ℕ} (pivot : Fin q) (pc : NativeSealBack.Label)
    (hh : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    NativeIO.workProgram (program pivot) (.back pc)=
      MicrocodeEmbedding.instruction (targetBinding q).ports Label.back (NativeSealBack.program pc) := by
  have h : pc≠.done := by intro h; subst pc; exact hh rfl
  simp [NativeIO.workProgram,program,h,FinitePortBinding.instruction_eq]

theorem embed_payload {q : ℕ} (pivot : Fin q) (pc : NativeMatchingXorPayload.Label)
    (source target baseTarget : Tape Bool) (a b : Fin q → List Bool) (pos : Port q → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (payloadBinding pivot).ports Label.payload
      (NativeMatchingXorPayload.cfg pc source target (Counter.marked (a pivot))
        (Function.update (fun t => pos ((payloadBinding pivot).ports t)) 1 z)).denote
      (NativeMatchingXorPages.frame source baseTarget a b pos)=
      workCfg (.payload pc) source target a b (Function.update pos .target z) := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorPayload.cfg NativeZipper.Config.denote
    Microcode.Config.denote workCfg NativeMatchingXorPages.frame
  simp only [← (payloadBinding pivot).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;>
    simp [FinitePortBinding.values,payloadBinding,NativeMatchingXorPages.bank] <;>
    first | rfl | (split_ifs <;> subst_vars <;> rfl)

theorem embed_pages {q : ℕ} (pc : NativeMatchingXorPages.Label q)
    (source target baseTarget : Tape Bool) (a b : Fin q → List Bool) (pos basePos : Port q → ℤ) :
    MicrocodeEmbedding.embed (allBinding q).ports Label.pages
      (NativeMatchingXorPages.cfg pc source target a b pos)
      (NativeMatchingXorPages.frame source baseTarget a b basePos)=
      workCfg (.pages pc) source target a b pos := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorPages.cfg workCfg NativeMatchingXorPages.frame
  simp only [← (allBinding q).values_eq_extend]
  rfl

theorem embed_back {q : ℕ} (pc : NativeSealBack.Label) (source target baseTarget : Tape Bool)
    (a b : Fin q → List Bool) (pos : Port q → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (targetBinding q).ports Label.back
      (NativeSealBack.cfg pc target (fun _ => z)).denote
      (NativeMatchingXorPages.frame source baseTarget a b pos)=
      workCfg (.back pc) source target a b (Function.update pos .target z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus workCfg NativeMatchingXorPages.frame
  simp only [← (targetBinding q).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_emit {q : ℕ} (pc : NativeMatchingXorOutput.Label)
    (source target baseTarget : Tape Bool) (a b : Fin q → List Bool)
    (pos : Port q → ℤ) (z ip : ℤ) (outRev : List Bool) :
    NativeIOEmbedding.embed (targetBinding q).ports Label.emit
      (NativeMatchingXorOutput.cfg pc target (fun _ => z) ip outRev).denote
      (NativeMatchingXorPages.frame source baseTarget a b pos)=
      cfg (.emit pc) source target a b (Function.update pos .target z) ip outRev := by
  unfold NativeIOEmbedding.embed NativeMatchingXorOutput.cfg NativeIOZipper.Config.denote
    MicrocodeEmbedding.embed NativeZipper.Config.denote Microcode.Config.denote
    cfg workCfg NativeMatchingXorPages.frame
  simp only [← (targetBinding q).values_eq_extend]
  congr 1
  congr 2 <;> funext p <;> cases p <;> rfl

abbrev Trace {q : ℕ} (pivot : Fin q) (input : List Bool) :=
  OperationalTrace.Trace (NativeIO.step (program pivot) input) (NativeIO.Active (program pivot))

theorem jump_trace {q : ℕ} (pivot : Fin q) (pc next : Label q)
    (h : program pivot pc=.work (.jump next)) (source target : Tape Bool)
    (a b : Fin q → List Bool) (pos : Port q → ℤ) (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace pivot input 1 (cfg pc source target a b pos ip outRev)
      (cfg next source target a b pos ip outRev) := by
  apply NativeIO.lift_work_trace
  exact NativeMicrocode.jump_trace _ _ _ (by simp [NativeIO.workProgram,workCfg,h])



theorem payload_call {q : ℕ} (pivot : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hvalid : ValidTags A.length a b) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*(A.length+B.length)+4*A.length+20, Trace pivot input t
      (cfg (start q) (Counter.marked (A++B)) ⟨[],[]⟩ a b pos ip outRev)
      (cfg (.payload (.rewind .done)) (Counter.marked (A++B))
        (NativeMatchingXorPrefixRewind.splitWord A B) a b (positioned pos A.length) ip outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorPayload.payload_trace A B (a pivot) (hvalid pivot).1
    (fun t => pos ((payloadBinding pivot).ports t))
  have he := MicrocodeEmbedding.trace_embed (payloadBinding pivot).ports Label.payload
    NativeMatchingXorPayload.program (NativeIO.workProgram (program pivot))
    (NativeMatchingXorPages.frame (Counter.marked (A++B)) ⟨[],[]⟩ a b pos)
    (payload_code pivot) htr
  have hi := embed_payload pivot NativeMatchingXorPayload.start (Counter.marked (A++B))
    ⟨[],[]⟩ ⟨[],[]⟩ a b pos (pos .target)
  have hp : (fun t => pos ((payloadBinding pivot).ports t)) 1=pos .target := rfl
  rw [← hp,Function.update_eq_self] at hi
  simp only [hp,Function.update_eq_self] at hi
  rw [hi] at he
  refine ⟨t,by simpa only [(hvalid pivot).1] using ht,?_⟩
  simpa only [NativeMatchingXorPayload.finalPositions,hp,embed_payload,
    NativeMatchingXorPrefixRewind.splitWord,positioned,start,cfg] using
    NativeIO.lift_work_trace (program pivot) input ip outRev he

theorem pages_call {q : ℕ} (pivot : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ q*(8*A.length+8), Trace pivot input t
      (cfg (.pages (NativeMatchingXorPages.start q)) (Counter.marked (A++B))
        (NativeMatchingXorPrefixRewind.splitWord A B) a b pos ip outRev)
      (cfg (.pages (.next (Fin.last q))) (Counter.marked (A++B))
        (NativeMatchingXorPrefixRewind.splitWord A (output A B a b q)) a b pos ip outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorPages.complete_trace A B a b hB hvalid
    [.start] (symbols B++[.stop]) ((symbols A).reverse++[.start]) [.stop] pos
  have he := MicrocodeEmbedding.trace_embed (allBinding q).ports Label.pages
    (NativeMatchingXorPages.program q) (NativeIO.workProgram (program pivot))
    (NativeMatchingXorPages.frame (Counter.marked (A++B)) ⟨[],[]⟩ a b pos)
    (pages_code pivot) htr
  refine ⟨t,ht,?_⟩
  simpa only [Counter.marked,symbols,List.map_append,List.append_assoc,
    NativeMatchingXorPrefixRewind.splitWord,embed_pages,cfg] using
    NativeIO.lift_work_trace (program pivot) input ip outRev he

theorem back_call {q : ℕ} (pivot : Fin q) (source : Tape Bool) (A B : List Bool)
    (a b : Fin q → List Bool) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*A.length+4, Trace pivot input t
      (cfg (.back .back) source (NativeMatchingXorPrefixRewind.splitWord A B) a b
        (positioned pos A.length) ip outRev)
      (cfg (.back .done) source (Counter.marked (A++B)) a b pos ip outRev) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorPrefixRewind.rewind_trace A B (fun _ => pos .target+A.length)
  have he := MicrocodeEmbedding.trace_embed (targetBinding q).ports Label.back NativeSealBack.program
    (NativeIO.workProgram (program pivot))
    (NativeMatchingXorPages.frame source ⟨[],[]⟩ a b pos) (back_code pivot) htr
  refine ⟨t,ht,?_⟩
  simpa only [embed_back,add_sub_cancel_right,Function.update_eq_self,positioned,cfg] using
    NativeIO.lift_work_trace (program pivot) input ip outRev he

theorem emit_call {q : ℕ} (pivot : Fin q) (source : Tape Bool) (xs : List Bool)
    (a b : Fin q → List Bool) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 3*xs.length+1, Trace pivot input t
      (cfg (.emit .read) source (Counter.marked xs) a b pos ip outRev)
      (cfg (.emit .done) source (NativeClosedStream.word xs) a b
        (positioned pos xs.length) ip (xs.reverse++outRev)) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorOutput.output_trace xs (fun _ => pos .target) input ip outRev
  have he := NativeIOEmbedding.trace_embed (targetBinding q).ports Label.emit
    NativeMatchingXorOutput.program (program pivot)
    (NativeMatchingXorPages.frame source ⟨[],[]⟩ a b pos) input
    (fun pc _ _ => NativeIOEmbedding.bound_instruction_eq _ _ _) htr
  exact ⟨t,ht,by simpa only [embed_emit,Function.update_eq_self,NativeClosedStream.word,positioned] using he⟩



theorem data_trace {q : ℕ} (pivot : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ q*(8*A.length+8)+24*A.length+28, Trace pivot input t
      (cfg (start q) (Counter.marked (A++B)) ⟨[],[]⟩ a b pos ip outRev)
      (cfg (.emit .done) (Counter.marked (A++B))
        (NativeClosedStream.word (A++output A B a b q)) a b
        (positioned pos (2*A.length)) ip ((A++output A B a b q).reverse++outRev)) := by
  obtain ⟨tc,hc,copy⟩ := payload_call pivot A B a b hvalid pos input ip outRev
  have j1 := jump_trace pivot (.payload (.rewind .done)) (.pages (NativeMatchingXorPages.start q))
    (by simp [program]) (Counter.marked (A++B)) (NativeMatchingXorPrefixRewind.splitWord A B)
    a b (positioned pos A.length) input ip outRev
  obtain ⟨tp,hp,pages⟩ := pages_call pivot A B a b hB hvalid (positioned pos A.length) input ip outRev
  have j2 := jump_trace pivot (.pages (.next (Fin.last q))) (.back .back)
    (by simp [program]) (Counter.marked (A++B)) (NativeMatchingXorPrefixRewind.splitWord A (output A B a b q))
    a b (positioned pos A.length) input ip outRev
  obtain ⟨tr,hr,back⟩ := back_call pivot (Counter.marked (A++B)) A (output A B a b q)
    a b pos input ip outRev
  have j3 := jump_trace pivot (.back .done) (.emit .read) (by simp [program])
    (Counter.marked (A++B)) (Counter.marked (A++output A B a b q)) a b pos input ip outRev
  obtain ⟨te,ho,emit⟩ := emit_call pivot (Counter.marked (A++B)) (A++output A B a b q)
    a b pos input ip outRev
  have hl : (A++output A B a b q).length=2*A.length := by
    rw [List.length_append,NativeMatchingXorPages.output_length A B a b hB hvalid]
    omega
  rw [hl] at ho emit
  rw [hB] at hc
  refine ⟨tc+(1+(tp+(1+(tr+(1+te))))),by omega,?_⟩
  exact NativeCountedLoop.trace_trans copy (NativeCountedLoop.trace_trans j1
    (NativeCountedLoop.trace_trans pages (NativeCountedLoop.trace_trans j2
      (NativeCountedLoop.trace_trans back (NativeCountedLoop.trace_trans j3 emit)))))

noncomputable def nativeEncoding (q : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Port q) (start q)
noncomputable def nativeMachine {q : ℕ} (pivot : Fin q) :=
  NativeIO.machine (nativeEncoding q) (program pivot)

theorem fixed_resources {q : ℕ} (pivot : Fin q) : (nativeMachine pivot).k=2+2*q ∧
    (nativeMachine pivot).g+1=5 ∧ (nativeEncoding q).label (start q)=0 := by
  exact ⟨(NativeMatchingXorPages.fixed_tapes q).1,rfl,NativeMicrocode.initialEncoding_start _⟩

theorem native_data {q : ℕ} (pivot : Fin q) (A B : List Bool) (a b : Fin q → List Bool)
    (hB : B.length=A.length) (hvalid : ValidTags A.length a b) (pos : Port q → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ q*(8*A.length+8)+24*A.length+28,
      Transpose.stepN (nativeMachine pivot) input t
        ((cfg (start q) (Counter.marked (A++B)) ⟨[],[]⟩ a b pos ip outRev).denote
          (nativeEncoding q) (program pivot))=
        some ((cfg (.emit .done) (Counter.marked (A++B))
          (NativeClosedStream.word (A++output A B a b q)) a b
          (positioned pos (2*A.length)) ip ((A++output A B a b q).reverse++outRev)).denote
            (nativeEncoding q) (program pivot)) ∧
      Transpose.step (nativeMachine pivot) input
        ((cfg (.emit .done) (Counter.marked (A++B))
          (NativeClosedStream.word (A++output A B a b q)) a b
          (positioned pos (2*A.length)) ip ((A++output A B a b q).reverse++outRev)).denote
            (nativeEncoding q) (program pivot))=none := by
  obtain ⟨t,ht,htr⟩ := data_trace pivot A B a b hB hvalid pos input ip outRev
  refine ⟨t,ht,NativeIO.trace_stepN (nativeEncoding q) (program pivot) input htr,?_⟩
  apply (NativeIO.step_none_iff (nativeEncoding q) (program pivot) input _).mpr
  simp [NativeIO.Active,cfg,workCfg,program,NativeIOEmbedding.boundInstruction,
    NativeMatchingXorOutput.program,FinitePortBinding.instruction]

end TransposeFollowup.NativeMatchingXorData
