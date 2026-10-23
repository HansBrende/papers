import TransposeFollowup.NativeMappedCopy
import TransposeFollowup.NativeClosedStream

/-! Copy a marked payload and position its copy by a physical marked clock.
The source is restored; the clock is read and rewound. The controller has
three tapes and is independent of all word lengths and absolute origins. -/
namespace TransposeFollowup.NativeMatchingXorPayload
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def copyBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports := ⟨![0,1], by decide +kernel⟩
  decode := fun p => if p=0 then some 0 else if p=1 then some 1 else none
  decode_spec := by intro p t; fin_cases p <;> fin_cases t <;> decide

def clockBinding : FinitePortBinding (Fin 1) (Fin 3) where
  ports := ⟨fun _ => 2, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => if p=2 then some 0 else none
  decode_spec := by intro p t; fin_cases p <;> fin_cases t <;> decide

inductive Label
  | copy (pc : NativeMappedCopy.Label)
  | scan | advance
  | rewind (pc : NativeSealBack.Label)
  | reject
  deriving DecidableEq, Fintype

def start : Label := .copy (.init (.erase 0))

def program : Microcode.Program (Fin 3) Label
  | .copy pc => if pc=.seal .done then .jump .scan
      else copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .scan => .read 2 (fun s => match s with
      | .data _ => .advance | .stop => .rewind .back | _ => .reject)
  | .advance => .act (fun p => ⟨none,if p=0 then .stay else .right⟩) .scan
  | .rewind pc => clockBinding.instruction Label.rewind (NativeSealBack.program pc)
  | .reject => .reject

def cfg (pc : Label) (source target clock : Tape Bool) (pos : Fin 3 → ℤ) :
    NativeZipper.Config (Fin 3) Label := ⟨⟨pc,![source,target,clock]⟩,pos⟩

def frame (source target clock : Tape Bool) (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.Frame (Fin 3) :=
  ⟨fun p => (![source,target,clock] p).denote,pos⟩

def advanced (pos : Fin 3 → ℤ) (n : ℕ) (p : Fin 3) : ℤ :=
  pos p + if p=0 then 0 else n

def finalPositions (pos : Fin 3 → ℤ) (n : ℕ) : Fin 3 → ℤ :=
  Function.update pos 1 (pos 1+n)

@[simp] theorem advanced_zero (pos : Fin 3 → ℤ) : advanced pos 0=pos := by
  funext p
  simp [advanced]

theorem copy_code (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy
      (NativeMappedCopy.program id pc) := by
  have h : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem rewind_code (pc : NativeSealBack.Label) :
    program (.rewind pc)=MicrocodeEmbedding.instruction clockBinding.ports Label.rewind
      (NativeSealBack.program pc) := clockBinding.instruction_eq _ _

theorem embed_copy (pc : NativeMappedCopy.Label) (source target clock : Tape Bool)
    (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc source target (fun t => pos (copyBinding.ports t)))
      (frame source ⟨[],[]⟩ clock pos) = (cfg (.copy pc) source target clock pos).denote := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg frame cfg NativeZipper.Config.denote
    Microcode.Config.denote
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_rewind (pc : NativeSealBack.Label) (source target clock : Tape Bool)
    (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed clockBinding.ports Label.rewind
      (NativeSealBack.cfg pc clock (fun _ => z)).denote
      (frame source target clock pos) =
      (cfg (.rewind pc) source target clock (Function.update pos 2 z)).denote := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg frame cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus
  simp only [← clockBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem copy_call (xs tags : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 6*xs.length+14, Trace t
      (cfg start (Counter.marked xs) ⟨[],[]⟩ (Counter.marked tags) pos).denote
      (cfg (.copy (.seal .done)) (Counter.marked xs) (Counter.marked xs)
        (Counter.marked tags) pos).denote := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id xs (fun j => pos (copyBinding.ports j))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy
    (NativeMappedCopy.program id) program
    (frame (Counter.marked xs) ⟨[],[]⟩ (Counter.marked tags) pos) copy_code htr
  exact ⟨t,ht,by simpa only [List.map_id,embed_copy,start] using he⟩

theorem scan_steps (source : Tape Bool) (a tag : Bool)
    (al ar tl tr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 2
      (cfg .scan source ⟨al,.data a::ar⟩ ⟨tl,.data tag::tr⟩ pos) =
      cfg .scan source ⟨.data a::al,ar⟩ ⟨.data tag::tl,tr⟩ (advanced pos 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.read,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp [advanced]

theorem scan_finish (source target : Tape Bool) (tl tr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 1 (cfg .scan source target ⟨tl,.stop::tr⟩ pos)=
      cfg (.rewind .back) source target ⟨tl,.stop::tr⟩ pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Tape.read]

theorem scan_run (source : Tape Bool) (xs tags : List Bool) (hlen : tags.length=xs.length)
    (al ar tl tr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (2*xs.length+1)
      (cfg .scan source ⟨al,symbols xs++ar⟩ ⟨tl,symbols tags++.stop::tr⟩ pos)=
      cfg (.rewind .back) source ⟨(symbols xs).reverse++al,ar⟩
        ⟨(symbols tags).reverse++tl,.stop::tr⟩ (advanced pos xs.length) := by
  induction xs generalizing tags al tl pos with
  | nil =>
    have ht : tags=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst tags
    simpa [symbols] using scan_finish source ⟨al,ar⟩ tl tr pos
  | cons a xs ih =>
    cases tags with
    | nil => simp at hlen
    | cons tag tags =>
      have hlen' : tags.length=xs.length := by simpa using hlen
      rw [show 2*(a::xs).length+1=2+(2*xs.length+1) by simp; omega,NativeZipper.run_add]
      simp only [symbols,List.map_cons,List.cons_append]
      rw [scan_steps]
      have h := ih tags hlen' (.data a::al) (.data tag::tl) (advanced pos 1)
      have hp : advanced (advanced pos 1) xs.length = advanced pos (a::xs).length := by
        funext p
        fin_cases p <;> simp [advanced] <;> omega
      simpa only [symbols,List.map_cons,List.reverse_cons,List.append_assoc,
        List.singleton_append,List.nil_append,hp] using h

theorem rewind_call (source target : Tape Bool) (tags : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*tags.length+4, Trace t
      (cfg (.rewind .back) source target (NativeClosedStream.word tags) pos).denote
      (cfg (.rewind .done) source target (Counter.marked tags)
        (Function.update pos 2 (pos 2-tags.length))).denote := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace tags (fun _ => pos 2)
  have he := MicrocodeEmbedding.trace_embed clockBinding.ports Label.rewind
    NativeSealBack.program program (frame source target (Counter.marked tags) pos)
    (fun pc _ _ => rewind_code pc) htr
  have he0 : MicrocodeEmbedding.embed clockBinding.ports Label.rewind
      (NativeSealBack.cfg .back (RowStream.closedTape tags) (fun _ => pos 2)).denote
      (frame source target (Counter.marked tags) pos)=
      (cfg (.rewind .back) source target (NativeClosedStream.word tags) pos).denote := by
    rw [← NativeClosedStream.word_eq]
    unfold MicrocodeEmbedding.embed NativeSealBack.cfg frame cfg NativeZipper.Config.denote
      Microcode.Config.denote Microcode.focus
    simp only [← clockBinding.values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [he0,embed_rewind] using he⟩

theorem payload_trace (A B tags : List Bool) (hlen : tags.length=A.length) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 6*(A.length+B.length)+4*tags.length+20, Trace t
      (cfg start (Counter.marked (A++B)) ⟨[],[]⟩ (Counter.marked tags) pos).denote
      (cfg (.rewind .done) (Counter.marked (A++B))
        ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩
        (Counter.marked tags) (finalPositions pos A.length)).denote := by
  obtain ⟨tc,hc,copy⟩ := copy_call (A++B) tags pos
  have jump : Trace 1
      (cfg (.copy (.seal .done)) (Counter.marked (A++B)) (Counter.marked (A++B))
        (Counter.marked tags) pos).denote
      (cfg .scan (Counter.marked (A++B)) (Counter.marked (A++B)) (Counter.marked tags) pos).denote :=
    NativeMicrocode.jump_trace _ _ _ rfl
  obtain ⟨ts,hs,scan⟩ := NativeZipper.trace_of_run program
    (scan_run (Counter.marked (A++B)) A tags hlen [.start] (symbols B++[.stop]) [.start] [] pos)
  have hscan : Trace ts
      (cfg .scan (Counter.marked (A++B)) (Counter.marked (A++B)) (Counter.marked tags) pos).denote
      (cfg (.rewind .back) (Counter.marked (A++B))
        ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩
        (NativeClosedStream.word tags) (advanced pos A.length)).denote := by
    simpa only [Counter.marked,symbols,List.map_append,List.append_assoc,NativeClosedStream.word] using scan
  obtain ⟨tr,hr,rewind⟩ := rewind_call (Counter.marked (A++B))
    ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩ tags (advanced pos A.length)
  have hp : Function.update (advanced pos A.length) 2
      (advanced pos A.length 2-tags.length)=finalPositions pos A.length := by
    funext p
    fin_cases p <;> simp [advanced,finalPositions,hlen]
  rw [hp] at rewind
  refine ⟨tc+(1+(ts+tr)),?_,NativeCountedLoop.trace_trans copy
    (NativeCountedLoop.trace_trans jump (NativeCountedLoop.trace_trans hscan rewind))⟩
  simp only [List.length_append] at hc
  omega

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 3) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=33 ∧ nativeEncoding.label start=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card Label-1+1=33
  decide +kernel

theorem native_payload (A B tags : List Bool) (hlen : tags.length=A.length)
    (pos : Fin 3 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 6*(A.length+B.length)+4*tags.length+20,
      Transpose.stepN nativeMachine input t
        ((cfg start (Counter.marked (A++B)) ⟨[],[]⟩ (Counter.marked tags) pos).denote.denote
          nativeEncoding program inputPos outRev)=
        some ((cfg (.rewind .done) (Counter.marked (A++B))
          ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩
          (Counter.marked tags) (finalPositions pos A.length)).denote.denote
            nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg (.rewind .done) (Counter.marked (A++B))
          ⟨(symbols A).reverse++[.start],symbols B++[.stop]⟩
          (Counter.marked tags) (finalPositions pos A.length)).denote.denote
            nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := payload_trace A B tags hlen pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program,
    FinitePortBinding.instruction,NativeSealBack.program]

end TransposeFollowup.NativeMatchingXorPayload
