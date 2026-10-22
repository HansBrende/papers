import TransposeFollowup.NativeClosedStream
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.SeedMultipleMeaning

/-! A marked template controls the width of an unmarked input field.
One input bit is appended for each template bit. The existing native
rewind restores the template; input and output advance by the field width. -/
namespace TransposeFollowup.NativeFieldAppend
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label
  | scan | read | emit (b : Bool) | rewind (pc : NativeSealBack.Label) | reject
  deriving DecidableEq,Fintype

def templateBinding : FinitePortBinding (Fin 1) (Fin 3) where
  ports:=⟨fun _ => 0,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=0 then some 0 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel

def actions (b : Bool) : Fin 3 → Microcode.Action := fun p => ⟨if p=2 then some (.data b) else none,.right⟩

def program : Microcode.Program (Fin 3) Label
  | .scan => .read 0 (fun s => match s with | .data _ => .read | .stop => .rewind .back | _ => .reject)
  | .read => .read 1 (fun s => match s with | .data b => .emit b | _ => .reject)
  | .emit b => .act (actions b) .scan
  | .rewind pc => templateBinding.instruction Label.rewind (NativeSealBack.program pc)
  | .reject => .reject

theorem rewind_code (pc : NativeSealBack.Label) (_ : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    program (.rewind pc)=MicrocodeEmbedding.instruction templateBinding.ports Label.rewind (NativeSealBack.program pc) :=
  templateBinding.instruction_eq _ _

def bank (template input output : Tape Bool) : Fin 3 → Tape Bool := ![template,input,output]
def cfg (pc : Label) (template input output : Tape Bool) (pos : Fin 3 → ℤ) : NativeZipper.Config (Fin 3) Label :=
  ⟨⟨pc,bank template input output⟩,pos⟩
def frame (template input output : Tape Bool) (pos : Fin 3 → ℤ) : MicrocodeEmbedding.Frame (Fin 3) :=
  ⟨fun p => (bank template input output p).denote,pos⟩
def finalPositions (pos : Fin 3 → ℤ) (m : ℕ) : Fin 3 → ℤ := fun p => pos p+if p=0 then 0 else (m : ℤ)

theorem three_steps (a b : Bool) (lt rt li ri lo : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 3 (cfg .scan ⟨lt,.data a::rt⟩ ⟨li,.data b::ri⟩ ⟨lo,[]⟩ pos)=
      cfg .scan ⟨.data a::lt,rt⟩ ⟨.data b::li,ri⟩ ⟨.data b::lo,[]⟩ (NativeZipper.shiftPositions pos 1) := by
  simp only [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,
    Matrix.cons_val_zero,Matrix.cons_val_one,Microcode.Action.apply,actions,Tape.read,List.headD_cons]
  congr 2
  funext p;fin_cases p <;> rfl

theorem forward_run (template field : List Bool) (hw : template.length=field.length)
    (lt li lo suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (3*template.length)
      (cfg .scan ⟨lt,symbols template++[.stop]⟩ ⟨li,symbols field++suffix⟩ ⟨lo,[]⟩ pos)=
      cfg .scan ⟨(symbols template).reverse++lt,[.stop]⟩ ⟨(symbols field).reverse++li,suffix⟩
        ⟨(symbols field).reverse++lo,[]⟩ (NativeZipper.shiftPositions pos template.length) := by
  induction template generalizing field lt li lo pos with
  | nil =>
    cases field <;> simp_all [NativeZipper.run,OperationalTrace.run,cfg,symbols]
  | cons a template ih =>
    cases field with
    | nil => simp at hw
    | cons b field =>
      have hl : template.length=field.length := by simp only [List.length_cons] at hw;omega
      rw [show 3*(a::template).length=3+3*template.length by simp;omega,NativeZipper.run_add]
      simp only [symbols,List.map_cons,List.cons_append]
      rw [three_steps]
      have hh := ih field hl (.data a::lt) (.data b::li) (.data b::lo) (NativeZipper.shiftPositions pos 1)
      simpa only [symbols,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,
        NativeZipper.shiftPositions_add,List.length_cons,Nat.cast_add,Nat.cast_one,add_comm (1 : ℤ)] using hh

end TransposeFollowup.NativeFieldAppend


namespace TransposeFollowup.NativeFieldAppend
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem embed_rewind (pc : NativeSealBack.Label) (word base input output : Tape Bool) (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed templateBinding.ports Label.rewind (NativeSealBack.cfg pc word (fun _ => z)).denote
      (frame base input output pos)=(cfg (.rewind pc) word input output (Function.update pos 0 z)).denote := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← templateBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem back_positions (pos : Fin 3 → ℤ) (m : ℕ) :
    Function.update (NativeZipper.shiftPositions pos m) 0 (NativeZipper.shiftPositions pos m 0-m)=finalPositions pos m := by
  funext p
  fin_cases p <;> simp [NativeZipper.shiftPositions,finalPositions]

theorem rewind_call (template : List Bool) (input output : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*template.length+4, Trace t
      (cfg (.rewind .back) (NativeClosedStream.word template) input output (NativeZipper.shiftPositions pos template.length)).denote
      (cfg (.rewind .done) (Counter.marked template) input output (finalPositions pos template.length)).denote := by
  let adv := NativeZipper.shiftPositions pos template.length
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace template (fun _ => adv 0)
  rw [← NativeClosedStream.word_eq] at htr
  have he := MicrocodeEmbedding.trace_embed templateBinding.ports Label.rewind NativeSealBack.program program
    (frame (NativeClosedStream.word template) input output adv) rewind_code htr
  refine ⟨t,ht,?_⟩
  simpa only [embed_rewind,Function.update_eq_self,adv,back_positions] using he

theorem stop_trace (left : List (Sym Bool)) (input output : Tape Bool) (pos : Fin 3 → ℤ) :
    Trace 1 (cfg .scan ⟨left,[.stop]⟩ input output pos).denote
      (cfg (.rewind .back) ⟨left,[.stop]⟩ input output pos).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program]
  · exact .refl _

theorem append_trace (template field : List Bool) (hw : template.length=field.length)
    (pre suffix outPre : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5*template.length+5, Trace t
      (cfg .scan (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨outPre,[]⟩ pos).denote
      (cfg (.rewind .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        ⟨(symbols field).reverse++outPre,[]⟩ (finalPositions pos template.length)).denote := by
  obtain ⟨a,ha,ta⟩ := NativeZipper.trace_of_run program (forward_run template field hw [.start] pre outPre suffix pos)
  have tj := stop_trace ((symbols template).reverse++[.start]) ⟨(symbols field).reverse++pre,suffix⟩
    ⟨(symbols field).reverse++outPre,[]⟩ (NativeZipper.shiftPositions pos template.length)
  obtain ⟨b,hb,tb⟩ := rewind_call template ⟨(symbols field).reverse++pre,suffix⟩ ⟨(symbols field).reverse++outPre,[]⟩ pos
  exact ⟨a+1+b,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 3) Label.scan
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=11 ∧ nativeEncoding.label .scan=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_append (template field : List Bool) (hw : template.length=field.length)
    (pre suffix outPre : List (Sym Bool)) (pos : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*template.length+5,
      Transpose.stepN nativeMachine input t
        ((cfg .scan (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨outPre,[]⟩ pos).denote.denote nativeEncoding program inputPos outRev)=
        some ((cfg (.rewind .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
          ⟨(symbols field).reverse++outPre,[]⟩ (finalPositions pos template.length)).denote.denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input ((cfg (.rewind .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        ⟨(symbols field).reverse++outPre,[]⟩ (finalPositions pos template.length)).denote.denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := append_trace template field hw pre suffix outPre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,program,FinitePortBinding.instruction,NativeSealBack.program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 3 ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (template field : List Bool) (hw : template.length=field.length) (pre suffix outPre : List (Sym Bool)) (pos : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 5*template.length+5,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg .scan (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨outPre,[]⟩ pos).denote
          outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.rewind .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
            ⟨(symbols field).reverse++outPre,[]⟩ (finalPositions pos template.length)).denote outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := append_trace template field hw pre suffix outPre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeFieldAppend


/-! Copy one unmarked, template-sized input field into a blank tape.
The existing buffer initializer and seal/rewind routines pay for both
markers and restore the output head. Only the input field head advances. -/
namespace TransposeFollowup.NativeFieldCopy
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Label
  | init (pc : NativeBuffer.Label)
  | append (pc : NativeFieldAppend.Label)
  | seal (pc : NativeSealBack.Label)
  deriving DecidableEq,Fintype

def targetBinding : FinitePortBinding (Fin 1) (Fin 3) where
  ports:=⟨fun _ => 2,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=2 then some 0 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel

def allBinding : FinitePortBinding (Fin 3) (Fin 3) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intro p j;simp [eq_comm]

def program : Microcode.Program (Fin 3) Label
  | .init .done => .jump (.append .scan)
  | .init pc => targetBinding.instruction Label.init (NativeBuffer.program pc)
  | .append (.rewind .done) => .jump (.seal .seal)
  | .append pc => allBinding.instruction Label.append (NativeFieldAppend.program pc)
  | .seal pc => targetBinding.instruction Label.seal (NativeSealBack.program pc)

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program (.init pc)=MicrocodeEmbedding.instruction targetBinding.ports Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem append_code (pc : NativeFieldAppend.Label) (hh : NativeFieldAppend.program pc≠.halt) (_ : NativeFieldAppend.program pc≠.reject) :
    program (.append pc)=MicrocodeEmbedding.instruction allBinding.ports Label.append (NativeFieldAppend.program pc) := by
  cases pc with
  | rewind pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,FinitePortBinding.instruction_eq]
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem seal_code (pc : NativeSealBack.Label) (_ : NativeSealBack.program pc≠.halt) (_ : NativeSealBack.program pc≠.reject) :
    program (.seal pc)=MicrocodeEmbedding.instruction targetBinding.ports Label.seal (NativeSealBack.program pc) :=
  targetBinding.instruction_eq _ _

def cfg (pc : Label) (template input output : Tape Bool) (pos : Fin 3 → ℤ) : NativeMicrocode.Config (Fin 3) Label :=
  ⟨⟨pc,fun p => (NativeFieldAppend.bank template input output p).denote⟩,pos⟩
def finalPositions (pos : Fin 3 → ℤ) (m : ℕ) : Fin 3 → ℤ := fun p => pos p+if p=1 then (m : ℤ) else 0
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem embed_init (pc : NativeBuffer.Label) (word template input base : Tape Bool) (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports Label.init (NativeBuffer.cfg pc word (fun _ => z)).denote
      (NativeFieldAppend.frame template input base pos)=cfg (.init pc) template input word (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus NativeFieldAppend.frame cfg
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_append (pc : NativeFieldAppend.Label) (template input output : Tape Bool) (pos : Fin 3 → ℤ)
    (base : MicrocodeEmbedding.Frame (Fin 3)) :
    MicrocodeEmbedding.embed allBinding.ports Label.append (NativeFieldAppend.cfg pc template input output pos).denote base=
      cfg (.append pc) template input output pos := by
  unfold MicrocodeEmbedding.embed NativeFieldAppend.cfg NativeZipper.Config.denote Microcode.Config.denote cfg
  simp only [← allBinding.values_eq_extend]
  rfl

theorem embed_seal (pc : NativeSealBack.Label) (word template input base : Tape Bool) (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports Label.seal (NativeSealBack.cfg pc word (fun _ => z)).denote
      (NativeFieldAppend.frame template input base pos)=cfg (.seal pc) template input word (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus NativeFieldAppend.frame cfg
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem init_call (template input : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2,Trace t (cfg (.init (.erase 0)) template input ⟨[],[]⟩ pos)
      (cfg (.init .done) template input BinaryCarry.preparedOutput pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos 2)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.init NativeBuffer.program program
    (NativeFieldAppend.frame template input ⟨[],[]⟩ pos) init_code htr
  exact ⟨t,ht,by simpa only [embed_init,Function.update_eq_self] using he⟩

theorem append_call (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5*template.length+5,Trace t
      (cfg (.append .scan) (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos)
      (cfg (.append (.rewind .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (NativeSealBack.openWord field) (NativeFieldAppend.finalPositions pos template.length)) := by
  obtain ⟨t,ht,htr⟩ := NativeFieldAppend.append_trace template field hw pre suffix [.start] pos
  have he := MicrocodeEmbedding.trace_embed allBinding.ports Label.append NativeFieldAppend.program program
    (NativeFieldAppend.frame (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos) append_code htr
  exact ⟨t,ht,by simpa only [embed_append,NativeSealBack.openWord,BinaryCarry.preparedOutput,symbols,List.map_reverse] using he⟩

theorem seal_positions (pos : Fin 3 → ℤ) (m : ℕ) :
    Function.update (NativeFieldAppend.finalPositions pos m) 2 (NativeFieldAppend.finalPositions pos m 2-m)=finalPositions pos m := by
  funext p;fin_cases p <;> simp [NativeFieldAppend.finalPositions,finalPositions]

theorem seal_call (template field : List Bool) (hw : template.length=field.length) (input : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*template.length+5,Trace t
      (cfg (.seal .seal) (Counter.marked template) input (NativeSealBack.openWord field) (NativeFieldAppend.finalPositions pos template.length))
      (cfg (.seal .done) (Counter.marked template) input (Counter.marked field) (finalPositions pos template.length)) := by
  let adv := NativeFieldAppend.finalPositions pos template.length
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace field (fun _ => adv 2)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports Label.seal NativeSealBack.program program
    (NativeFieldAppend.frame (Counter.marked template) input (NativeSealBack.openWord field) adv) seal_code htr
  refine ⟨t,by omega,?_⟩
  simpa only [embed_seal,Function.update_eq_self,← hw,adv,seal_positions] using he

theorem jump_trace (pc next : Label) (template input output : Tape Bool) (pos : Fin 3 → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc template input output pos) (cfg next template input output pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem copy_trace (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 7*template.length+14,Trace t
      (cfg (.init (.erase 0)) (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos)
      (cfg (.seal .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (Counter.marked field) (finalPositions pos template.length)) := by
  obtain ⟨a,ha,ta⟩ := init_call (Counter.marked template) ⟨pre,symbols field++suffix⟩ pos
  have j1 := jump_trace (.init .done) (.append .scan) (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos rfl
  obtain ⟨b,hb,tb⟩ := append_call template field hw pre suffix pos
  have j2 := jump_trace (.append (.rewind .done)) (.seal .seal) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
    (NativeSealBack.openWord field) (NativeFieldAppend.finalPositions pos template.length) rfl
  obtain ⟨c,hc,tc⟩ := seal_call template field hw ⟨(symbols field).reverse++pre,suffix⟩ pos
  exact ⟨a+1+b+1+c,by omega,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Fin 3) (Label.init (.erase 0))
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=3 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=27 ∧
    nativeEncoding.label (.init (.erase 0))=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  decide +kernel

theorem native_copy (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 7*template.length+14,
      Transpose.stepN nativeMachine input t ((cfg (.init (.erase 0)) (Counter.marked template)
        ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg (.seal .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
          (Counter.marked field) (finalPositions pos template.length)).denote nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input ((cfg (.seal .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (Counter.marked field) (finalPositions pos template.length)).denote nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := copy_trace template field hw pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,NativeSealBack.program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 3 ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (template field : List Bool) (hw : template.length=field.length) (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 7*template.length+14,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (.init (.erase 0)) (Counter.marked template)
          ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos) outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.seal .done) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
            (Counter.marked field) (finalPositions pos template.length)) outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := copy_trace template field hw pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.NativeFieldCopy


/-! The field-copy front end is followed by the existing fixed zero-fill
and sealing tail. C is part of finite control, never a runtime width. -/
namespace TransposeFollowup.NativePaddedField
open FixedTapeCompiler CopyMachine
open NativeFieldCopy (targetBinding allBinding)
set_option autoImplicit false

def padded (C : ℕ) (field : List Bool) := field++List.replicate C false

theorem padded_length (C : ℕ) (field : List Bool) : (padded C field).length=field.length+C := by simp [padded]
theorem padded_value (C : ℕ) (field : List Bool) : Counter.value (padded C field)=Counter.value field :=
  PaddedWord.value_append_zeroes field C

inductive Label (C : ℕ)
  | init (pc : NativeBuffer.Label)
  | append (pc : NativeFieldAppend.Label)
  | tail (pc : PaddedWord.Label C)
  deriving DecidableEq,Fintype

def tailBinding : FinitePortBinding (Fin 2) (Fin 3) where
  ports:=⟨![0,2],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=2 then some 1 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel

def program (C : ℕ) : Microcode.Program (Fin 3) (Label C)
  | .init .done => .jump (.append .scan)
  | .init pc => targetBinding.instruction Label.init (NativeBuffer.program pc)
  | .append (.rewind .done) => .jump (.tail (.fill ⟨C,by omega⟩))
  | .append pc => allBinding.instruction Label.append (NativeFieldAppend.program pc)
  | .tail pc => tailBinding.instruction Label.tail (PaddedWord.program C id pc)

theorem init_code (C : ℕ) (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc≠.halt) (_ : NativeBuffer.program pc≠.reject) :
    program C (.init pc)=MicrocodeEmbedding.instruction targetBinding.ports Label.init (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem append_code (C : ℕ) (pc : NativeFieldAppend.Label) (hh : NativeFieldAppend.program pc≠.halt) (_ : NativeFieldAppend.program pc≠.reject) :
    program C (.append pc)=MicrocodeEmbedding.instruction allBinding.ports Label.append (NativeFieldAppend.program pc) := by
  cases pc with
  | rewind pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,FinitePortBinding.instruction_eq]
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem tail_code (C : ℕ) (pc : PaddedWord.Label C) (_ : PaddedWord.program C id pc≠.halt) (_ : PaddedWord.program C id pc≠.reject) :
    program C (.tail pc)=MicrocodeEmbedding.instruction tailBinding.ports Label.tail (PaddedWord.program C id pc) :=
  tailBinding.instruction_eq _ _

def cfg {C : ℕ} (pc : Label C) (template input output : Tape Bool) (pos : Fin 3 → ℤ) : NativeMicrocode.Config (Fin 3) (Label C) :=
  ⟨⟨pc,fun p => (NativeFieldAppend.bank template input output p).denote⟩,pos⟩
abbrev Trace (C : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program C)) (NativeMicrocode.Active (program C))

theorem tail_trace (C : ℕ) (source : Tape Bool) (field : List Bool) (pos : Fin 2 → ℤ) :
    ∃ t ≤ 2*field.length+3*C+6, PaddedWord.Trace C id t
      (PaddedWord.cfg (.fill ⟨C,by omega⟩) source (NativeSealBack.openWord field) pos)
      (PaddedWord.cfg (.seal .done) source (Counter.marked (padded C field)) (Function.update pos 1 (pos 1-field.length))) := by
  have ta := PaddedWord.fill_trace C id C le_rfl source field pos
  obtain ⟨b,hb,tb⟩ := PaddedWord.seal_call C id source (padded C field) (NativeMappedAppend.finalPositions pos C)
  have hp : Function.update (NativeMappedAppend.finalPositions pos C) 1
      (NativeMappedAppend.finalPositions pos C 1-(padded C field).length)=Function.update pos 1 (pos 1-field.length) := by
    funext p;fin_cases p <;> simp [NativeMappedAppend.finalPositions,padded_length]
  rw [hp] at tb
  rw [padded_length] at hb
  exact ⟨C+1+b,by omega,NativeCountedLoop.trace_trans ta tb⟩

end TransposeFollowup.NativePaddedField


namespace TransposeFollowup.NativePaddedField
open FixedTapeCompiler CopyMachine
open NativeFieldCopy (targetBinding allBinding)
set_option autoImplicit false

theorem embed_init (C : ℕ) (pc : NativeBuffer.Label) (word template input base : Tape Bool) (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed targetBinding.ports (Label.init (C:=C)) (NativeBuffer.cfg pc word (fun _ => z)).denote
      (NativeFieldAppend.frame template input base pos)=cfg (.init pc) template input word (Function.update pos 2 z) := by
  unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus NativeFieldAppend.frame cfg
  simp only [← targetBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem embed_append (C : ℕ) (pc : NativeFieldAppend.Label) (template input output : Tape Bool) (pos : Fin 3 → ℤ)
    (base : MicrocodeEmbedding.Frame (Fin 3)) :
    MicrocodeEmbedding.embed allBinding.ports (Label.append (C:=C)) (NativeFieldAppend.cfg pc template input output pos).denote base=
      cfg (.append pc) template input output pos := by
  unfold MicrocodeEmbedding.embed NativeFieldAppend.cfg NativeZipper.Config.denote Microcode.Config.denote cfg
  simp only [← allBinding.values_eq_extend]
  rfl

theorem embed_tail (C : ℕ) (pc : PaddedWord.Label C) (template input output base : Tape Bool) (tpos : Fin 2 → ℤ) (pos : Fin 3 → ℤ) :
    MicrocodeEmbedding.embed tailBinding.ports (Label.tail (C:=C)) (PaddedWord.cfg pc template output tpos)
      (NativeFieldAppend.frame template input base pos)=cfg (.tail pc) template input output (tailBinding.values tpos pos) := by
  unfold MicrocodeEmbedding.embed PaddedWord.cfg NativeFieldAppend.frame cfg
  simp only [← tailBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem init_call (C : ℕ) (template input : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2,Trace C t (cfg (.init (.erase 0)) template input ⟨[],[]⟩ pos)
      (cfg (.init .done) template input BinaryCarry.preparedOutput pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos 2)
  have he := MicrocodeEmbedding.trace_embed targetBinding.ports (Label.init (C:=C)) NativeBuffer.program (program C)
    (NativeFieldAppend.frame template input ⟨[],[]⟩ pos) (init_code C) htr
  exact ⟨t,ht,by simpa only [embed_init,Function.update_eq_self] using he⟩

theorem append_call (C : ℕ) (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 5*template.length+5,Trace C t
      (cfg (.append .scan) (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos)
      (cfg (.append (.rewind .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (NativeSealBack.openWord field) (NativeFieldAppend.finalPositions pos template.length)) := by
  obtain ⟨t,ht,htr⟩ := NativeFieldAppend.append_trace template field hw pre suffix [.start] pos
  have he := MicrocodeEmbedding.trace_embed allBinding.ports (Label.append (C:=C)) NativeFieldAppend.program (program C)
    (NativeFieldAppend.frame (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos) (append_code C) htr
  exact ⟨t,ht,by simpa only [embed_append,NativeSealBack.openWord,BinaryCarry.preparedOutput] using he⟩

theorem tail_call (C : ℕ) (template field : List Bool) (hw : template.length=field.length) (input : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*template.length+3*C+6,Trace C t
      (cfg (.tail (.fill ⟨C,by omega⟩)) (Counter.marked template) input (NativeSealBack.openWord field)
        (NativeFieldAppend.finalPositions pos template.length))
      (cfg (.tail (.seal .done)) (Counter.marked template) input (Counter.marked (padded C field))
        (NativeFieldCopy.finalPositions pos template.length)) := by
  let adv := NativeFieldAppend.finalPositions pos template.length
  obtain ⟨t,ht,htr⟩ := tail_trace C (Counter.marked template) field ![adv 0,adv 2]
  have he := MicrocodeEmbedding.trace_embed tailBinding.ports (Label.tail (C:=C)) (PaddedWord.program C id) (program C)
    (NativeFieldAppend.frame (Counter.marked template) input (NativeSealBack.openWord field) adv) (tail_code C) htr
  have hi : tailBinding.values ![adv 0,adv 2] adv=adv := by funext p;fin_cases p <;> rfl
  have hf : tailBinding.values (Function.update ![adv 0,adv 2] 1 (adv 2-field.length)) adv=
      NativeFieldCopy.finalPositions pos template.length := by
    funext p;fin_cases p <;> simp [tailBinding,FinitePortBinding.values,adv,NativeFieldAppend.finalPositions,NativeFieldCopy.finalPositions,hw]
  exact ⟨t,by omega,by simpa only [embed_tail,hi,Matrix.cons_val_one,Matrix.cons_val_zero,hf] using he⟩

theorem jump_trace (C : ℕ) (pc next : Label C) (template input output : Tape Bool) (pos : Fin 3 → ℤ)
    (h : program C pc=.jump next) : Trace C 1 (cfg pc template input output pos) (cfg next template input output pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.NativePaddedField


namespace TransposeFollowup.NativePaddedField
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem copy_trace (C : ℕ) (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 7*template.length+3*C+15,Trace C t
      (cfg (.init (.erase 0)) (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos)
      (cfg (.tail (.seal .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (Counter.marked (padded C field)) (NativeFieldCopy.finalPositions pos template.length)) := by
  obtain ⟨a,ha,ta⟩ := init_call C (Counter.marked template) ⟨pre,symbols field++suffix⟩ pos
  have j1 := jump_trace C (.init .done) (.append .scan) (Counter.marked template) ⟨pre,symbols field++suffix⟩ BinaryCarry.preparedOutput pos rfl
  obtain ⟨b,hb,tb⟩ := append_call C template field hw pre suffix pos
  have j2 := jump_trace C (.append (.rewind .done)) (.tail (.fill ⟨C,by omega⟩)) (Counter.marked template)
    ⟨(symbols field).reverse++pre,suffix⟩ (NativeSealBack.openWord field) (NativeFieldAppend.finalPositions pos template.length) rfl
  obtain ⟨c,hc,tc⟩ := tail_call C template field hw ⟨(symbols field).reverse++pre,suffix⟩ pos
  exact ⟨a+1+b+1+c,by omega,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc⟩

noncomputable def nativeEncoding (C : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 3) (Label.init (C:=C) (.erase 0))
noncomputable def nativeMachine (C : ℕ) := NativeMicrocode.machine (nativeEncoding C) (program C)

def labelEquiv (C : ℕ) : Label C ≃ NativeBuffer.Label ⊕ NativeFieldAppend.Label ⊕ PaddedWord.Label C where
  toFun | .init pc => .inl pc | .append pc => .inr (.inl pc) | .tail pc => .inr (.inr pc)
  invFun | .inl pc => .init pc | .inr (.inl pc) => .append pc | .inr (.inr pc) => .tail pc
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|pc) <;> rfl

theorem fixed_resources (C : ℕ) : (nativeMachine C).k=3 ∧ (nativeMachine C).g+1=5 ∧ (nativeMachine C).q+1=C+54 ∧
    (nativeEncoding C).label (.init (.erase 0))=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label C)-1+1=_
  rw [Fintype.card_congr (labelEquiv C)]
  have hb : Fintype.card NativeBuffer.Label=10 := NativeBuffer.fixed_resources.2.2
  have ha : Fintype.card NativeFieldAppend.Label=11 := by decide +kernel
  simp only [Fintype.card_sum,hb,ha,PaddedWord.label_card]
  omega

theorem native_copy (C : ℕ) (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 7*template.length+3*C+15,
      Transpose.stepN (nativeMachine C) input t ((cfg (.init (.erase 0)) (Counter.marked template)
        ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos).denote (nativeEncoding C) (program C) inputPos outRev)=
        some ((cfg (.tail (.seal .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
          (Counter.marked (padded C field)) (NativeFieldCopy.finalPositions pos template.length)).denote (nativeEncoding C) (program C) inputPos outRev) ∧
      Transpose.step (nativeMachine C) input ((cfg (.tail (.seal .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
        (Counter.marked (padded C field)) (NativeFieldCopy.finalPositions pos template.length)).denote (nativeEncoding C) (program C) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := copy_trace C template field hw pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding C) (program C) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C) (program C) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program,FinitePortBinding.instruction,PaddedWord.program,NativeSealBack.program]

theorem native_call {U J : Type*} {k q : ℕ} (C : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 3 ↪ U) (labels : Label C → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program C pc≠.halt → program C pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program C pc))
    (template field : List Bool) (hw : template.length=field.length) (pre suffix : List (Sym Bool)) (pos : Fin 3 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 7*template.length+3*C+15,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg (.init (.erase 0)) (Counter.marked template)
          ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ pos) outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.tail (.seal .done)) (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩
            (Counter.marked (padded C field)) (NativeFieldCopy.finalPositions pos template.length)) outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := copy_trace C template field hw pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program C) target outerFrame input inputPos outRev hc htr⟩

theorem common_width (ell small large : ℕ) (h : small≤large) (field : List Bool) (hw : field.length=2*ell+small) :
    (padded (large-small) field).length=2*ell+large ∧ Counter.value (padded (large-small) field)=Counter.value field := by
  refine ⟨?_,padded_value _ _⟩
  rw [padded_length,hw]
  omega

end TransposeFollowup.NativePaddedField


/-! A real boundary read distinguishes a pair from a batch STOP. Two
field-copy calls share template/input tapes and retain the first result
while copying the second. A consumed STOP is returned as a separate flag. -/
namespace TransposeFollowup.NativePairReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def outPort (second : Bool) : Fin 4 := if second then 3 else 2
def copyPort (second : Bool) : Fin 3 → Fin 4 := ![0,1,outPort second]
def copyBinding (second : Bool) : FinitePortBinding (Fin 3) (Fin 4) where
  ports:=⟨copyPort second,by cases second <;> decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else if p=outPort second then some 2 else none
  decode_spec:=by intro p j;cases second <;> fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (C : ℕ)
  | check | copy (second : Bool) (pc : NativePaddedField.Label C) | stop | done (pair : Bool) | reject
  deriving DecidableEq,Fintype

def program (C : ℕ) : Microcode.Program (Fin 4) (Label C)
  | .check => .read 1 (fun s => match s with | .data _ => .copy false (.init (.erase 0)) | .stop => .stop | _ => .reject)
  | .copy false (.tail (.seal .done)) => .jump (.copy true (.init (.erase 0)))
  | .copy true (.tail (.seal .done)) => .jump (.done true)
  | .copy second pc => (copyBinding second).instruction (Label.copy second) (NativePaddedField.program C pc)
  | .stop => .act (Microcode.single 1 ⟨none,.right⟩) (.done false)
  | .done _ => .halt
  | .reject => .reject

theorem copy_code (C : ℕ) (second : Bool) (pc : NativePaddedField.Label C)
    (hh : NativePaddedField.program C pc≠.halt) (_ : NativePaddedField.program C pc≠.reject) :
    program C (.copy second pc)=MicrocodeEmbedding.instruction (copyBinding second).ports (Label.copy second)
      (NativePaddedField.program C pc) := by
  cases pc with
  | tail pc =>
    cases pc with
    | «seal» pc =>
      cases pc with
      | done => exact False.elim (hh rfl)
      | _ => cases second <;> simp only [program,FinitePortBinding.instruction_eq]
    | _ => cases second <;> simp only [program,FinitePortBinding.instruction_eq]
  | _ => cases second <;> simp only [program,FinitePortBinding.instruction_eq]

def bank (template input first second : Tape Bool) : Fin 4 → Tape Bool := ![template,input,first,second]
def withOutput (second : Bool) (template input word other : Tape Bool) : Fin 4 → Tape Bool :=
  if second then bank template input other word else bank template input word other
def cfg {C : ℕ} (pc : Label C) (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ) : NativeMicrocode.Config (Fin 4) (Label C) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ) : MicrocodeEmbedding.Frame (Fin 4) := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Fin 4 → ℤ) (m : ℕ) : Fin 4 → ℤ := fun p => pos p+if p=1 then (m : ℤ) else 0
abbrev Trace (C : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program C)) (NativeMicrocode.Active (program C))

theorem advance_add (pos : Fin 4 → ℤ) (a b : ℕ) : advance (advance pos a) b=advance pos (a+b) := by
  funext p;fin_cases p <;> simp [advance,add_assoc]

theorem embed_copy (C : ℕ) (second : Bool) (pc : NativePaddedField.Label C) (template input word other baseTemplate baseInput : Tape Bool)
    (rpos : Fin 3 → ℤ) (pos : Fin 4 → ℤ) :
    MicrocodeEmbedding.embed (copyBinding second).ports (Label.copy (C:=C) second) (NativePaddedField.cfg pc template input word rpos)
      (frame (withOutput second baseTemplate baseInput ⟨[],[]⟩ other) pos)=
      cfg (.copy second pc) (withOutput second template input word other) ((copyBinding second).values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativePaddedField.cfg cfg frame
  simp only [← (copyBinding second).values_eq_extend]
  congr 2
  funext p;cases second <;> fin_cases p <;> rfl

theorem copy_positions (second : Bool) (pos : Fin 4 → ℤ) :
    (copyBinding second).values (fun p => pos (copyPort second p)) pos=pos := by
  funext p;cases second <;> fin_cases p <;> rfl

theorem copy_final_positions (second : Bool) (pos : Fin 4 → ℤ) (m : ℕ) :
    (copyBinding second).values (NativeFieldCopy.finalPositions (fun p => pos (copyPort second p)) m) pos=advance pos m := by
  funext p;cases second <;> fin_cases p <;>
    simp [copyBinding,FinitePortBinding.values,NativeFieldCopy.finalPositions,copyPort,outPort,advance]

theorem copy_call (C : ℕ) (second : Bool) (template field : List Bool) (hw : template.length=field.length)
    (pre suffix : List (Sym Bool)) (other : Tape Bool) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 7*template.length+3*C+15,Trace C t
      (cfg (.copy second (.init (.erase 0))) (withOutput second (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ other) pos)
      (cfg (.copy second (.tail (.seal .done)))
        (withOutput second (Counter.marked template) ⟨(symbols field).reverse++pre,suffix⟩ (Counter.marked (NativePaddedField.padded C field)) other)
        (advance pos template.length)) := by
  obtain ⟨t,ht,htr⟩ := NativePaddedField.copy_trace C template field hw pre suffix (fun p => pos (copyPort second p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding second).ports (Label.copy (C:=C) second) (NativePaddedField.program C) (program C)
    (frame (withOutput second (Counter.marked template) ⟨pre,symbols field++suffix⟩ ⟨[],[]⟩ other) pos) (copy_code C second) htr
  exact ⟨t,ht,by simpa only [embed_copy,copy_positions,copy_final_positions] using he⟩

theorem jump_trace (C : ℕ) (pc next : Label C) (s : Fin 4 → Tape Bool) (pos : Fin 4 → ℤ)
    (h : program C pc=.jump next) : Trace C 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.NativePairReader


namespace TransposeFollowup.NativePairReader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem check_trace (C : ℕ) (template first second : List Bool) (hp : 0<first.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    Trace C 1 (cfg .check (bank (Counter.marked template) ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.copy false (.init (.erase 0))) (bank (Counter.marked template) ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos) := by
  cases first with
  | nil => simp at hp
  | cons b first =>
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,cfg,program]
    · exact .refl _

theorem pair_trace (C : ℕ) (template first second : List Bool) (hp : 0<template.length)
    (hfirst : template.length=first.length) (hsecond : template.length=second.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 14*template.length+6*C+33,Trace C t
      (cfg .check (bank (Counter.marked template) ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.done true) (bank (Counter.marked template) ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked (NativePaddedField.padded C first)) (Counter.marked (NativePaddedField.padded C second)))
        (advance pos (2*template.length))) := by
  have ti := check_trace C template first second (by omega) pre suffix pos
  obtain ⟨a,ha,ta⟩ := copy_call C false template first hfirst pre (symbols second++suffix) ⟨[],[]⟩ pos
  have j1 := jump_trace C (.copy false (.tail (.seal .done))) (.copy true (.init (.erase 0)))
    (bank (Counter.marked template) ⟨(symbols first).reverse++pre,symbols second++suffix⟩
      (Counter.marked (NativePaddedField.padded C first)) ⟨[],[]⟩) (advance pos template.length) rfl
  obtain ⟨b,hb,tb⟩ := copy_call C true template second hsecond ((symbols first).reverse++pre) suffix
    (Counter.marked (NativePaddedField.padded C first)) (advance pos template.length)
  have j2 := jump_trace C (.copy true (.tail (.seal .done))) (.done true)
    (bank (Counter.marked template) ⟨(symbols second).reverse++((symbols first).reverse++pre),suffix⟩
      (Counter.marked (NativePaddedField.padded C first)) (Counter.marked (NativePaddedField.padded C second)))
      (advance (advance pos template.length) template.length) rfl
  have ti' : Trace C 1 (cfg .check (bank (Counter.marked template) ⟨pre,symbols first++(symbols second++suffix)⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.copy false (.init (.erase 0))) (bank (Counter.marked template) ⟨pre,symbols first++(symbols second++suffix)⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos) := by
    simpa only [symbols,List.map_append,List.append_assoc] using ti
  refine ⟨1+(a+(1+(b+1))),by omega,?_⟩
  simpa [withOutput,symbols,List.map_append,List.reverse_append,List.append_assoc,advance_add,two_mul] using
    NativeCountedLoop.trace_trans ti' (NativeCountedLoop.trace_trans ta (NativeCountedLoop.trace_trans j1 (NativeCountedLoop.trace_trans tb j2)))

theorem stop_trace (C : ℕ) (template first second : Tape Bool) (pre suffix : List (Sym Bool)) (pos : Fin 4 → ℤ) :
    ∃ t ≤ 2,Trace C t (cfg .check (bank template ⟨pre,.stop::suffix⟩ first second) pos)
      (cfg (.done false) (bank template ⟨.stop::pre,suffix⟩ first second) (advance pos 1)) := by
  let z : NativeZipper.Config (Fin 4) (Label C) := ⟨⟨.check,bank template ⟨pre,.stop::suffix⟩ first second⟩,pos⟩
  let z' : NativeZipper.Config (Fin 4) (Label C) := ⟨⟨.done false,bank template ⟨.stop::pre,suffix⟩ first second⟩,advance pos 1⟩
  have hr : NativeZipper.run (program C) 2 z=z' := by
    simp only [z,z',NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,bank,
      Matrix.cons_val_one,Matrix.cons_val_zero,Tape.read,List.headD_cons,Microcode.Action.apply]
    congr 2
    · funext p;fin_cases p <;> rfl
    · funext p;fin_cases p <;> simp [Microcode.single,advance,NativeMicrocode.direction,Transpose.Dir.shift]
  exact NativeZipper.trace_of_run (program C) hr

noncomputable def nativeEncoding (C : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 4) (Label.check (C:=C))
noncomputable def nativeMachine (C : ℕ) := NativeMicrocode.machine (nativeEncoding C) (program C)

def labelEquiv (C : ℕ) : Label C ≃ Unit ⊕ (Bool × NativePaddedField.Label C) ⊕ Unit ⊕ Bool ⊕ Unit where
  toFun | .check => .inl () | .copy b pc => .inr (.inl (b,pc)) | .stop => .inr (.inr (.inl ()))
        | .done b => .inr (.inr (.inr (.inl b))) | .reject => .inr (.inr (.inr (.inr ())))
  invFun | .inl _ => .check | .inr (.inl (b,pc)) => .copy b pc | .inr (.inr (.inl _)) => .stop
         | .inr (.inr (.inr (.inl b))) => .done b | .inr (.inr (.inr (.inr _))) => .reject
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (⟨⟩|⟨b,pc⟩|⟨⟩|b|⟨⟩) <;> rfl

theorem fixed_resources (C : ℕ) : (nativeMachine C).k=4 ∧ (nativeMachine C).g+1=5 ∧ (nativeMachine C).q+1=2*C+113 ∧
    (nativeEncoding C).label .check=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label C)-1+1=_
  rw [Fintype.card_congr (labelEquiv C)]
  have hs := (NativePaddedField.fixed_resources C).2.2.1
  change Fintype.card (NativePaddedField.Label C)-1+1=C+54 at hs
  have hp : 0<Fintype.card (NativePaddedField.Label C) := Fintype.card_pos_iff.mpr ⟨.init (.erase 0)⟩
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_unit,Fintype.card_bool]
  omega

theorem native_pair (C : ℕ) (template first second : List Bool) (hp : 0<template.length)
    (hfirst : template.length=first.length) (hsecond : template.length=second.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 4 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 14*template.length+6*C+33,
      Transpose.stepN (nativeMachine C) input t
        ((cfg .check (bank (Counter.marked template) ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos).denote (nativeEncoding C) (program C) inputPos outRev)=
        some ((cfg (.done true) (bank (Counter.marked template) ⟨(symbols (first++second)).reverse++pre,suffix⟩
          (Counter.marked (NativePaddedField.padded C first)) (Counter.marked (NativePaddedField.padded C second)))
          (advance pos (2*template.length))).denote (nativeEncoding C) (program C) inputPos outRev) ∧
      Transpose.step (nativeMachine C) input ((cfg (.done true) (bank (Counter.marked template) ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked (NativePaddedField.padded C first)) (Counter.marked (NativePaddedField.padded C second)))
        (advance pos (2*template.length))).denote (nativeEncoding C) (program C) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := pair_trace C template first second hp hfirst hsecond pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding C) (program C) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C) (program C) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_stop (C : ℕ) (template first second : Tape Bool) (pre suffix : List (Sym Bool)) (pos : Fin 4 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2,
      Transpose.stepN (nativeMachine C) input t ((cfg .check (bank template ⟨pre,.stop::suffix⟩ first second) pos).denote
        (nativeEncoding C) (program C) inputPos outRev)=
        some ((cfg (.done false) (bank template ⟨.stop::pre,suffix⟩ first second) (advance pos 1)).denote
          (nativeEncoding C) (program C) inputPos outRev) ∧
      Transpose.step (nativeMachine C) input ((cfg (.done false) (bank template ⟨.stop::pre,suffix⟩ first second) (advance pos 1)).denote
        (nativeEncoding C) (program C) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := stop_trace C template first second pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding C) (program C) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding C) (program C) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

end TransposeFollowup.NativePairReader


/-! Prepare a field-width template from the preserved short dimension,
read one pair or a batch STOP, and physically erase the template. The
returned flag survives cleanup in finite control. No prepared template
is supplied to this controller. -/
namespace TransposeFollowup.PreparedPair
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def prepareBinding : FinitePortBinding (Fin 2) (Fin 5) where
  ports:=⟨![0,1],by decide +kernel⟩
  decode:=fun p => if p=0 then some 0 else if p=1 then some 1 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def readBinding : FinitePortBinding (Fin 4) (Fin 5) where
  ports:=⟨![1,2,3,4],by decide +kernel⟩
  decode:=fun p => if p=1 then some 0 else if p=2 then some 1 else if p=3 then some 2 else if p=4 then some 3 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel
def eraseBinding : FinitePortBinding (Fin 1) (Fin 5) where
  ports:=⟨fun _ => 1,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun p => if p=1 then some 0 else none
  decode_spec:=by intro p j;fin_cases p <;> fin_cases j <;> decide +kernel

inductive Label (small pad : ℕ)
  | prepare (pc : PaddedWord.Label small)
  | read (pc : NativePairReader.Label pad)
  | erase (pair : Bool) (pc : NativeErase.Label)
  | done (pair : Bool)
  deriving DecidableEq,Fintype

def program (small pad : ℕ) : Microcode.Program (Fin 5) (Label small pad)
  | .prepare (.seal .done) => .jump (.read .check)
  | .prepare pc => prepareBinding.instruction Label.prepare (PaddedWord.program small id pc)
  | .read (.done pair) => .jump (.erase pair 2)
  | .read pc => readBinding.instruction Label.read (NativePairReader.program pad pc)
  | .erase pair pc => if pc=0 then .jump (.done pair) else eraseBinding.instruction (Label.erase pair) (NativeErase.program pc)
  | .done _ => .halt

theorem prepare_code (small pad : ℕ) (pc : PaddedWord.Label small) (hh : PaddedWord.program small id pc≠.halt)
    (_ : PaddedWord.program small id pc≠.reject) :
    program small pad (.prepare pc)=MicrocodeEmbedding.instruction prepareBinding.ports Label.prepare (PaddedWord.program small id pc) := by
  cases pc with
  | «seal» pc =>
    cases pc with
    | done => exact False.elim (hh rfl)
    | _ => simp only [program,FinitePortBinding.instruction_eq]
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem read_code (small pad : ℕ) (pc : NativePairReader.Label pad) (hh : NativePairReader.program pad pc≠.halt)
    (_ : NativePairReader.program pad pc≠.reject) :
    program small pad (.read pc)=MicrocodeEmbedding.instruction readBinding.ports Label.read (NativePairReader.program pad pc) := by
  cases pc with
  | done _ => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem erase_code (small pad : ℕ) (pair : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program small pad (.erase pair pc)=MicrocodeEmbedding.instruction eraseBinding.ports (Label.erase pair) (NativeErase.program pc) := by
  have hp : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hp,ite_false,FinitePortBinding.instruction_eq]

abbrev Bank := Fin 5 → Tape Bool
def bank (source template input first second : Tape Bool) : Bank := ![source,template,input,first,second]
def cfg {small pad : ℕ} (pc : Label small pad) (s : Bank) (pos : Fin 5 → ℤ) : NativeMicrocode.Config (Fin 5) (Label small pad) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Fin 5 → ℤ) : MicrocodeEmbedding.Frame (Fin 5) := ⟨fun p => (s p).denote,pos⟩
def advance (pos : Fin 5 → ℤ) (m : ℕ) : Fin 5 → ℤ := fun p => pos p+if p=2 then (m : ℤ) else 0
abbrev Trace (small pad : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program small pad)) (NativeMicrocode.Active (program small pad))

theorem embed_prepare (small pad : ℕ) (pc : PaddedWord.Label small) (source template input first second : Tape Bool)
    (baseSource baseTemplate : Tape Bool) (pos : Fin 5 → ℤ) :
    MicrocodeEmbedding.embed prepareBinding.ports (Label.prepare (pad:=pad))
      (PaddedWord.cfg pc source template ![pos 0,pos 1]) (frame (bank baseSource baseTemplate input first second) pos)=
      cfg (.prepare pc) (bank source template input first second) pos := by
  unfold MicrocodeEmbedding.embed PaddedWord.cfg cfg frame
  simp only [← prepareBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem prepare_call (small pad : ℕ) (xs : List Bool) (input first second : Tape Bool) (pos : Fin 5 → ℤ) :
    ∃ t ≤ 12*xs.length+3*small+21,Trace small pad t
      (cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ input first second) pos)
      (cfg (.prepare (.seal .done)) (bank (Counter.marked xs) (Counter.marked (PaddedWord.word small id xs)) input first second) pos) := by
  obtain ⟨t,ht,htr⟩ := PaddedWord.padded_trace small id xs ![pos 0,pos 1]
  have he := MicrocodeEmbedding.trace_embed prepareBinding.ports (Label.prepare (pad:=pad)) (PaddedWord.program small id)
    (program small pad) (frame (bank (Counter.marked xs) ⟨[],[]⟩ input first second) pos) (prepare_code small pad) htr
  exact ⟨t,ht,by simpa only [embed_prepare] using he⟩

def liftRead (source : Tape Bool) (s : Fin 4 → Tape Bool) : Bank := ![source,s 0,s 1,s 2,s 3]

theorem liftRead_bank (source template input first second : Tape Bool) :
    liftRead source (NativePairReader.bank template input first second)=bank source template input first second := by
  funext p;fin_cases p <;> rfl

theorem embed_read (small pad : ℕ) (pc : NativePairReader.Label pad) (s base : Fin 4 → Tape Bool) (source : Tape Bool)
    (rpos : Fin 4 → ℤ) (pos : Fin 5 → ℤ) :
    MicrocodeEmbedding.embed readBinding.ports (Label.read (small:=small)) (NativePairReader.cfg pc s rpos)
      (frame (liftRead source base) pos)=cfg (.read pc) (liftRead source s) (readBinding.values rpos pos) := by
  unfold MicrocodeEmbedding.embed NativePairReader.cfg cfg frame
  simp only [← readBinding.values_eq_extend]
  congr 2
  funext p;fin_cases p <;> rfl

theorem read_positions (pos : Fin 5 → ℤ) : readBinding.values (fun p => pos (readBinding.ports p)) pos=pos := by
  funext p;fin_cases p <;> rfl

theorem read_final_positions (pos : Fin 5 → ℤ) (m : ℕ) :
    readBinding.values (NativePairReader.advance (fun p => pos (readBinding.ports p)) m) pos=advance pos m := by
  funext p;fin_cases p <;> simp [readBinding,FinitePortBinding.values,NativePairReader.advance,advance]

theorem pair_call (small pad : ℕ) (xs first second : List Bool) (hp : 0<(PaddedWord.word small id xs).length)
    (hf : (PaddedWord.word small id xs).length=first.length) (hs : (PaddedWord.word small id xs).length=second.length)
    (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) :
    ∃ t ≤ 14*(PaddedWord.word small id xs).length+6*pad+33,Trace small pad t
      (cfg (.read .check) (bank (Counter.marked xs) (Counter.marked (PaddedWord.word small id xs))
        ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.read (.done true)) (bank (Counter.marked xs) (Counter.marked (PaddedWord.word small id xs))
        ⟨(symbols (first++second)).reverse++pre,suffix⟩ (Counter.marked (NativePaddedField.padded pad first))
        (Counter.marked (NativePaddedField.padded pad second))) (advance pos (2*(PaddedWord.word small id xs).length))) := by
  let template:=PaddedWord.word small id xs
  obtain ⟨t,ht,htr⟩ := NativePairReader.pair_trace pad template first second hp hf hs pre suffix (fun p => pos (readBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small)) (NativePairReader.program pad) (program small pad)
    (frame (liftRead (Counter.marked xs) (NativePairReader.bank (Counter.marked template) ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)) pos)
    (read_code small pad) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank] using he⟩

theorem stop_call (small pad : ℕ) (xs : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) :
    ∃ t ≤ 2,Trace small pad t
      (cfg (.read .check) (bank (Counter.marked xs) (Counter.marked (PaddedWord.word small id xs)) ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.read (.done false)) (bank (Counter.marked xs) (Counter.marked (PaddedWord.word small id xs)) ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) (advance pos 1)) := by
  let template:=PaddedWord.word small id xs
  obtain ⟨t,ht,htr⟩ := NativePairReader.stop_trace pad (Counter.marked template) ⟨[],[]⟩ ⟨[],[]⟩ pre suffix (fun p => pos (readBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed readBinding.ports (Label.read (small:=small)) (NativePairReader.program pad) (program small pad)
    (frame (liftRead (Counter.marked xs) (NativePairReader.bank (Counter.marked template) ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)) pos)
    (read_code small pad) htr
  simp only [embed_read,read_positions,read_final_positions] at he
  exact ⟨t,ht,by simpa only [liftRead_bank] using he⟩

theorem embed_erase (small pad : ℕ) (pair : Bool) (pc : NativeErase.Label) (word : Tape Bool) (s : Bank) (pos : Fin 5 → ℤ) :
    MicrocodeEmbedding.embed eraseBinding.ports (Label.erase (small:=small) (pad:=pad) pair)
      (NativeErase.cfg pc word (fun _ => pos 1)).denote (frame s pos)=
      cfg (.erase pair pc) (Function.update s 1 word) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← eraseBinding.values_eq_extend]
  congr 2 <;> funext p <;> fin_cases p <;> rfl

theorem erase_call (small pad : ℕ) (pair : Bool) (xs : List Bool) (s : Bank) (hs : s 1=Counter.marked xs) (pos : Fin 5 → ℤ) :
    ∃ t ≤ 4*xs.length+4,Trace small pad t (cfg (.erase pair 2) s pos)
      (cfg (.erase pair 0) (Function.update s 1 ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace xs (fun _ => pos 1)
  have he := MicrocodeEmbedding.trace_embed eraseBinding.ports (Label.erase (small:=small) (pad:=pad) pair) NativeErase.program (program small pad)
    (frame s pos) (erase_code small pad pair) htr
  exact ⟨t,ht,by simpa only [embed_erase,← hs,Function.update_eq_self] using he⟩

theorem clear_template (source template input first second : Tape Bool) :
    Function.update (bank source template input first second) 1 ⟨[],[]⟩=bank source ⟨[],[]⟩ input first second := by
  funext p;fin_cases p <;> rfl

theorem jump_trace (small pad : ℕ) (pc next : Label small pad) (s : Bank) (pos : Fin 5 → ℤ)
    (h : program small pad pc=.jump next) : Trace small pad 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ h

end TransposeFollowup.PreparedPair


namespace TransposeFollowup.PreparedPair
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def pairBudget (small pad : ℕ) (xs : List Bool) := 48*xs.length+21*small+6*pad+61
def stopBudget (small : ℕ) (xs : List Bool) := 20*xs.length+7*small+30

theorem pair_trace (small pad : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) :
    ∃ t ≤ pairBudget small pad xs,Trace small pad t
      (cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.done true) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second)))
        (advance pos (2*(2*xs.length+small)))) := by
  let template:=PaddedWord.word small id xs
  let before : Tape Bool := ⟨pre,symbols (first++second)++suffix⟩
  let after : Tape Bool := ⟨(symbols (first++second)).reverse++pre,suffix⟩
  let A:=Counter.marked (NativePaddedField.padded pad first)
  let B:=Counter.marked (NativePaddedField.padded pad second)
  let adv:=advance pos (2*template.length)
  have hm : template.length=2*xs.length+small := PaddedWord.word_length small id xs
  obtain ⟨a,ha,ta⟩ := prepare_call small pad xs before ⟨[],[]⟩ ⟨[],[]⟩ pos
  have j1 := jump_trace small pad (.prepare (.seal .done)) (.read .check)
    (bank (Counter.marked xs) (Counter.marked template) before ⟨[],[]⟩ ⟨[],[]⟩) pos rfl
  obtain ⟨b,hb,tb⟩ := pair_call small pad xs first second (by rw [PaddedWord.word_length];exact hp)
    (by rw [PaddedWord.word_length,hf]) (by rw [PaddedWord.word_length,hs]) pre suffix pos
  have j2 := jump_trace small pad (.read (.done true)) (.erase true 2) (bank (Counter.marked xs) (Counter.marked template) after A B) adv rfl
  obtain ⟨c,hc,tc⟩ := erase_call small pad true template (bank (Counter.marked xs) (Counter.marked template) after A B) rfl adv
  rw [clear_template] at tc
  have j3 := jump_trace small pad (.erase true 0) (.done true) (bank (Counter.marked xs) ⟨[],[]⟩ after A B) adv rfl
  have ht := NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc) j3
  refine ⟨a+1+b+1+c+1,?_,?_⟩
  · dsimp only [pairBudget]
    rw [PaddedWord.word_length] at hb
    rw [hm] at hc
    omega
  · simpa only [adv,hm] using ht

theorem stop_trace (small pad : ℕ) (xs : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) :
    ∃ t ≤ stopBudget small xs,Trace small pad t
      (cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
      (cfg (.done false) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) (advance pos 1)) := by
  let template:=PaddedWord.word small id xs
  let before : Tape Bool := ⟨pre,.stop::suffix⟩
  let after : Tape Bool := ⟨.stop::pre,suffix⟩
  let adv:=advance pos 1
  obtain ⟨a,ha,ta⟩ := prepare_call small pad xs before ⟨[],[]⟩ ⟨[],[]⟩ pos
  have j1 := jump_trace small pad (.prepare (.seal .done)) (.read .check)
    (bank (Counter.marked xs) (Counter.marked template) before ⟨[],[]⟩ ⟨[],[]⟩) pos rfl
  obtain ⟨b,hb,tb⟩ := stop_call small pad xs pre suffix pos
  have j2 := jump_trace small pad (.read (.done false)) (.erase false 2)
    (bank (Counter.marked xs) (Counter.marked template) after ⟨[],[]⟩ ⟨[],[]⟩) adv rfl
  obtain ⟨c,hc,tc⟩ := erase_call small pad false template
    (bank (Counter.marked xs) (Counter.marked template) after ⟨[],[]⟩ ⟨[],[]⟩) rfl adv
  rw [clear_template] at tc
  have j3 := jump_trace small pad (.erase false 0) (.done false) (bank (Counter.marked xs) ⟨[],[]⟩ after ⟨[],[]⟩ ⟨[],[]⟩) adv rfl
  refine ⟨a+1+b+1+c+1,?_,NativeCountedLoop.trace_trans
    (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta j1) tb) j2) tc) j3⟩
  dsimp only [stopBudget]
  rw [show template.length=2*xs.length+small from PaddedWord.word_length small id xs] at hc
  omega

noncomputable def nativeEncoding (small pad : ℕ) := NativeMicrocode.initialEncoding (T:=Fin 5) (Label.prepare (pad:=pad) (PaddedWord.Label.init (C:=small) (.erase 0)))
noncomputable def nativeMachine (small pad : ℕ) := NativeMicrocode.machine (nativeEncoding small pad) (program small pad)

def labelEquiv (small pad : ℕ) : Label small pad ≃ PaddedWord.Label small ⊕ NativePairReader.Label pad ⊕ (Bool × NativeErase.Label) ⊕ Bool where
  toFun | .prepare pc => .inl pc | .read pc => .inr (.inl pc) | .erase b pc => .inr (.inr (.inl (b,pc))) | .done b => .inr (.inr (.inr b))
  invFun | .inl pc => .prepare pc | .inr (.inl pc) => .read pc | .inr (.inr (.inl (b,pc))) => .erase b pc | .inr (.inr (.inr b)) => .done b
  left_inv:=by intro pc;cases pc <;> rfl
  right_inv:=by rintro (pc|pc|⟨b,pc⟩|b) <;> rfl

theorem fixed_resources (small pad : ℕ) : (nativeMachine small pad).k=5 ∧ (nativeMachine small pad).g+1=5 ∧
    (nativeMachine small pad).q+1=small+2*pad+164 ∧ (nativeEncoding small pad).label (.prepare (.init (.erase 0)))=0 := by
  refine ⟨rfl,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Label small pad)-1+1=_
  rw [Fintype.card_congr (labelEquiv small pad)]
  have hs := (NativePairReader.fixed_resources pad).2.2.1
  change Fintype.card (NativePairReader.Label pad)-1+1=2*pad+113 at hs
  have hp : 0<Fintype.card (NativePairReader.Label pad) := Fintype.card_pos_iff.mpr ⟨.check⟩
  have he : Fintype.card NativeErase.Label=8 := by decide +kernel
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,PaddedWord.label_card,he]
  omega

theorem native_pair (small pad : ℕ) (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ pairBudget small pad xs,
      Transpose.stepN (nativeMachine small pad) input t
        ((cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev)=
        some ((cfg (.done true) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
          (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second)))
          (advance pos (2*(2*xs.length+small)))).denote (nativeEncoding small pad) (program small pad) inputPos outRev) ∧
      Transpose.step (nativeMachine small pad) input ((cfg (.done true) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
        (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second)))
        (advance pos (2*(2*xs.length+small)))).denote (nativeEncoding small pad) (program small pad) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := pair_trace small pad xs first second hp hf hs pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small pad) (program small pad) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small pad) (program small pad) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_stop (small pad : ℕ) (xs : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ stopBudget small xs,
      Transpose.stepN (nativeMachine small pad) input t
        ((cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev)=
        some ((cfg (.done false) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) (advance pos 1)).denote
          (nativeEncoding small pad) (program small pad) inputPos outRev) ∧
      Transpose.step (nativeMachine small pad) input ((cfg (.done false) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩)
        (advance pos 1)).denote (nativeEncoding small pad) (program small pad) inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := stop_trace small pad xs pre suffix pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN (nativeEncoding small pad) (program small pad) input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff (nativeEncoding small pad) (program small pad) input inputPos outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

end TransposeFollowup.PreparedPair


/-! Framed calls and the common-width contract. The finite constants are
chosen by the map family; the runtime dimension is still read from tape. -/
namespace TransposeFollowup.PreparedPair
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem common_words (small large : ℕ) (h : small≤large) (xs first second : List Bool)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small) :
    (NativePaddedField.padded (large-small) first).length=2*xs.length+large ∧
    (NativePaddedField.padded (large-small) second).length=2*xs.length+large ∧
    Counter.value (NativePaddedField.padded (large-small) first)=Counter.value first ∧
    Counter.value (NativePaddedField.padded (large-small) second)=Counter.value second := by
  obtain ⟨ha,hva⟩ := NativePaddedField.common_width xs.length small large h first hf
  obtain ⟨hb,hvb⟩ := NativePaddedField.common_width xs.length small large h second hs
  exact ⟨ha,hb,hva,hvb⟩

theorem pair_uniform_budget (small large : ℕ) (h : small≤large) (xs : List Bool) :
    pairBudget small (large-small) xs ≤ 48*xs.length+21*large+61 := by
  unfold pairBudget
  omega

theorem stop_uniform_budget (small large : ℕ) (h : small≤large) (xs : List Bool) :
    stopBudget small xs ≤ 48*xs.length+21*large+61 := by
  unfold stopBudget
  omega

theorem native_pair_call {U J : Type*} {k q : ℕ} (small pad : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 5 ↪ U) (labels : Label small pad → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small pad pc≠.halt → program small pad pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small pad pc))
    (xs first second : List Bool) (hp : 0<2*xs.length+small)
    (hf : first.length=2*xs.length+small) (hs : second.length=2*xs.length+small)
    (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ pairBudget small pad xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩
            ⟨pre,symbols (first++second)++suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos) outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done true) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨(symbols (first++second)).reverse++pre,suffix⟩
            (Counter.marked (NativePaddedField.padded pad first)) (Counter.marked (NativePaddedField.padded pad second)))
            (advance pos (2*(2*xs.length+small)))) outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := pair_trace small pad xs first second hp hf hs pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small pad) target outerFrame input inputPos outRev hc htr⟩

theorem native_stop_call {U J : Type*} {k q : ℕ} (small pad : ℕ) (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Fin 5 ↪ U) (labels : Label small pad → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program small pad pc≠.halt → program small pad pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program small pad pc))
    (xs : List Bool) (pre suffix : List (Sym Bool)) (pos : Fin 5 → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ stopBudget small xs,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels
          (cfg (.prepare (.init (.erase 0))) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨pre,.stop::suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) pos)
          outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg (.done false) (bank (Counter.marked xs) ⟨[],[]⟩ ⟨.stop::pre,suffix⟩ ⟨[],[]⟩ ⟨[],[]⟩) (advance pos 1))
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := stop_trace small pad xs pre suffix pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels (program small pad) target outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.PreparedPair
