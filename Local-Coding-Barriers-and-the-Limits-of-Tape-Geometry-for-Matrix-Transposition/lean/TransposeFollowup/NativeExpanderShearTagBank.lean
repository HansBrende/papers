import TransposeFollowup.NativeMatchingXorTagStream
import TransposeFollowup.NativeClosedStream
import TransposeFollowup.PortBindingFrame

/-! Expand each of a fixed finite bank of row masks using one restored unary
clock. The controller initializes and seals every tag tape and restores every
mask head; no row count or width is supplied in finite control. -/
namespace TransposeFollowup.NativeExpanderShearTagPage
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def singleBinding (p : Fin 3) : FinitePortBinding (Fin 1) (Fin 3) where
  ports := ⟨fun _ => p, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun q => if q=p then some 0 else none
  decode_spec := by
    intro q i
    change (if q=p then some (0 : Fin 1) else none)=some i ↔ p=q
    fin_cases i
    simp [eq_comm]

def identityBinding : FinitePortBinding (Fin 3) (Fin 3) where
  ports := Function.Embedding.refl _
  decode := some
  decode_spec := by intro p i; simp [eq_comm]

inductive Label
  | init (pc : NativeBuffer.Label)
  | expand (pc : NativeMatchingXorTagStream.Label)
  | seal (pc : NativeSealBack.Label)
  | rewind (pc : NativeSealBack.Label)
  | done
  deriving DecidableEq, Fintype

def start : Label := .init (.erase 0)
def program : Microcode.Program (Fin 3) Label
  | .init .done => .jump (.expand .scan)
  | .init pc => (singleBinding 2).instruction Label.init (NativeBuffer.program pc)
  | .expand .done => .jump (.seal .seal)
  | .expand pc => identityBinding.instruction Label.expand (NativeMatchingXorTagStream.program pc)
  | .seal .done => .jump (.rewind .back)
  | .seal pc => (singleBinding 2).instruction Label.seal (NativeSealBack.program pc)
  | .rewind .done => .jump .done
  | .rewind pc => (singleBinding 0).instruction Label.rewind (NativeSealBack.program pc)
  | .done => .halt

theorem init_code (pc : NativeBuffer.Label) (hh : NativeBuffer.program pc ≠ .halt)
    (_ : NativeBuffer.program pc ≠ .reject) :
    program (.init pc)=MicrocodeEmbedding.instruction (singleBinding 2).ports Label.init
      (NativeBuffer.program pc) := by
  cases pc <;> simp_all [program,NativeBuffer.program,FinitePortBinding.instruction_eq]

theorem expand_code (pc : NativeMatchingXorTagStream.Label)
    (hh : NativeMatchingXorTagStream.program pc ≠ .halt)
    (_ : NativeMatchingXorTagStream.program pc ≠ .reject) :
    program (.expand pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.expand
      (NativeMatchingXorTagStream.program pc) := by
  cases pc <;> simp_all [program,NativeMatchingXorTagStream.program,FinitePortBinding.instruction_eq]

theorem seal_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc ≠ .halt)
    (_ : NativeSealBack.program pc ≠ .reject) :
    program (.seal pc)=MicrocodeEmbedding.instruction (singleBinding 2).ports Label.seal
      (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

theorem rewind_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc ≠ .halt)
    (_ : NativeSealBack.program pc ≠ .reject) :
    program (.rewind pc)=MicrocodeEmbedding.instruction (singleBinding 0).ports Label.rewind
      (NativeSealBack.program pc) := by
  cases pc <;> simp_all [program,NativeSealBack.program,FinitePortBinding.instruction_eq]

def bank (flags clock out : Tape Bool) : Fin 3 → Tape Bool := ![flags,clock,out]
def cfg (pc : Label) (flags clock out : Tape Bool) (pos : Fin 3 → ℤ) : NativeMicrocode.Config (Fin 3) Label :=
  ⟨⟨pc,fun p => (bank flags clock out p).denote⟩,pos⟩
def frame (flags clock out : Tape Bool) (pos : Fin 3 → ℤ) : MicrocodeEmbedding.Frame (Fin 3) :=
  ⟨fun p => (bank flags clock out p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

/-- All three interfaces retain absolute head coordinates. -/
theorem embed_single (p : Fin 3) (labels : NativeSealBack.Label → Label)
    (pc : NativeSealBack.Label) (w flags clock out : Tape Bool) (pos : Fin 3 → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding p).ports labels
      (NativeSealBack.cfg pc w (fun _ => z)).denote (frame flags clock out pos)=
    ⟨⟨labels pc,fun q => ((Function.update (bank flags clock out) p w) q).denote⟩,
      Function.update pos p z⟩ := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus frame
  simp only [←(singleBinding p).values_eq_extend]
  congr 2 <;> funext q <;> by_cases h : q=p <;>
    simp [singleBinding,FinitePortBinding.values,Function.update,h]

theorem jump_trace (pc next : Label) (flags clock out : Tape Bool) (pos : Fin 3 → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc flags clock out pos) (cfg next flags clock out pos) :=
  NativeMicrocode.jump_trace _ _ _ h

theorem init_call (flags clock : Tape Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2, Trace t (cfg start flags clock ⟨[],[]⟩ pos)
      (cfg (.init .done) flags clock (NativeSealBack.openWord []) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBuffer.initialize_trace (fun _ => pos 2)
  have he := MicrocodeEmbedding.trace_embed (singleBinding 2).ports Label.init
    NativeBuffer.program program (frame flags clock ⟨[],[]⟩ pos) init_code htr
  have hi : MicrocodeEmbedding.embed (singleBinding 2).ports Label.init
      (NativeBuffer.cfg (.erase 0) ⟨[],[]⟩ (fun _ => pos 2)).denote
      (frame flags clock ⟨[],[]⟩ pos)=cfg start flags clock ⟨[],[]⟩ pos := by
    unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [←(singleBinding 2).values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  have hf : MicrocodeEmbedding.embed (singleBinding 2).ports Label.init
      (NativeBuffer.cfg .done BinaryCarry.preparedOutput (fun _ => pos 2)).denote
      (frame flags clock ⟨[],[]⟩ pos)=cfg (.init .done) flags clock (NativeSealBack.openWord []) pos := by
    unfold MicrocodeEmbedding.embed NativeBuffer.cfg NativeZipper.Config.denote Microcode.Config.denote
      Microcode.focus frame cfg
    simp only [←(singleBinding 2).values_eq_extend]
    congr 2 <;> funext p <;> fin_cases p <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using he⟩

abbrev expanded := NativeMatchingXorTagStream.expanded
abbrev advanced := NativeMatchingXorTagStream.advance

theorem embed_expand (pc : NativeMatchingXorTagStream.Label) (flags clock out : Tape Bool)
    (pos : Fin 3 → ℤ) (base : MicrocodeEmbedding.Frame (Fin 3)) :
    MicrocodeEmbedding.embed identityBinding.ports Label.expand
      (NativeMatchingXorTagStream.cfg pc flags clock out pos).denote base=
      cfg (.expand pc) flags clock out pos := by
  unfold MicrocodeEmbedding.embed NativeMatchingXorTagStream.cfg NativeZipper.Config.denote
    Microcode.Config.denote cfg
  simp only [←identityBinding.values_eq_extend]
  rfl

theorem expand_call (flags clock : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ flags.length*(4*clock.length+7)+1, Trace t
      (cfg (.expand .scan) (Counter.marked flags) (Counter.marked clock) (NativeSealBack.openWord []) pos)
      (cfg (.expand .done) (RowStream.closedTape flags) (Counter.marked clock)
        (NativeSealBack.openWord (expanded clock.length flags))
        (advanced pos flags.length (flags.length*clock.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorTagStream.complete_trace flags clock [] [.start] [] pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports Label.expand
    NativeMatchingXorTagStream.program program
    (frame (Counter.marked flags) (Counter.marked clock) (NativeSealBack.openWord []) pos) expand_code htr
  refine ⟨t,ht,?_⟩
  simpa only [embed_expand,List.nil_append,Counter.marked,RowStream.closedTape,symbols,
    List.append_nil,List.map_reverse] using he

theorem seal_call (flags clock out : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*out.length+5, Trace t
      (cfg (.seal .seal) (RowStream.closedTape flags) (Counter.marked clock)
        (NativeSealBack.openWord out) (advanced pos flags.length out.length))
      (cfg (.seal .done) (RowStream.closedTape flags) (Counter.marked clock)
        (Counter.marked out) (advanced pos flags.length 0)) := by
  obtain ⟨t,ht,htr⟩ := NativeSealBack.seal_trace out (fun _ => (advanced pos flags.length out.length) 2)
  have he := MicrocodeEmbedding.trace_embed (singleBinding 2).ports Label.seal
    NativeSealBack.program program
    (frame (RowStream.closedTape flags) (Counter.marked clock) (NativeSealBack.openWord out)
      (advanced pos flags.length out.length)) seal_code htr
  rw [embed_single,embed_single] at he
  have hi : Function.update (bank (RowStream.closedTape flags) (Counter.marked clock)
      (NativeSealBack.openWord out)) 2 (NativeSealBack.openWord out)=
      bank (RowStream.closedTape flags) (Counter.marked clock) (NativeSealBack.openWord out) := by
    funext p; fin_cases p <;> rfl
  have hf : Function.update (bank (RowStream.closedTape flags) (Counter.marked clock)
      (NativeSealBack.openWord out)) 2 (Counter.marked out)=
      bank (RowStream.closedTape flags) (Counter.marked clock) (Counter.marked out) := by
    funext p; fin_cases p <;> rfl
  have hpi := Function.update_eq_self 2 (advanced pos flags.length out.length)
  have hpf : Function.update (advanced pos flags.length out.length) 2
      ((advanced pos flags.length out.length) 2-out.length)=advanced pos flags.length 0 := by
    funext p; fin_cases p <;> simp [advanced,NativeMatchingXorTagStream.advance]
  exact ⟨t,ht,by simpa only [hi,hf,hpi,hpf,cfg] using he⟩

theorem rewind_call (flags clock out : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 2*flags.length+4, Trace t
      (cfg (.rewind .back) (RowStream.closedTape flags) (Counter.marked clock)
        (Counter.marked out) (advanced pos flags.length 0))
      (cfg (.rewind .done) (Counter.marked flags) (Counter.marked clock) (Counter.marked out) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace flags
    (fun _ => (advanced pos flags.length 0) 0)
  have he := MicrocodeEmbedding.trace_embed (singleBinding 0).ports Label.rewind
    NativeSealBack.program program
    (frame (RowStream.closedTape flags) (Counter.marked clock) (Counter.marked out)
      (advanced pos flags.length 0)) rewind_code htr
  rw [embed_single,embed_single] at he
  have hi : Function.update (bank (RowStream.closedTape flags) (Counter.marked clock)
      (Counter.marked out)) 0 (RowStream.closedTape flags)=
      bank (RowStream.closedTape flags) (Counter.marked clock) (Counter.marked out) := by
    funext p; fin_cases p <;> rfl
  have hf : Function.update (bank (RowStream.closedTape flags) (Counter.marked clock)
      (Counter.marked out)) 0 (Counter.marked flags)=
      bank (Counter.marked flags) (Counter.marked clock) (Counter.marked out) := by
    funext p; fin_cases p <;> rfl
  have hpi := Function.update_eq_self 0 (advanced pos flags.length 0)
  have hpf : Function.update (advanced pos flags.length 0) 0
      ((advanced pos flags.length 0) 0-flags.length)=pos := by
    funext p; fin_cases p <;> simp [advanced,NativeMatchingXorTagStream.advance]
  exact ⟨t,ht,by simpa only [hi,hf,hpi,hpf,cfg] using he⟩

theorem complete_trace (flags clock : List Bool) (pos : Fin 3 → ℤ) :
    ∃ t ≤ 6*flags.length*clock.length+9*flags.length+16, Trace t
      (cfg start (Counter.marked flags) (Counter.marked clock) ⟨[],[]⟩ pos)
      (cfg .done (Counter.marked flags) (Counter.marked clock)
        (Counter.marked (expanded clock.length flags)) pos) := by
  obtain ⟨a,ha,ta⟩ := init_call (Counter.marked flags) (Counter.marked clock) pos
  have ja := jump_trace (.init .done) (.expand .scan) (Counter.marked flags) (Counter.marked clock)
    (NativeSealBack.openWord []) pos rfl
  obtain ⟨b,hb,tb⟩ := expand_call flags clock pos
  have hj : flags.length*clock.length=(expanded clock.length flags).length :=
    (NativeMatchingXorTagStream.expanded_length clock.length flags).symm
  rw [hj] at tb
  have jb := jump_trace (.expand .done) (.seal .seal) (RowStream.closedTape flags) (Counter.marked clock)
    (NativeSealBack.openWord (expanded clock.length flags))
    (advanced pos flags.length (expanded clock.length flags).length) rfl
  obtain ⟨c,hc,tc⟩ := seal_call flags clock (expanded clock.length flags) pos
  have jc := jump_trace (.seal .done) (.rewind .back) (RowStream.closedTape flags) (Counter.marked clock)
    (Counter.marked (expanded clock.length flags)) (advanced pos flags.length 0) rfl
  obtain ⟨e,he,te⟩ := rewind_call flags clock (expanded clock.length flags) pos
  have je := jump_trace (.rewind .done) .done (Counter.marked flags) (Counter.marked clock)
    (Counter.marked (expanded clock.length flags)) pos rfl
  refine ⟨_,?_,trace_trans ta (trace_trans ja (trace_trans tb (trace_trans jb
    (trace_trans tc (trace_trans jc (trace_trans te je))))))⟩
  rw [NativeMatchingXorTagStream.expanded_length] at hc
  nlinarith

end TransposeFollowup.NativeExpanderShearTagPage

namespace TransposeFollowup.NativeExpanderShearTagBank
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

inductive Port (q : ℕ) | mask (j : Fin q) | tag (j : Fin q) | clock
  deriving DecidableEq, Fintype

abbrev Bank (q : ℕ) := Port q → Tape Bool

def binding {q : ℕ} (j : Fin q) : FinitePortBinding (Fin 3) (Port q) where
  ports := ⟨![.mask j,.clock,.tag j],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  decode := fun p => match p with
    | .mask i => if i=j then some 0 else none
    | .clock => some 1
    | .tag i => if i=j then some 2 else none
  decode_spec := by
    intro p t
    change _ ↔ (![.mask j,.clock,.tag j] : Fin 3 → Port q) t = p
    cases p <;> fin_cases t <;> simp [eq_comm]

inductive Label (q : ℕ) | page (j : Fin q) (pc : NativeExpanderShearTagPage.Label) | done
  deriving DecidableEq, Fintype

def entry (q k : ℕ) : Label q := if h : k<q then .page ⟨k,h⟩ NativeExpanderShearTagPage.start else .done

def program (q : ℕ) : Microcode.Program (Port q) (Label q)
  | .page j .done => .jump (entry q (j.val+1))
  | .page j pc => (binding j).instruction (Label.page j) (NativeExpanderShearTagPage.program pc)
  | .done => .halt

theorem page_code {q : ℕ} (j : Fin q) (pc : NativeExpanderShearTagPage.Label)
    (hh : NativeExpanderShearTagPage.program pc ≠ .halt)
    (_ : NativeExpanderShearTagPage.program pc ≠ .reject) :
    program q (.page j pc)=MicrocodeEmbedding.instruction (binding j).ports (Label.page j)
      (NativeExpanderShearTagPage.program pc) := by
  cases pc <;> simp_all [program,NativeExpanderShearTagPage.program,FinitePortBinding.instruction_eq]

def stage {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) (k : ℕ) : Bank q
  | .mask j => Counter.marked (flags j)
  | .clock => Counter.marked clock
  | .tag j => if j.val<k then Counter.marked (NativeMatchingXorTagStream.expanded clock.length (flags j))
      else ⟨[],[]⟩

abbrev initial {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) := stage flags clock 0
abbrev final {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) := stage flags clock q

def cfg {q : ℕ} (pc : Label q) (s : Bank q) (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) (Label q) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame {q : ℕ} (s : Bank q) (pos : Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) :=
  ⟨fun p => (s p).denote,pos⟩
abbrev Trace (q : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program q)) (NativeMicrocode.Active (program q))
noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (entry q 0)
noncomputable def nativeMachine (q : ℕ) := NativeMicrocode.machine (nativeEncoding q) (program q)

theorem embed_page {q : ℕ} (j : Fin q) (pc : NativeExpanderShearTagPage.Label)
    (a b c : Tape Bool) (s : Bank q) (pos : Port q → ℤ) :
    MicrocodeEmbedding.embed (binding j).ports (Label.page j)
      (NativeExpanderShearTagPage.cfg pc a b c (fun p => pos ((binding j).ports p)))
      (frame s pos)=cfg (.page j pc) ((binding j).values (NativeExpanderShearTagPage.bank a b c) s) pos := by
  exact (binding j).embed_bank_project _ _ _ _ _

theorem page_call {q : ℕ} (j : Fin q) (flags : Fin q → List Bool) (clock : List Bool)
    (pos : Port q → ℤ) :
    ∃ t ≤ 6*(flags j).length*clock.length+9*(flags j).length+16, Trace q t
      (cfg (.page j NativeExpanderShearTagPage.start) (stage flags clock j.val) pos)
      (cfg (.page j .done) (stage flags clock (j.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeExpanderShearTagPage.complete_trace (flags j) clock
    (fun p => pos ((binding j).ports p))
  have he := MicrocodeEmbedding.trace_embed (binding j).ports (Label.page j)
    NativeExpanderShearTagPage.program (program q) (frame (stage flags clock j.val) pos)
    (page_code j) htr
  rw [embed_page,embed_page] at he
  have hi : (binding j).values (NativeExpanderShearTagPage.bank (Counter.marked (flags j))
      (Counter.marked clock) ⟨[],[]⟩) (stage flags clock j.val)=stage flags clock j.val := by
    funext p
    cases p with
    | clock => rfl
    | mask i => by_cases h : i=j <;> simp [FinitePortBinding.values,binding,NativeExpanderShearTagPage.bank,stage,h]
    | tag i => by_cases h : i=j <;> simp [FinitePortBinding.values,binding,NativeExpanderShearTagPage.bank,stage,h]
  have hf : (binding j).values (NativeExpanderShearTagPage.bank (Counter.marked (flags j))
      (Counter.marked clock) (Counter.marked (NativeExpanderShearTagPage.expanded clock.length (flags j))))
      (stage flags clock j.val)=stage flags clock (j.val+1) := by
    funext p
    cases p with
    | clock => rfl
    | mask i => by_cases h : i=j <;> simp [FinitePortBinding.values,binding,NativeExpanderShearTagPage.bank,stage,h]
    | tag i =>
      by_cases h : i=j
      · subst i
        simp [FinitePortBinding.values,binding,NativeExpanderShearTagPage.bank,stage,NativeExpanderShearTagPage.expanded]
      · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
        have he : i.val<j.val+1 ↔ i.val<j.val := by omega
        simp [FinitePortBinding.values,binding,stage,h,he]
  exact ⟨t,ht,by simpa only [hi,hf] using he⟩

theorem complete_from {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool)
    (m : ℕ) (hlen : ∀ j,(flags j).length=m) (pos : Port q → ℤ)
    (k : ℕ) (hk : k ≤ q) :
    ∃ t ≤ (q-k)*(6*m*clock.length+9*m+17), Trace q t
      (cfg (entry q k) (stage flags clock k) pos) (cfg .done (final flags clock) pos) := by
  induction h : q-k generalizing k with
  | zero =>
    have he : k=q := by omega
    subst k
    refine ⟨0,by simp,?_⟩
    simp only [entry,lt_self_iff_false,↓reduceDIte]
    exact .refl _
  | succ d ih =>
    have hlt : k<q := by omega
    let j : Fin q := ⟨k,hlt⟩
    obtain ⟨a,ha,ta⟩ := page_call j flags clock pos
    have tj : Trace q 1 (cfg (.page j .done) (stage flags clock (k+1)) pos)
        (cfg (entry q (k+1)) (stage flags clock (k+1)) pos) :=
      NativeMicrocode.jump_trace _ _ _ rfl
    obtain ⟨b,hb,tb⟩ := ih (k+1) (by omega) (by omega)
    refine ⟨a+1+b,?_,?_⟩
    · rw [hlen j] at ha
      nlinarith
    · have he : entry q k=.page j NativeExpanderShearTagPage.start := by simp [entry,hlt,j]
      rw [he]
      exact trace_trans (trace_trans ta tj) tb

theorem complete_trace {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool)
    (m : ℕ) (hlen : ∀ j,(flags j).length=m) (pos : Port q → ℤ) :
    ∃ t ≤ q*(6*m*clock.length+9*m+17), Trace q t
      (cfg (entry q 0) (initial flags clock) pos) (cfg .done (final flags clock) pos) := by
  simpa only [Nat.sub_zero] using complete_from flags clock m hlen pos 0 (Nat.zero_le q)

theorem native_call {q : ℕ} {U J : Type*} {k t : ℕ}
    (encoding : NativeMicrocode.Encoding U J k t) (ports : Port q ↪ U) (labels : Label q → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program q pc≠.halt → program q pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program q pc))
    (flags : Fin q → List Bool) (clock : List Bool) (m : ℕ)
    (hlen : ∀ j,(flags j).length=m) (pos : Port q → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ steps ≤ q*(6*m*clock.length+9*m+17),
      Transpose.stepN (NativeMicrocode.machine encoding target) input steps
        ((MicrocodeEmbedding.embed ports labels (cfg (entry q 0) (initial flags clock) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final flags clock) pos) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨steps,ht,htr⟩ := complete_trace flags clock m hlen pos
  exact ⟨steps,ht,MicrocodeEmbedding.native_call encoding ports labels (program q) target
    outerFrame input inputPos outRev hc htr⟩

@[simp] theorem final_mask {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) (j : Fin q) :
    final flags clock (.mask j)=Counter.marked (flags j) := rfl
@[simp] theorem final_clock {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) :
    final flags clock .clock=Counter.marked clock := rfl
@[simp] theorem final_tag {q : ℕ} (flags : Fin q → List Bool) (clock : List Bool) (j : Fin q) :
    final flags clock (.tag j)=Counter.marked (NativeMatchingXorTagStream.expanded clock.length (flags j)) := by
  simp [final,stage,j.isLt]

private def portEquiv (q : ℕ) : Port q ≃ ((Fin q ⊕ Fin q) ⊕ Unit) where
  toFun := fun p => match p with
    | .mask j => .inl (.inl j) | .tag j => .inl (.inr j) | .clock => .inr ()
  invFun := fun p => match p with
    | .inl (.inl j) => .mask j | .inl (.inr j) => .tag j | .inr _ => .clock
  left_inv := by intro p; cases p <;> rfl
  right_inv := by
    intro p
    rcases p with (j | j) | u
    · rfl
    · rfl
    · cases u; rfl

theorem fixed_resources (q : ℕ) : (nativeMachine q).k=2*q+1 ∧ (nativeMachine q).g+1=5 ∧
    (nativeEncoding q).label (entry q 0)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Port q)=2*q+1
  rw [Fintype.card_congr (portEquiv q)]
  simp [two_mul]

end TransposeFollowup.NativeExpanderShearTagBank
