import TransposeFollowup.PortBindingFrame
import TransposeFollowup.InPlaceAdd
import TransposeFollowup.SeedMultipleMeaning
import TransposeFollowup.NativeErase
import TransposeFollowup.DimensionCandidateSearch
import TransposeFollowup.NativeTrimRun
import TransposeFollowup.NativeBatchErase
import TransposeFollowup.NativeUnprepare

/-! Nine fixed tapes implement one candidate increment. Four additions update
k^2 and k; a comparison triggers the entry-width/threshold update. Copying,
erasure and every transfer to the next call are native instructions. -/
namespace TransposeFollowup.DimensionAdvance
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | candidate | square | bits | threshold | unit | zero | fuel | scratch | copyThreshold
  deriving DecidableEq

instance : Fintype Port where
  elems := {.candidate,.square,.bits,.threshold,.unit,.zero,.fuel,.scratch,.copyThreshold}
  complete := by intro p;cases p <;> simp

abbrev Bank := Port → Tape Bool

def accPort : Fin 6 → Port := ![.square,.square,.square,.candidate,.bits,.threshold]
def factorPort : Fin 6 → Port := ![.candidate,.candidate,.unit,.unit,.unit,.copyThreshold]
def addPort (i : Fin 6) : RepeatedAdd.Port → Port
  | .acc => accPort i | .factor => factorPort i | .fuel => .fuel | .scratch => .scratch | .zero => .zero

def addBinding (i : Fin 6) : FinitePortBinding RepeatedAdd.Port Port where
  ports:=⟨addPort i,by fin_cases i <;> decide +kernel⟩
  decode:=fun p => if p=accPort i then some .acc else if p=factorPort i then some .factor else
    match p with | .fuel => some .fuel | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec:=by intro p q;fin_cases i <;> cases p <;> cases q <;> decide +kernel

def compareBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![.candidate,.threshold],by decide +kernel⟩
  decode:=fun p => match p with | .candidate => some 0 | .threshold => some 1 | _ => none
  decode_spec:=by intro p i;cases p <;> fin_cases i <;> decide +kernel

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![.threshold,.copyThreshold],by decide +kernel⟩
  decode:=fun p => match p with | .threshold => some 0 | .copyThreshold => some 1 | _ => none
  decode_spec:=by intro p i;cases p <;> fin_cases i <;> decide +kernel

def eraseBinding : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => .copyThreshold,by intro _ _ _;exact Subsingleton.elim _ _⟩
  decode:=fun p => if p=.copyThreshold then some 0 else none
  decode_spec:=by intro p i;cases p <;> fin_cases i <;> decide +kernel

inductive Label
  | add (i : Fin 6) (pc : RepeatedAdd.Label)
  | compare (pc : BinaryCompare.Label)
  | copy (pc : NativeMappedCopy.Label)
  | erase (pc : NativeErase.Label)
  | done
  deriving DecidableEq,Fintype

def start : Label := .add 0 (.counter 0)
def afterAdd : Fin 6 → Label := ![.add 1 (.counter 0),.add 2 (.counter 0),.add 3 (.counter 0),
  .compare (.scan .equal),.copy (.init (.erase 0)),.erase 2]
def program : Microcode.Program Port Label
  | .add i pc => if pc=.counter 12 then .jump (afterAdd i)
      else (addBinding i).instruction (Label.add i) (RepeatedAdd.program pc)
  | .compare (.done .greater) => .jump (.add 4 (.counter 0))
  | .compare (.done _) => .jump .done
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .copy pc => if pc=.seal .done then .jump (.add 5 (.counter 0))
      else copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .erase pc => if pc=0 then .jump .done else eraseBinding.instruction Label.erase (NativeErase.program pc)
  | .done => .halt

theorem add_code (i : Fin 6) (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt)
    (_ : RepeatedAdd.program pc≠.reject) :
    program (.add i pc)=MicrocodeEmbedding.instruction (addBinding i).ports (Label.add i) (RepeatedAdd.program pc) := by
  have hn : pc≠.counter 12 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem compare_code (pc : BinaryCompare.Label) (hh : BinaryCompare.program pc≠.halt)
    (_ : BinaryCompare.program pc≠.reject) :
    program (.compare pc)=MicrocodeEmbedding.instruction compareBinding.ports Label.compare (BinaryCompare.program pc) := by
  cases pc with
  | done r => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports Label.copy (NativeMappedCopy.program id pc) := by
  have hn : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction eraseBinding.ports Label.erase (NativeErase.program pc) := by
  have hn : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

end TransposeFollowup.DimensionAdvance


namespace TransposeFollowup.DimensionAdvance
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_add (i : Fin 6) (pc : RepeatedAdd.Label) (a x : List Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (addBinding i).ports (Label.add i)
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] a x) (fun p => pos (addPort i p))) (frame s pos)=
      cfg (.add i pc) ((addBinding i).values (RepeatedAdd.ready [true] a x).tapes s) pos := by
  exact (addBinding i).embed_bank_project _ _ _ _ _

theorem add_result (i : Fin 6) (a x : List Bool) (s : Bank) :
    (addBinding i).values (RepeatedAdd.ready [true] (RepeatedAdd.addWord a x) x).tapes s=
      Function.update ((addBinding i).values (RepeatedAdd.ready [true] a x).tapes s) (accPort i)
        (Counter.marked (RepeatedAdd.addWord a x)) := by
  funext p;fin_cases i <;> cases p <;> rfl

theorem add_call (i : Fin 6) (a x : List Bool) (hl : a.length=x.length) (s : Bank) (pos : Port → ℤ)
    (hi : (addBinding i).values (RepeatedAdd.ready [true] a x).tapes s=s) :
    ∃ t ≤ 18*x.length+51, Trace t (cfg (.add i (.counter 0)) s pos)
      (cfg (.add i (.counter 12)) (Function.update s (accPort i) (Counter.marked (RepeatedAdd.addWord a x))) pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace a x hl (fun p => pos (addPort i p))
  have he := MicrocodeEmbedding.trace_embed (addBinding i).ports (Label.add i) RepeatedAdd.program program
    (frame s pos) (add_code i) htr
  exact ⟨t,ht,by simpa only [embed_add,add_result,hi] using he⟩

theorem embed_compare (pc : BinaryCompare.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports Label.compare
      (BinaryCompare.cfg pc a b (fun p => pos (compareBinding.ports p))).denote (frame s pos)=
      cfg (.compare pc) (compareBinding.values (BinaryCompare.bank a b) s) pos := by
  exact compareBinding.embed_bank_project _ _ _ _ _

theorem compare_call (a b : List Bool) (hl : a.length=b.length) (s : Bank) (pos : Port → ℤ)
    (hi : compareBinding.values (BinaryCompare.bank (Counter.marked a) (Counter.marked b)) s=s) :
    ∃ t ≤ 5*a.length+6, Trace t (cfg (.compare (.scan .equal)) s pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (Counter.value a) (Counter.value b)))) s pos) := by
  change compareBinding.values (BinaryCompare.bank (BinaryCompare.marked a) (BinaryCompare.marked b)) s=s at hi
  obtain ⟨t,ht,htr⟩ := BinaryCompare.comparison_trace a b hl (fun p => pos (compareBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed compareBinding.ports Label.compare BinaryCompare.program program
    (frame s pos) compare_code htr
  exact ⟨t,ht,by simpa only [embed_compare,hi,← NativeCounter.word_value] using he⟩

theorem embed_copy (pc : NativeMappedCopy.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc a b (fun p => pos (copyBinding.ports p))) (frame s pos)=
      cfg (.copy pc) (copyBinding.values (NativeMappedCopy.bank a b) s) pos := by
  exact copyBinding.embed_bank_project _ _ _ _ _

theorem copy_result (a : List Bool) (s : Bank) :
    copyBinding.values (NativeMappedCopy.bank (Counter.marked a) (Counter.marked a)) s=
      Function.update (copyBinding.values (NativeMappedCopy.bank (Counter.marked a) ⟨[],[]⟩) s)
        Port.copyThreshold (Counter.marked a) := by
  funext p;cases p <;> rfl

theorem copy_call (a : List Bool) (s : Bank) (pos : Port → ℤ)
    (hi : copyBinding.values (NativeMappedCopy.bank (Counter.marked a) ⟨[],[]⟩) s=s) :
    ∃ t ≤ 6*a.length+14, Trace t (cfg (.copy (.init (.erase 0))) s pos)
      (cfg (.copy (.seal .done)) (Function.update s Port.copyThreshold (Counter.marked a)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id a (fun p => pos (copyBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy (NativeMappedCopy.program id) program
    (frame s pos) copy_code htr
  exact ⟨t,ht,by simpa only [embed_copy,List.map_id,copy_result,hi] using he⟩

theorem embed_erase (pc : NativeErase.Label) (a : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed eraseBinding.ports Label.erase
      (NativeErase.cfg pc a (fun _ => pos .copyThreshold)).denote (frame s pos)=
      cfg (.erase pc) (Function.update s Port.copyThreshold a) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← eraseBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem erase_call (a : List Bool) (s : Bank) (pos : Port → ℤ) (hi : s .copyThreshold=Counter.marked a) :
    ∃ t ≤ 4*a.length+4, Trace t (cfg (.erase 2) s pos)
      (cfg (.erase 0) (Function.update s Port.copyThreshold ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace a (fun _ => pos .copyThreshold)
  have he := MicrocodeEmbedding.trace_embed eraseBinding.ports Label.erase NativeErase.program program
    (frame s pos) erase_code htr
  have hin : Function.update s Port.copyThreshold (Counter.marked a)=s := by rw [← hi];exact Function.update_eq_self _ _
  exact ⟨t,ht,by simpa only [embed_erase,hin] using he⟩

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ) (hc : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ hc

end TransposeFollowup.DimensionAdvance


namespace TransposeFollowup.DimensionAdvance
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

structure Words where
  candidate : List Bool
  square : List Bool
  bits : List Bool
  threshold : List Bool
  deriving DecidableEq

def Sized (w : Words) (m : ℕ) : Prop :=
  w.candidate.length=m ∧ w.square.length=m ∧ w.bits.length=m ∧ w.threshold.length=m

def word (w : Words) (m : ℕ) : Port → List Bool
  | .candidate => w.candidate | .square => w.square | .bits => w.bits | .threshold => w.threshold
  | .unit => ArithmeticSeed.one m | .zero => ArithmeticSeed.zeros m
  | .fuel => [true] | .scratch => [] | .copyThreshold => w.threshold

def updateWord (w : Words) (p : Port) (xs : List Bool) : Words :=
  match p with
  | .candidate => {w with candidate:=xs} | .square => {w with square:=xs}
  | .bits => {w with bits:=xs} | .threshold => {w with threshold:=xs} | _ => w

def added (i : Fin 6) (w : Words) (m : ℕ) : Words :=
  updateWord w (accPort i) (RepeatedAdd.addWord (word w m (accPort i)) (word w m (factorPort i)))

def bank (w : Words) (m : ℕ) (copy : Tape Bool) : Bank
  | .scratch => BinaryCarry.preparedOutput
  | .copyThreshold => copy
  | p => Counter.marked (word w m p)

theorem operand_lengths (i : Fin 6) (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) :
    (word w m (accPort i)).length=m ∧ (word w m (factorPort i)).length=m := by
  rcases hw with ⟨hk,hs,hb,ht⟩
  fin_cases i <;> simp [accPort,factorPort,word,hk,hs,hb,ht,ArithmeticSeed.one_length m hm]

theorem added_sized (i : Fin 6) (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) : Sized (added i w m) m := by
  have hl := operand_lengths i w m hm hw
  have ha := RepeatedAdd.addWord_length (word w m (accPort i)) (word w m (factorPort i)) (hl.1.trans hl.2.symm)
  rw [hl.2] at ha
  rcases hw with ⟨hk,hs,hb,ht⟩
  fin_cases i <;> simp_all [Sized,added,updateWord,accPort,word,factorPort]

theorem add_bank_ready (i : Fin 6) (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (copy : Tape Bool)
    (hc : i=5 → copy=Counter.marked w.threshold) :
    (addBinding i).values (RepeatedAdd.ready [true] (word w m (accPort i)) (word w m (factorPort i))).tapes
      (bank w m copy)=bank w m copy := by
  have hl := (operand_lengths i w m hm hw).2
  funext p
  fin_cases i <;> cases p
  all_goals simp_all [bank,addBinding,accPort,factorPort,word,FinitePortBinding.values,
    RepeatedAdd.ready,RepeatedAdd.Bank.tapes,ArithmeticSeed.zeros,BinaryCarry.marked,BinaryCompare.marked,Counter.marked]

theorem add_bank_result (i : Fin 6) (w : Words) (m : ℕ) (copy : Tape Bool) :
    Function.update (bank w m copy) (accPort i)
      (Counter.marked (RepeatedAdd.addWord (word w m (accPort i)) (word w m (factorPort i))))=
      bank (added i w m) m copy := by
  funext p;fin_cases i <;> cases p <;> rfl

theorem word_add_call (i : Fin 6) (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (copy : Tape Bool)
    (hc : i=5 → copy=Counter.marked w.threshold) (pos : Port → ℤ) :
    ∃ t ≤ 18*m+51, Trace t (cfg (.add i (.counter 0)) (bank w m copy) pos)
      (cfg (.add i (.counter 12)) (bank (added i w m) m copy) pos) := by
  have hl := operand_lengths i w m hm hw
  obtain ⟨t,ht,htr⟩ := add_call i (word w m (accPort i)) (word w m (factorPort i)) (hl.1.trans hl.2.symm)
    (bank w m copy) pos (add_bank_ready i w m hm hw copy hc)
  exact ⟨t,by simpa only [hl.2] using ht,by simpa only [add_bank_result] using htr⟩

theorem word_compare_call (w : Words) (m : ℕ) (hw : Sized w m) (pos : Port → ℤ) :
    ∃ t ≤ 5*m+6, Trace t (cfg (.compare (.scan .equal)) (bank w m ⟨[],[]⟩) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (Counter.value w.candidate) (Counter.value w.threshold))))
        (bank w m ⟨[],[]⟩) pos) := by
  have hi : compareBinding.values (BinaryCompare.bank (Counter.marked w.candidate) (Counter.marked w.threshold))
      (bank w m ⟨[],[]⟩)=bank w m ⟨[],[]⟩ := by funext p;cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := compare_call w.candidate w.threshold (hw.1.trans hw.2.2.2.symm) (bank w m ⟨[],[]⟩) pos hi
  exact ⟨t,by simpa only [hw.1] using ht,htr⟩

theorem word_copy_call (w : Words) (m : ℕ) (hw : Sized w m) (pos : Port → ℤ) :
    ∃ t ≤ 6*m+14, Trace t (cfg (.copy (.init (.erase 0))) (bank w m ⟨[],[]⟩) pos)
      (cfg (.copy (.seal .done)) (bank w m (Counter.marked w.threshold)) pos) := by
  have hi : copyBinding.values (NativeMappedCopy.bank (Counter.marked w.threshold) ⟨[],[]⟩)
      (bank w m ⟨[],[]⟩)=bank w m ⟨[],[]⟩ := by funext p;cases p <;> rfl
  have he : Function.update (bank w m ⟨[],[]⟩) Port.copyThreshold (Counter.marked w.threshold)=bank w m (Counter.marked w.threshold) := by
    funext p;cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := copy_call w.threshold (bank w m ⟨[],[]⟩) pos hi
  exact ⟨t,by simpa only [hw.2.2.2] using ht,by simpa only [he] using htr⟩

theorem word_erase_call (w : Words) (m : ℕ) (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*xs.length+4, Trace t (cfg (.erase 2) (bank w m (Counter.marked xs)) pos)
      (cfg (.erase 0) (bank w m ⟨[],[]⟩) pos) := by
  have he : Function.update (bank w m (Counter.marked xs)) Port.copyThreshold (⟨[],[]⟩:Tape Bool)=bank w m ⟨[],[]⟩ := by
    funext p;cases p <;> rfl
  obtain ⟨t,ht,htr⟩ := erase_call xs (bank w m (Counter.marked xs)) pos rfl
  exact ⟨t,ht,by simpa only [he] using htr⟩

end TransposeFollowup.DimensionAdvance


namespace TransposeFollowup.DimensionAdvance
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

open NativeCountedLoop (trace_trans)

def prefixWords (w : Words) (m : ℕ) : Words := added 3 (added 2 (added 1 (added 0 w m) m) m) m
def grownWords (w : Words) (m : ℕ) : Words := added 5 (added 4 w m) m
def result (w : Words) (m : ℕ) : Words :=
  let p := prefixWords w m
  if Counter.value p.threshold < Counter.value p.candidate then grownWords p m else p

theorem prefix_sized (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) : Sized (prefixWords w m) m :=
  added_sized 3 _ m hm (added_sized 2 _ m hm (added_sized 1 _ m hm (added_sized 0 w m hm hw)))

theorem grown_sized (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) : Sized (grownWords w m) m :=
  added_sized 5 _ m hm (added_sized 4 w m hm hw)

theorem result_sized (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) : Sized (result w m) m := by
  dsimp only [result]
  split
  · exact grown_sized _ _ hm (prefix_sized w m hm hw)
  · exact prefix_sized w m hm hw

theorem prefix_trace (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (pos : Port → ℤ) :
    ∃ t ≤ 72*m+208, Trace t (cfg start (bank w m ⟨[],[]⟩) pos)
      (cfg (.compare (.scan .equal)) (bank (prefixWords w m) m ⟨[],[]⟩) pos) := by
  let a := added 0 w m
  let b := added 1 a m
  let c := added 2 b m
  let d := added 3 c m
  have ha : Sized a m := added_sized 0 w m hm hw
  have hb : Sized b m := added_sized 1 a m hm ha
  have hc : Sized c m := added_sized 2 b m hm hb
  obtain ⟨ta,hta,tra⟩ := word_add_call 0 w m hm hw ⟨[],[]⟩ (by simp) pos
  have ja := jump_trace (.add 0 (.counter 12)) (.add 1 (.counter 0)) (bank a m ⟨[],[]⟩) pos rfl
  obtain ⟨tb,htb,trb⟩ := word_add_call 1 a m hm ha ⟨[],[]⟩ (by simp) pos
  have jb := jump_trace (.add 1 (.counter 12)) (.add 2 (.counter 0)) (bank b m ⟨[],[]⟩) pos rfl
  obtain ⟨tc,htc,trc⟩ := word_add_call 2 b m hm hb ⟨[],[]⟩ (by simp) pos
  have jc := jump_trace (.add 2 (.counter 12)) (.add 3 (.counter 0)) (bank c m ⟨[],[]⟩) pos rfl
  obtain ⟨td,htd,trd⟩ := word_add_call 3 c m hm hc ⟨[],[]⟩ (by simp) pos
  have jd := jump_trace (.add 3 (.counter 12)) (.compare (.scan .equal)) (bank d m ⟨[],[]⟩) pos rfl
  exact ⟨ta+1+tb+1+tc+1+td+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans
    (trace_trans (trace_trans (trace_trans tra ja) trb) jb) trc) jc) trd) jd⟩

theorem grown_trace (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (pos : Port → ℤ) :
    ∃ t ≤ 46*m+125, Trace t (cfg (.compare (.done .greater)) (bank w m ⟨[],[]⟩) pos)
      (cfg .done (bank (grownWords w m) m ⟨[],[]⟩) pos) := by
  let a := added 4 w m
  let b := added 5 a m
  have ha : Sized a m := added_sized 4 w m hm hw
  have j0 := jump_trace (.compare (.done .greater)) (.add 4 (.counter 0)) (bank w m ⟨[],[]⟩) pos rfl
  obtain ⟨ta,hta,tra⟩ := word_add_call 4 w m hm hw ⟨[],[]⟩ (by simp) pos
  have ja := jump_trace (.add 4 (.counter 12)) (.copy (.init (.erase 0))) (bank a m ⟨[],[]⟩) pos rfl
  obtain ⟨tb,htb,trb⟩ := word_copy_call a m ha pos
  have jb := jump_trace (.copy (.seal .done)) (.add 5 (.counter 0)) (bank a m (Counter.marked a.threshold)) pos rfl
  obtain ⟨tc,htc,trc⟩ := word_add_call 5 a m hm ha (Counter.marked a.threshold) (by intro _;rfl) pos
  have jc := jump_trace (.add 5 (.counter 12)) (.erase 2) (bank b m (Counter.marked a.threshold)) pos rfl
  obtain ⟨td,htd,trd⟩ := word_erase_call b m a.threshold pos
  have jd := jump_trace (.erase 0) .done (bank b m ⟨[],[]⟩) pos rfl
  refine ⟨1+ta+1+tb+1+tc+1+td+1,?_,?_⟩
  · rw [ha.2.2.2] at htd
    omega
  · exact trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans
      (trace_trans (trace_trans j0 tra) ja) trb) jb) trc) jc) trd) jd

theorem numeric_greater_iff (a b : ℕ) : BinaryCompare.numeric .equal a b=.greater ↔ b < a := by
  by_cases hab : a < b
  · have hba : ¬b < a := by omega
    simp [BinaryCompare.numeric,hab,hba]
  · simp [BinaryCompare.numeric,hab]

theorem complete_trace (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (pos : Port → ℤ) :
    ∃ t ≤ 123*m+339, Trace t (cfg start (bank w m ⟨[],[]⟩) pos)
      (cfg .done (bank (result w m) m ⟨[],[]⟩) pos) := by
  let p := prefixWords w m
  have hp : Sized p m := prefix_sized w m hm hw
  obtain ⟨a,ha,ta⟩ := prefix_trace w m hm hw pos
  obtain ⟨b,hb,tb⟩ := word_compare_call p m hp pos
  let r := BinaryCompare.numeric .equal (Counter.value p.candidate) (Counter.value p.threshold)
  by_cases hg : Counter.value p.threshold < Counter.value p.candidate
  · dsimp only [p] at hg
    have hr : r=.greater := (numeric_greater_iff _ _).mpr hg
    change Trace b (cfg (.compare (.scan .equal)) (bank p m ⟨[],[]⟩) pos)
      (cfg (.compare (.done r)) (bank p m ⟨[],[]⟩) pos) at tb
    rw [hr] at tb
    obtain ⟨c,hc,tc⟩ := grown_trace p m hm hp pos
    refine ⟨a+b+c,by omega,?_⟩
    simpa only [result,hg,ite_true] using trace_trans (trace_trans ta tb) tc
  · dsimp only [p] at hg
    have hr : r≠.greater := by intro h;exact hg ((numeric_greater_iff _ _).mp h)
    have hcode : program (.compare (.done r))=.jump .done := by
      cases hr' : r with
      | greater => exact False.elim (hr hr')
      | _ => rfl
    have tj := jump_trace (.compare (.done r)) .done (bank p m ⟨[],[]⟩) pos hcode
    refine ⟨a+b+1,by omega,?_⟩
    simpa only [result,hg,ite_false] using trace_trans (trace_trans ta tb) tj

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_complete (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) : ∃ t ≤ 123*m+339,
    Transpose.stepN nativeMachine input t ((cfg start (bank w m ⟨[],[]⟩) pos).denote nativeEncoding program ip outRev)=
      some ((cfg .done (bank (result w m) m ⟨[],[]⟩) pos).denote nativeEncoding program ip outRev) ∧
    Transpose.step nativeMachine input ((cfg .done (bank (result w m) m ⟨[],[]⟩) pos).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace w m hm hw pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) : ∃ t ≤ 123*m+339,
    Transpose.stepN (NativeMicrocode.machine encoding target) input t
      ((MicrocodeEmbedding.embed ports labels (cfg start (bank w m ⟨[],[]⟩) pos) outerFrame).denote encoding target ip outRev)=
      some ((MicrocodeEmbedding.embed ports labels (cfg .done (bank (result w m) m ⟨[],[]⟩) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace w m hm hw pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input ip outRev hc htr⟩

theorem fixed_resources : nativeMachine.k=9 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=655 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=9
    decide +kernel
  · change Fintype.card Label-1+1=655
    decide +kernel

end TransposeFollowup.DimensionAdvance


namespace TransposeFollowup.DimensionAdvance
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def values (w : Words) : DimensionCandidate.State :=
  ⟨Counter.value w.candidate,Counter.value w.square,Counter.value w.bits,Counter.value w.threshold⟩

theorem add_value_exact (a x : List Bool) (hl : a.length=x.length)
    (hf : Counter.value a+Counter.value x < 2^x.length) :
    Counter.value (RepeatedAdd.addWord a x)=Counter.value a+Counter.value x := by
  simpa only [← NativeCounter.word_value,Nat.mod_eq_of_lt hf] using RepeatedAdd.addWord_value a x hl

theorem prefix_values (w : Words) (m k : ℕ) (hm : 0 < m) (hw : Sized w m)
    (hv : values w=DimensionCandidate.canonical k) (hf : (k+1)*(k+1) < 2^m) :
    values (prefixWords w m)=⟨k+1,(k+1)*(k+1),Transpose.entryBits k,2^Transpose.entryBits k⟩ := by
  have hk : Counter.value w.candidate=k := congrArg DimensionCandidate.State.candidate hv
  have hs : Counter.value w.square=k*k := congrArg DimensionCandidate.State.square hv
  have hb : Counter.value w.bits=Transpose.entryBits k := congrArg DimensionCandidate.State.bits hv
  have ht : Counter.value w.threshold=2^Transpose.entryBits k := congrArg DimensionCandidate.State.threshold hv
  let a := added 0 w m
  let b := added 1 a m
  let c := added 2 b m
  let d := added 3 c m
  have ha : Sized a m := added_sized 0 w m hm hw
  have hbw : Sized b m := added_sized 1 a m hm ha
  have hu := ArithmeticSeed.one_length m hm
  have va : Counter.value a.square=k*k+k := by
    change Counter.value (RepeatedAdd.addWord w.square w.candidate)=_
    rw [add_value_exact _ _ (hw.2.1.trans hw.1.symm) (by rw [hw.1,hs,hk];nlinarith),hs,hk]
  have vb : Counter.value b.square=k*k+k+k := by
    change Counter.value (RepeatedAdd.addWord a.square w.candidate)=_
    rw [add_value_exact _ _ (ha.2.1.trans hw.1.symm) (by rw [hw.1,va,hk];nlinarith),va,hk]
  have vc : Counter.value c.square=(k+1)*(k+1) := by
    change Counter.value (RepeatedAdd.addWord b.square (ArithmeticSeed.one m))=_
    rw [add_value_exact _ _ (hbw.2.1.trans hu.symm) (by rw [hu,vb,ArithmeticSeed.one_value];nlinarith),vb,ArithmeticSeed.one_value]
    ring
  have vd : Counter.value d.candidate=k+1 := by
    change Counter.value (RepeatedAdd.addWord w.candidate (ArithmeticSeed.one m))=_
    rw [add_value_exact _ _ (hw.1.trans hu.symm) (by rw [hu,hk,ArithmeticSeed.one_value];nlinarith),hk,ArithmeticSeed.one_value]
  change (⟨Counter.value d.candidate,Counter.value c.square,Counter.value w.bits,Counter.value w.threshold⟩:DimensionCandidate.State)=_
  rw [vd,vc,hb,ht]

theorem grown_values (w : Words) (m : ℕ) (hm : 0 < m) (hw : Sized w m)
    (hb : Counter.value w.bits+1 < 2^m) (ht : 2*Counter.value w.threshold < 2^m) :
    values (grownWords w m)=⟨Counter.value w.candidate,Counter.value w.square,
      Counter.value w.bits+1,2*Counter.value w.threshold⟩ := by
  have hu := ArithmeticSeed.one_length m hm
  have vb : Counter.value (RepeatedAdd.addWord w.bits (ArithmeticSeed.one m))=Counter.value w.bits+1 := by
    rw [add_value_exact _ _ (hw.2.2.1.trans hu.symm) (by simpa only [hu,ArithmeticSeed.one_value] using hb),ArithmeticSeed.one_value]
  have vt : Counter.value (RepeatedAdd.addWord w.threshold w.threshold)=2*Counter.value w.threshold := by
    rw [add_value_exact _ _ rfl (by rw [hw.2.2.2];omega)]
    omega
  change (⟨Counter.value w.candidate,Counter.value w.square,
    Counter.value (RepeatedAdd.addWord w.bits (ArithmeticSeed.one m)),
    Counter.value (RepeatedAdd.addWord w.threshold w.threshold)⟩:DimensionCandidate.State)=_
  rw [vb,vt]

theorem result_values (w : Words) (m k : ℕ) (hm : 0 < m) (hw : Sized w m) (hk : 1 ≤ k)
    (hv : values w=DimensionCandidate.canonical k) (hs : (k+1)*(k+1) < 2^m)
    (hb : Transpose.entryBits k+1 < 2^m) (ht : 2*2^Transpose.entryBits k < 2^m) :
    values (result w m)=DimensionCandidate.canonical (k+1) := by
  let p := prefixWords w m
  have hp : Sized p m := prefix_sized w m hm hw
  have hvp := prefix_values w m k hm hw hv hs
  have vpk : Counter.value p.candidate=k+1 := congrArg DimensionCandidate.State.candidate hvp
  have vps : Counter.value p.square=(k+1)*(k+1) := congrArg DimensionCandidate.State.square hvp
  have vpb : Counter.value p.bits=Transpose.entryBits k := congrArg DimensionCandidate.State.bits hvp
  have vpt : Counter.value p.threshold=2^Transpose.entryBits k := congrArg DimensionCandidate.State.threshold hvp
  have hpoly : (k+1)*(k+1)=k*k+k+k+1 := by ring
  have hadv := DimensionCandidate.advance_at k hk
  by_cases hg : 2^Transpose.entryBits k < k+1
  · have hgp : Counter.value p.threshold < Counter.value p.candidate := by rw [vpt,vpk];exact hg
    have he : result w m=grownWords p m := by
      change (if Counter.value p.threshold < Counter.value p.candidate then grownWords p m else p)=_
      simp only [hgp,ite_true]
    rw [he,grown_values p m hm hp (by rw [vpb];exact hb) (by rw [vpt];exact ht),vpk,vps,vpb,vpt,hpoly,two_mul]
    simpa only [DimensionCandidate.advance,DimensionCandidate.canonical,hg,ite_true] using hadv
  · have hgp : ¬Counter.value p.threshold < Counter.value p.candidate := by rw [vpt,vpk];exact hg
    have he : result w m=p := by
      change (if Counter.value p.threshold < Counter.value p.candidate then grownWords p m else p)=_
      simp only [hgp,ite_false]
    rw [he,hvp,hpoly]
    simpa only [DimensionCandidate.advance,DimensionCandidate.canonical,hg,ite_false] using hadv

theorem candidate_trace (w : Words) (m k : ℕ) (hm : 0 < m) (hw : Sized w m) (hk : 1 ≤ k)
    (hv : values w=DimensionCandidate.canonical k) (hs : (k+1)*(k+1) < 2^m)
    (hb : Transpose.entryBits k+1 < 2^m) (ht : 2*2^Transpose.entryBits k < 2^m) (pos : Port → ℤ) :
    ∃ next, Sized next m ∧ values next=DimensionCandidate.canonical (k+1) ∧
    ∃ t ≤ 123*m+339, Trace t (cfg start (bank w m ⟨[],[]⟩) pos) (cfg .done (bank next m ⟨[],[]⟩) pos) :=
  ⟨result w m,result_sized w m hm hw,result_values w m k hm hw hk hv hs hb ht,complete_trace w m hm hw pos⟩

theorem search_fits {k n : ℕ} (hk : 1 ≤ k) (hkn : k < n) :
    (k+1)*(k+1) < 2^DimensionCandidate.width (Transpose.inputLength n) ∧
    Transpose.entryBits k+1 < 2^DimensionCandidate.width (Transpose.inputLength n) ∧
    2*2^Transpose.entryBits k < 2^DimensionCandidate.width (Transpose.inputLength n) := by
  have hn : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hL := DimensionCandidate.dimension_le_length n hn
  have hb := Transpose.Tape.Impl.entryBits_le_self hk
  have ht := DimensionCandidate.threshold_bound k hk
  have hb1 : 1 ≤ Transpose.entryBits n := by unfold Transpose.entryBits;omega
  have hs : n*n ≤ Transpose.inputLength n := Nat.le_mul_of_pos_right _ hb1
  have hf := DimensionCandidate.double_length_fit (Transpose.inputLength n)
  have hnext : (k+1)*(k+1) ≤ n*n := by nlinarith
  have h2n : 2*n ≤ n*n := by nlinarith
  constructor
  · omega
  constructor
  · omega
  · nlinarith

theorem search_candidate_trace (w : Words) (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (hw : Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : values w=DimensionCandidate.canonical k) (pos : Port → ℤ) :
    ∃ next,Sized next (DimensionCandidate.width (Transpose.inputLength n)) ∧
      values next=DimensionCandidate.canonical (k+1) ∧
    ∃ t ≤ 123*DimensionCandidate.width (Transpose.inputLength n)+339,
      Trace t (cfg start (bank w (DimensionCandidate.width (Transpose.inputLength n)) ⟨[],[]⟩) pos)
        (cfg .done (bank next (DimensionCandidate.width (Transpose.inputLength n)) ⟨[],[]⟩) pos) := by
  have hm : 0 < DimensionCandidate.width (Transpose.inputLength n) := by unfold DimensionCandidate.width;omega
  have hf := search_fits hk hkn
  exact candidate_trace w _ k hm hw hk hv hf.1 hf.2.1 hf.2.2 pos

end TransposeFollowup.DimensionAdvance


/-! The dimension-search transition has no supplied dimension or loop count.
It evaluates the current candidate, compares against a retained length word,
clears both product temporaries, and either returns or physically advances. -/
namespace TransposeFollowup.DimensionSearch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port
  | candidate | square | bits | threshold | unit | zero | fuel | scratch | copyThreshold
  | product | repeatFuel | length
  deriving DecidableEq
instance : Fintype Port where
  elems:={.candidate,.square,.bits,.threshold,.unit,.zero,.fuel,.scratch,.copyThreshold,.product,.repeatFuel,.length}
  complete:=by intro p;cases p <;> simp
abbrev Bank := Port → Tape Bool

def advancePort : DimensionAdvance.Port → Port
  | .candidate => .candidate | .square => .square | .bits => .bits | .threshold => .threshold
  | .unit => .unit | .zero => .zero | .fuel => .fuel | .scratch => .scratch | .copyThreshold => .copyThreshold

def advanceBinding : FinitePortBinding DimensionAdvance.Port Port where
  ports:=⟨advancePort,by decide +kernel⟩
  decode:=fun p => match p with
    | .candidate => some .candidate | .square => some .square | .bits => some .bits | .threshold => some .threshold
    | .unit => some .unit | .zero => some .zero | .fuel => some .fuel | .scratch => some .scratch
    | .copyThreshold => some .copyThreshold | _ => none
  decode_spec:=by decide +kernel

def copyPorts (fuel : Bool) : Fin 2 → Port := if fuel then ![.bits,.repeatFuel] else ![.zero,.product]
def copyBinding (fuel : Bool) : FinitePortBinding (Fin 2) Port where
  ports:=⟨copyPorts fuel,by cases fuel <;> decide +kernel⟩
  decode:=fun p => if p=copyPorts fuel 0 then some 0 else if p=copyPorts fuel 1 then some 1 else none
  decode_spec:=by cases fuel <;> decide +kernel

def multiplyPort : RepeatedAdd.Port → Port
  | .acc => .product | .factor => .square | .fuel => .repeatFuel | .scratch => .scratch | .zero => .zero

def multiplyBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports:=⟨multiplyPort,by decide +kernel⟩
  decode:=fun p => match p with
    | .product => some .acc | .square => some .factor
    | .repeatFuel => some .fuel | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec:=by decide +kernel

def compareBinding : FinitePortBinding (Fin 2) Port where
  ports:=⟨![.product,.length],by decide +kernel⟩
  decode:=fun p => match p with | .product => some 0 | .length => some 1 | _ => none
  decode_spec:=by decide +kernel

def erasePort (fuel : Bool) : Port := if fuel then .repeatFuel else .product

def eraseBinding (fuel : Bool) : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => erasePort fuel,by intro _ _ _;exact Subsingleton.elim _ _⟩
  decode:=fun p => if p=erasePort fuel then some 0 else none
  decode_spec:=by cases fuel <;> decide +kernel

inductive Label
  | copy (fuel : Bool) (pc : NativeMappedCopy.Label)
  | multiply (pc : RepeatedAdd.Label)
  | compare (pc : BinaryCompare.Label)
  | erase (finish fuel : Bool) (pc : NativeErase.Label)
  | advance (pc : DimensionAdvance.Label)
  | done | reject
  deriving DecidableEq,Fintype

def start : Label := .copy false (.init (.erase 0))
def afterCopy (fuel : Bool) : Label := if fuel then .multiply (.counter 0) else .copy true (.init (.erase 0))
def afterErase (finish fuel : Bool) : Label :=
  if fuel then (if finish then .done else .advance DimensionAdvance.start) else .erase finish true 2

def program : Microcode.Program Port Label
  | .copy fuel pc => if pc=.seal .done then .jump (afterCopy fuel)
      else (copyBinding fuel).instruction (Label.copy fuel) (NativeMappedCopy.program id pc)
  | .multiply pc => if pc=.counter 12 then .jump (.compare (.scan .equal))
      else multiplyBinding.instruction Label.multiply (RepeatedAdd.program pc)
  | .compare (.done .less) => .jump (.erase false false 2)
  | .compare (.done .equal) => .jump (.erase true false 2)
  | .compare (.done .greater) => .reject
  | .compare pc => compareBinding.instruction Label.compare (BinaryCompare.program pc)
  | .erase finish fuel pc => if pc=0 then .jump (afterErase finish fuel)
      else (eraseBinding fuel).instruction (Label.erase finish fuel) (NativeErase.program pc)
  | .advance .done => .jump start
  | .advance pc => advanceBinding.instruction Label.advance (DimensionAdvance.program pc)
  | .done => .halt
  | .reject => .reject

theorem copy_code (fuel : Bool) (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy fuel pc)=MicrocodeEmbedding.instruction (copyBinding fuel).ports (Label.copy fuel) (NativeMappedCopy.program id pc) := by
  have hn : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem multiply_code (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt) (_ : RepeatedAdd.program pc≠.reject) :
    program (.multiply pc)=MicrocodeEmbedding.instruction multiplyBinding.ports Label.multiply (RepeatedAdd.program pc) := by
  have hn : pc≠.counter 12 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem compare_code (pc : BinaryCompare.Label) (hh : BinaryCompare.program pc≠.halt) (_ : BinaryCompare.program pc≠.reject) :
    program (.compare pc)=MicrocodeEmbedding.instruction compareBinding.ports Label.compare (BinaryCompare.program pc) := by
  cases pc with
  | done r => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem erase_code (finish fuel : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program (.erase finish fuel pc)=MicrocodeEmbedding.instruction (eraseBinding fuel).ports
      (Label.erase finish fuel) (NativeErase.program pc) := by
  have hn : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem advance_code (pc : DimensionAdvance.Label) (hh : DimensionAdvance.program pc≠.halt) (_ : DimensionAdvance.program pc≠.reject) :
    program (.advance pc)=MicrocodeEmbedding.instruction advanceBinding.ports Label.advance (DimensionAdvance.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

def bank (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) (product fuel : Tape Bool) : Bank
  | .candidate => DimensionAdvance.bank w m ⟨[],[]⟩ .candidate
  | .square => DimensionAdvance.bank w m ⟨[],[]⟩ .square
  | .bits => DimensionAdvance.bank w m ⟨[],[]⟩ .bits
  | .threshold => DimensionAdvance.bank w m ⟨[],[]⟩ .threshold
  | .unit => DimensionAdvance.bank w m ⟨[],[]⟩ .unit
  | .zero => DimensionAdvance.bank w m ⟨[],[]⟩ .zero
  | .fuel => DimensionAdvance.bank w m ⟨[],[]⟩ .fuel
  | .scratch => DimensionAdvance.bank w m ⟨[],[]⟩ .scratch
  | .copyThreshold => DimensionAdvance.bank w m ⟨[],[]⟩ .copyThreshold
  | .product => product | .repeatFuel => fuel | .length => Counter.marked length

def initial (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) := bank w m length ⟨[],[]⟩ ⟨[],[]⟩
def zeroed (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) := bank w m length (Counter.marked (ArithmeticSeed.zeros m)) ⟨[],[]⟩
def ready (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) := bank w m length (Counter.marked (ArithmeticSeed.zeros m)) (Counter.marked w.bits)
def productWord (w : DimensionAdvance.Words) (m : ℕ) := RepeatedAdd.repeatWord w.square (Counter.value w.bits) (ArithmeticSeed.zeros m)
def multiplied (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) :=
  bank w m length (Counter.marked (productWord w m)) (Counter.marked (List.replicate w.bits.length true))
def productCleared (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) :=
  bank w m length ⟨[],[]⟩ (Counter.marked (List.replicate w.bits.length true))

end TransposeFollowup.DimensionSearch


namespace TransposeFollowup.DimensionSearch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_copy (fuel : Bool) (pc : NativeMappedCopy.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (copyBinding fuel).ports (Label.copy fuel)
      (NativeMappedCopy.cfg pc a b (fun p => pos (copyPorts fuel p))) (frame s pos)=
      cfg (.copy fuel pc) ((copyBinding fuel).values (NativeMappedCopy.bank a b) s) pos := by
  exact (copyBinding fuel).embed_bank_project _ _ _ _ _

theorem zero_copy_call (w : DimensionAdvance.Words) (m : ℕ) (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*m+14, Trace t (cfg start (initial w m length) pos)
      (cfg (.copy false (.seal .done)) (zeroed w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id (ArithmeticSeed.zeros m) (fun p => pos (copyPorts false p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding false).ports (Label.copy false) (NativeMappedCopy.program id)
    program (frame (initial w m length) pos) (copy_code false) htr
  have hi : (copyBinding false).values (NativeMappedCopy.bank (Counter.marked (ArithmeticSeed.zeros m)) ⟨[],[]⟩)
      (initial w m length)=initial w m length := by funext p;cases p <;> rfl
  have hf : (copyBinding false).values (NativeMappedCopy.bank (Counter.marked (ArithmeticSeed.zeros m))
      (Counter.marked (ArithmeticSeed.zeros m))) (initial w m length)=zeroed w m length := by funext p;cases p <;> rfl
  exact ⟨t,by simpa only [ArithmeticSeed.zeros,List.length_replicate] using ht,
    by simpa only [embed_copy,List.map_id,hi,hf,start] using he⟩

theorem fuel_copy_call (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 6*m+14, Trace t (cfg (.copy true (.init (.erase 0))) (zeroed w m length) pos)
      (cfg (.copy true (.seal .done)) (ready w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id w.bits (fun p => pos (copyPorts true p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding true).ports (Label.copy true) (NativeMappedCopy.program id)
    program (frame (zeroed w m length) pos) (copy_code true) htr
  have hi : (copyBinding true).values (NativeMappedCopy.bank (Counter.marked w.bits) ⟨[],[]⟩)
      (zeroed w m length)=zeroed w m length := by funext p;cases p <;> rfl
  have hf : (copyBinding true).values (NativeMappedCopy.bank (Counter.marked w.bits) (Counter.marked w.bits))
      (zeroed w m length)=ready w m length := by funext p;cases p <;> rfl
  exact ⟨t,by simpa only [hw.2.2.1] using ht,by simpa only [embed_copy,List.map_id,hi,hf] using he⟩

theorem embed_multiply (pc : RepeatedAdd.Label) (w : DimensionAdvance.Words) (m : ℕ)
    (hw : DimensionAdvance.Sized w m) (length a fuel : List Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed multiplyBinding.ports Label.multiply
      (RepeatedAdd.cfg pc (RepeatedAdd.ready fuel a w.square) (fun p => pos (multiplyPort p)))
      (frame (initial w m length) pos)=cfg (.multiply pc)
        (bank w m length (Counter.marked a) (Counter.marked fuel)) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← multiplyBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p
  all_goals simp only [multiplyBinding,FinitePortBinding.values,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
    hw.2.1,bank,initial,DimensionAdvance.bank,DimensionAdvance.word,ArithmeticSeed.zeros]
  all_goals rfl

theorem multiply_call (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ Counter.value w.bits*(18*m+39)+4*m+8, Trace t
      (cfg (.multiply (.counter 0)) (ready w m length) pos)
      (cfg (.multiply (.counter 12)) (multiplied w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.repeated_add_trace w.bits (ArithmeticSeed.zeros m) w.square
    (by simpa only [ArithmeticSeed.zeros,List.length_replicate] using hw.2.1.symm) (fun p => pos (multiplyPort p))
  have he := MicrocodeEmbedding.trace_embed multiplyBinding.ports Label.multiply RepeatedAdd.program program
    (frame (initial w m length) pos) multiply_code htr
  refine ⟨t,?_,by simpa only [embed_multiply _ _ _ hw,ready,multiplied,productWord] using he⟩
  unfold RepeatedAdd.budget at ht
  rw [hw.2.1,hw.2.2.1] at ht
  nlinarith

theorem product_length (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m) :
    (productWord w m).length=m := by
  rw [productWord,RepeatedAdd.repeatWord_length w.square _ _ (by simpa only [ArithmeticSeed.zeros,List.length_replicate] using hw.2.1.symm),hw.2.1]

theorem embed_compare (pc : BinaryCompare.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed compareBinding.ports Label.compare
      (BinaryCompare.cfg pc a b (fun p => pos (compareBinding.ports p))).denote (frame s pos)=
      cfg (.compare pc) (compareBinding.values (BinaryCompare.bank a b) s) pos := by
  exact compareBinding.embed_bank_project _ _ _ _ _

theorem compare_call (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (hl : length.length=m) (pos : Port → ℤ) :
    ∃ t ≤ 5*m+6, Trace t (cfg (.compare (.scan .equal)) (multiplied w m length) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (Counter.value (productWord w m)) (Counter.value length))))
        (multiplied w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := BinaryCompare.comparison_trace (productWord w m) length ((product_length w m hw).trans hl.symm)
    (fun p => pos (compareBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed compareBinding.ports Label.compare BinaryCompare.program program
    (frame (multiplied w m length) pos) compare_code htr
  have hi : compareBinding.values (BinaryCompare.bank (BinaryCompare.marked (productWord w m)) (BinaryCompare.marked length))
      (multiplied w m length)=multiplied w m length := by funext p;cases p <;> rfl
  exact ⟨t,by simpa only [product_length w m hw] using ht,by simpa only [embed_compare,hi,← NativeCounter.word_value] using he⟩

theorem embed_erase (finish fuel : Bool) (pc : NativeErase.Label) (a : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (eraseBinding fuel).ports (Label.erase finish fuel)
      (NativeErase.cfg pc a (fun _ => pos (erasePort fuel))).denote (frame s pos)=
      cfg (.erase finish fuel pc) (Function.update s (erasePort fuel) a) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (eraseBinding fuel).values_eq_extend]
  congr 2 <;> funext p <;> cases fuel <;> cases p <;> rfl

theorem product_erase_call (finish : Bool) (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*m+4, Trace t (cfg (.erase finish false 2) (multiplied w m length) pos)
      (cfg (.erase finish false 0) (productCleared w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace (productWord w m) (fun _ => pos (erasePort false))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding false).ports (Label.erase finish false) NativeErase.program program
    (frame (multiplied w m length) pos) (erase_code finish false) htr
  have hi : Function.update (multiplied w m length) (erasePort false) (Counter.marked (productWord w m))=multiplied w m length :=
    Function.update_eq_self _ _
  have hf : Function.update (multiplied w m length) (erasePort false) (⟨[],[]⟩:Tape Bool)=productCleared w m length := by
    funext p;cases p <;> rfl
  exact ⟨t,by simpa only [product_length w m hw] using ht,by simpa only [embed_erase,hi,hf] using he⟩

theorem fuel_erase_call (finish : Bool) (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*m+4, Trace t (cfg (.erase finish true 2) (productCleared w m length) pos)
      (cfg (.erase finish true 0) (initial w m length) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace (List.replicate w.bits.length true) (fun _ => pos (erasePort true))
  have he := MicrocodeEmbedding.trace_embed (eraseBinding true).ports (Label.erase finish true) NativeErase.program program
    (frame (productCleared w m length) pos) (erase_code finish true) htr
  have hi : Function.update (productCleared w m length) (erasePort true) (Counter.marked (List.replicate w.bits.length true))=productCleared w m length :=
    Function.update_eq_self _ _
  have hf : Function.update (productCleared w m length) (erasePort true) (⟨[],[]⟩:Tape Bool)=initial w m length := by
    funext p;cases p <;> rfl
  exact ⟨t,by simpa only [List.length_replicate,hw.2.2.1] using ht,by simpa only [embed_erase,hi,hf] using he⟩

theorem embed_advance (pc : DimensionAdvance.Label) (w base : DimensionAdvance.Words) (m : ℕ)
    (length : List Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed advanceBinding.ports Label.advance
      (DimensionAdvance.cfg pc (DimensionAdvance.bank w m ⟨[],[]⟩) (fun p => pos (advancePort p)))
      (frame (initial base m length) pos)=cfg (.advance pc) (initial w m length) pos := by
  unfold MicrocodeEmbedding.embed DimensionAdvance.cfg cfg frame
  simp only [← advanceBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem advance_call (w : DimensionAdvance.Words) (m : ℕ) (hm : 0 < m) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 123*m+339, Trace t (cfg (.advance DimensionAdvance.start) (initial w m length) pos)
      (cfg (.advance .done) (initial (DimensionAdvance.result w m) m length) pos) := by
  obtain ⟨t,ht,htr⟩ := DimensionAdvance.complete_trace w m hm hw (fun p => pos (advancePort p))
  have he := MicrocodeEmbedding.trace_embed advanceBinding.ports Label.advance DimensionAdvance.program program
    (frame (initial w m length) pos) advance_code htr
  exact ⟨t,ht,by simpa only [embed_advance] using he⟩

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ) (hc : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ hc

end TransposeFollowup.DimensionSearch


namespace TransposeFollowup.DimensionSearch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

open NativeCountedLoop (trace_trans)

def computeBudget (b m : ℕ) : ℕ := b*(18*m+39)+21*m+45
def evaluateBudget (b m : ℕ) : ℕ := b*(18*m+39)+29*m+56
def iterationBudget (b m : ℕ) : ℕ := b*(18*m+39)+152*m+396

theorem compute_trace (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (hl : length.length=m) (pos : Port → ℤ) :
    ∃ t ≤ computeBudget (Counter.value w.bits) m, Trace t (cfg start (initial w m length) pos)
      (cfg (.compare (.done (BinaryCompare.numeric .equal (Counter.value (productWord w m)) (Counter.value length))))
        (multiplied w m length) pos) := by
  obtain ⟨a,ha,ta⟩ := zero_copy_call w m length pos
  have ja := jump_trace (.copy false (.seal .done)) (.copy true (.init (.erase 0))) (zeroed w m length) pos rfl
  obtain ⟨b,hb,tb⟩ := fuel_copy_call w m hw length pos
  have jb := jump_trace (.copy true (.seal .done)) (.multiply (.counter 0)) (ready w m length) pos rfl
  obtain ⟨c,hc,tc⟩ := multiply_call w m hw length pos
  have jc := jump_trace (.multiply (.counter 12)) (.compare (.scan .equal)) (multiplied w m length) pos rfl
  obtain ⟨d,hd,td⟩ := compare_call w m hw length hl pos
  exact ⟨a+1+b+1+c+1+d,by unfold computeBudget;omega,
    trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans ta ja) tb) jb) tc) jc) td⟩

theorem cleanup_trace (finish : Bool) (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (length : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 8*m+11, Trace t
      (cfg (.compare (.done (if finish then .equal else .less))) (multiplied w m length) pos)
      (cfg (if finish then .done else .advance DimensionAdvance.start) (initial w m length) pos) := by
  have j0 := jump_trace (.compare (.done (if finish then .equal else .less))) (.erase finish false 2)
    (multiplied w m length) pos (by cases finish <;> rfl)
  obtain ⟨a,ha,ta⟩ := product_erase_call finish w m hw length pos
  have ja := jump_trace (.erase finish false 0) (.erase finish true 2) (productCleared w m length) pos rfl
  obtain ⟨b,hb,tb⟩ := fuel_erase_call finish w m hw length pos
  have jb := jump_trace (.erase finish true 0) (if finish then .done else .advance DimensionAdvance.start)
    (initial w m length) pos rfl
  exact ⟨1+a+1+b+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans j0 ta) ja) tb) jb⟩

theorem product_value (w : DimensionAdvance.Words) (m : ℕ) (hw : DimensionAdvance.Sized w m)
    (hf : Counter.value w.bits*Counter.value w.square < 2^m) :
    Counter.value (productWord w m)=Counter.value w.square*Counter.value w.bits := by
  have hfit : BinaryCompare.value (ArithmeticSeed.zeros m)+Counter.value w.bits*BinaryCompare.value w.square < 2^w.square.length := by
    simpa only [ArithmeticSeed.zeros,← NativeCounter.word_value,PaddedWord.value_zeroes,Nat.zero_add,hw.2.1] using hf
  have h := RepeatedAdd.repeatWord_value_exact w.square (Counter.value w.bits) (ArithmeticSeed.zeros m)
    (by simpa only [ArithmeticSeed.zeros,List.length_replicate] using hw.2.1.symm) hfit
  simpa only [productWord,ArithmeticSeed.zeros,← NativeCounter.word_value,PaddedWord.value_zeroes,Nat.zero_add,Nat.mul_comm] using h

theorem valid_product (w : DimensionAdvance.Words) (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical k) :
    Counter.value (productWord w (DimensionCandidate.width (Transpose.inputLength n)))=Transpose.inputLength k := by
  have vs : Counter.value w.square=k*k := congrArg DimensionCandidate.State.square hv
  have vb : Counter.value w.bits=Transpose.entryBits k := congrArg DimensionCandidate.State.bits hv
  have hfit := (DimensionCandidate.state_fits hk hkn).2.2.2.2
  change Transpose.inputLength k < 2^DimensionCandidate.width (Transpose.inputLength n) at hfit
  rw [product_value w _ hw (by rw [vs,vb,Nat.mul_comm];exact hfit),vs,vb]
  rfl

theorem terminal_trace (w : DimensionAdvance.Words) (n : ℕ) (hn : 1 ≤ n)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical n)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ) :
    ∃ t ≤ evaluateBudget (Transpose.entryBits n) (DimensionCandidate.width (Transpose.inputLength n)),
      Trace t (cfg start (initial w (DimensionCandidate.width (Transpose.inputLength n)) length) pos)
        (cfg .done (initial w (DimensionCandidate.width (Transpose.inputLength n)) length) pos) := by
  let m := DimensionCandidate.width (Transpose.inputLength n)
  obtain ⟨a,ha,ta⟩ := compute_trace w m hw length hl pos
  have vp := valid_product w n n hn le_rfl hw hv
  have vb : Counter.value w.bits=Transpose.entryBits n := congrArg DimensionCandidate.State.bits hv
  have he : BinaryCompare.numeric .equal (Counter.value (productWord w m)) (Counter.value length)=.equal := by
    rw [vp,hL];simp [BinaryCompare.numeric]
  rw [he] at ta
  obtain ⟨b,hb,tb⟩ := cleanup_trace true w m hw length pos
  refine ⟨a+b,?_,trace_trans ta tb⟩
  rw [vb] at ha
  change a+b ≤ evaluateBudget (Transpose.entryBits n) m
  unfold computeBudget at ha
  unfold evaluateBudget
  omega

theorem body_trace (w : DimensionAdvance.Words) (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical k)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ) :
    let m := DimensionCandidate.width (Transpose.inputLength n)
    DimensionAdvance.Sized (DimensionAdvance.result w m) m ∧
    DimensionAdvance.values (DimensionAdvance.result w m)=DimensionCandidate.canonical (k+1) ∧
    ∃ t ≤ iterationBudget (Transpose.entryBits k) m,
      Trace t (cfg start (initial w m length) pos) (cfg start (initial (DimensionAdvance.result w m) m length) pos) := by
  let m := DimensionCandidate.width (Transpose.inputLength n)
  have hm : 0 < m := by dsimp [m,DimensionCandidate.width];omega
  have hf := DimensionAdvance.search_fits hk hkn
  refine ⟨DimensionAdvance.result_sized w m hm hw,DimensionAdvance.result_values w m k hm hw hk hv hf.1 hf.2.1 hf.2.2,?_⟩
  obtain ⟨a,ha,ta⟩ := compute_trace w m hw length hl pos
  have vp := valid_product w n k hk hkn.le hw hv
  have vb : Counter.value w.bits=Transpose.entryBits k := congrArg DimensionCandidate.State.bits hv
  have he : BinaryCompare.numeric .equal (Counter.value (productWord w m)) (Counter.value length)=.less := by
    rw [vp,hL]
    simp only [BinaryCompare.numeric,DimensionCandidate.length_strictMono hkn,ite_true]
  rw [he] at ta
  obtain ⟨b,hb,tb⟩ := cleanup_trace false w m hw length pos
  obtain ⟨c,hc,tc⟩ := advance_call w m hm hw length pos
  have tj := jump_trace (.advance .done) start (initial (DimensionAdvance.result w m) m length) pos rfl
  refine ⟨a+b+c+1,?_,trace_trans (trace_trans (trace_trans ta tb) tc) tj⟩
  rw [vb] at ha
  change a+b+c+1 ≤ iterationBudget (Transpose.entryBits k) m
  unfold computeBudget at ha
  unfold iterationBudget
  omega

end TransposeFollowup.DimensionSearch


/-! Prepared-input dimension search. No dimension or iteration limit occurs
in the transition program. Initialization and final bank cleanup are separate
paid obligations; this file does not claim a run from Transpose.init. -/
namespace TransposeFollowup.DimensionSearch
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

open NativeCountedLoop (trace_trans)

def loopBudget (n m r : ℕ) : ℕ := r*iterationBudget (Transpose.entryBits n) m+evaluateBudget (Transpose.entryBits n) m

theorem iteration_mono {a b : ℕ} (h : a ≤ b) (m : ℕ) : iterationBudget a m ≤ iterationBudget b m := by
  unfold iterationBudget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) _

theorem loop_trace (n k r : ℕ) (hk : 1 ≤ k) (hr : k+r=n) (w : DimensionAdvance.Words)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical k)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ) :
    let m := DimensionCandidate.width (Transpose.inputLength n)
    ∃ final,DimensionAdvance.Sized final m ∧ DimensionAdvance.values final=DimensionCandidate.canonical n ∧
    ∃ t ≤ loopBudget n m r,
      Trace t (cfg start (initial w m length) pos) (cfg .done (initial final m length) pos) := by
  let m := DimensionCandidate.width (Transpose.inputLength n)
  induction r generalizing k w with
  | zero =>
    have he : k=n := by omega
    subst k
    obtain ⟨t,ht,htr⟩ := terminal_trace w n hk hw hv length hl hL pos
    exact ⟨w,hw,hv,t,by simpa only [loopBudget,Nat.zero_mul,Nat.zero_add] using ht,htr⟩
  | succ r ih =>
    have hkn : k < n := by omega
    obtain ⟨hs,hvnext,a,ha,ta⟩ := body_trace w n k hk hkn hw hv length hl hL pos
    obtain ⟨last,hslast,hvlast,b,hb,tb⟩ := ih (k+1) (by omega) (by omega) (DimensionAdvance.result w m) hs hvnext
    have hm := iteration_mono (DimensionCandidate.entryBits_mono hkn.le) m
    have hcost : a ≤ iterationBudget (Transpose.entryBits n) m := ha.trans hm
    refine ⟨last,hslast,hvlast,a+b,?_,trace_trans ta tb⟩
    change b ≤ loopBudget n m r at hb
    change a+b ≤ loopBudget n m (r+1)
    unfold loopBudget at hb ⊢
    nlinarith

theorem evaluate_le_iteration (b m : ℕ) : evaluateBudget b m ≤ iterationBudget b m := by
  unfold evaluateBudget iterationBudget
  omega

theorem iteration_bound (b m : ℕ) (hb : 1 ≤ b) (hm : 1 ≤ m) : iterationBudget b m ≤ 605*b*m := by
  have hbm : b ≤ b*m := Nat.le_mul_of_pos_right b hm
  have hmb : m ≤ b*m := Nat.le_mul_of_pos_left m hb
  have h1 : 1 ≤ b*m := hb.trans hbm
  unfold iterationBudget
  nlinarith

theorem complete_budget (n : ℕ) (hn : 1 ≤ n) :
    loopBudget n (DimensionCandidate.width (Transpose.inputLength n)) (n-1) ≤ 7260*Transpose.inputLength n := by
  let m := DimensionCandidate.width (Transpose.inputLength n)
  let b := Transpose.entryBits n
  have hb : 1 ≤ b := by dsimp [b,Transpose.entryBits];omega
  have hm : 1 ≤ m := by dsimp [m,DimensionCandidate.width];omega
  have he := evaluate_le_iteration b m
  have hi := iteration_bound b m hb hm
  have hs := DimensionCandidate.search_budget n hn
  change n*b*m ≤ 12*Transpose.inputLength n at hs
  calc
    loopBudget n m (n-1) ≤ n*iterationBudget b m := by
      unfold loopBudget
      change (n-1)*iterationBudget b m+evaluateBudget b m ≤ n*iterationBudget b m
      calc
        _ ≤ (n-1)*iterationBudget b m+iterationBudget b m := Nat.add_le_add_left he _
        _ = ((n-1)+1)*iterationBudget b m := by ring
        _ = n*iterationBudget b m := by rw [Nat.sub_add_cancel hn]
    _ ≤ n*(605*b*m) := Nat.mul_le_mul_left n hi
    _ = 605*(n*b*m) := by ring
    _ ≤ 605*(12*Transpose.inputLength n) := Nat.mul_le_mul_left _ hs
    _ = 7260*Transpose.inputLength n := by ring

theorem complete_trace (n : ℕ) (hn : 1 ≤ n) (w : DimensionAdvance.Words)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical 1)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ) :
    let m := DimensionCandidate.width (Transpose.inputLength n)
    ∃ final,DimensionAdvance.Sized final m ∧ DimensionAdvance.values final=DimensionCandidate.canonical n ∧
    ∃ t ≤ 7260*Transpose.inputLength n,
      Trace t (cfg start (initial w m length) pos) (cfg .done (initial final m length) pos) := by
  obtain ⟨final,hs,hvfinal,t,ht,htr⟩ := loop_trace n 1 (n-1) (by omega) (by omega) w hw hv length hl hL pos
  exact ⟨final,hs,hvfinal,t,ht.trans (complete_budget n hn),htr⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem native_complete (n : ℕ) (hn : 1 ≤ n) (w : DimensionAdvance.Words)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical 1)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    let m := DimensionCandidate.width (Transpose.inputLength n)
    ∃ final,DimensionAdvance.Sized final m ∧ DimensionAdvance.values final=DimensionCandidate.canonical n ∧
    ∃ t ≤ 7260*Transpose.inputLength n,
      Transpose.stepN nativeMachine input t ((cfg start (initial w m length) pos).denote nativeEncoding program ip outRev)=
        some ((cfg .done (initial final m length) pos).denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input ((cfg .done (initial final m length) pos).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨final,hs,hvfinal,t,ht,htr⟩ := complete_trace n hn w hw hv length hl hL pos
  refine ⟨final,hs,hvfinal,t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (n : ℕ) (hn : 1 ≤ n) (w : DimensionAdvance.Words)
    (hw : DimensionAdvance.Sized w (DimensionCandidate.width (Transpose.inputLength n)))
    (hv : DimensionAdvance.values w=DimensionCandidate.canonical 1)
    (length : List Bool) (hl : length.length=DimensionCandidate.width (Transpose.inputLength n))
    (hL : Counter.value length=Transpose.inputLength n) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    let m := DimensionCandidate.width (Transpose.inputLength n)
    ∃ final,DimensionAdvance.Sized final m ∧ DimensionAdvance.values final=DimensionCandidate.canonical n ∧
    ∃ t ≤ 7260*Transpose.inputLength n,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (initial w m length) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (initial final m length) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨final,hs,hvfinal,t,ht,htr⟩ := complete_trace n hn w hw hv length hl hL pos
  exact ⟨final,hs,hvfinal,t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input ip outRev hc htr⟩

theorem fixed_resources : nativeMachine.k=12 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=864 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=12
    decide +kernel
  · change Fintype.card Label-1+1=864
    decide +kernel

end TransposeFollowup.DimensionSearch


/-! Controller for the remaining paid dimension-loader composition.
The transition code is fixed. Its entry has only a short length word;
initialization, candidate search, final trim and erasures are explicit.
This file alone does not yet prove the complete trace contract. -/
namespace TransposeFollowup.DimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | work (p : DimensionSearch.Port) | source | extra
  deriving DecidableEq, Fintype
abbrev Bank := Port → Tape Bool

def seedPort : ArithmeticSeed.Port → Port
  | .source => .source | .number => .work .length | .zeroA => .work .zero
  | .zeroB => .work .product | .one => .work .unit | .fuel => .work .fuel
  | .left => .work .scratch | .right => .extra

def seedBinding : FinitePortBinding ArithmeticSeed.Port Port where
  ports:=⟨seedPort,by decide +kernel⟩
  decode:=fun p => match p with
    | .source => some .source | .extra => some .right
    | .work .length => some .number | .work .zero => some .zeroA
    | .work .product => some .zeroB | .work .unit => some .one
    | .work .fuel => some .fuel | .work .scratch => some .left | _ => none
  decode_spec:=by decide +kernel

def copyTarget : Fin 4 → Port := ![.work .candidate,.work .square,.work .bits,.work .threshold]
def copyPorts (i : Fin 4) : Fin 2 → Port := ![.work .unit,copyTarget i]
def copyBinding (i : Fin 4) : FinitePortBinding (Fin 2) Port where
  ports:=⟨copyPorts i,by fin_cases i <;> decide +kernel⟩
  decode:=fun p => if p=.work .unit then some 0 else if p=copyTarget i then some 1 else none
  decode_spec:=by fin_cases i <;> decide +kernel

def addPort : RepeatedAdd.Port → Port
  | .acc => .work .threshold | .factor => .work .unit | .fuel => .work .fuel
  | .scratch => .work .scratch | .zero => .work .zero

def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports:=⟨addPort,by decide +kernel⟩
  decode:=fun p => match p with
    | .work .threshold => some .acc | .work .unit => some .factor | .work .fuel => some .fuel
    | .work .scratch => some .scratch | .work .zero => some .zero | _ => none
  decode_spec:=by decide +kernel

def searchBinding : FinitePortBinding DimensionSearch.Port Port where
  ports:=⟨Port.work,by intro p q h;cases h;rfl⟩
  decode:=fun p => match p with | .work p => some p | _ => none
  decode_spec:=by decide +kernel

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports:=⟨fun _ => p,fun _ _ _ => Subsingleton.elim _ _⟩
  decode:=fun q => if q=p then some 0 else none
  decode_spec:=by
    intro q i
    change (if q=p then some (0 : Fin 1) else none)=some i ↔ p=q
    fin_cases i
    simp [eq_comm]

def erasePorts : Fin 8 ↪ Port :=
  ⟨![.source,.work .square,.work .bits,.work .threshold,.work .unit,.work .zero,.work .fuel,.work .length],
    by decide +kernel⟩

def identityBinding : FinitePortBinding Port Port where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros;simp [eq_comm]

def clearPort (last : Bool) : Port := if last then .work .scratch else .extra

inductive Label
  | seed (pc : ArithmeticSeed.Label 4)
  | copy (i : Fin 4) (pc : NativeMappedCopy.Label)
  | add (pc : RepeatedAdd.Label)
  | initialErase (pc : NativeErase.Label)
  | clear (last : Bool) (pc : NativeUnprepare.Label)
  | search (pc : DimensionSearch.Label)
  | trim (pc : NativeTrim.Label)
  | erase (pc : NativeBatchErase.Label 8)
  | done
  deriving DecidableEq,Fintype

def start : Label := .seed (.pad false (.init (.erase 0)))
def afterCopy (i : Fin 4) : Label := if i=3 then .add (.counter 0) else .copy (i+1) (.init (.erase 0))

def program : Microcode.Program Port Label
  | .seed .done => .jump (.copy 0 (.init (.erase 0)))
  | .seed pc => seedBinding.instruction Label.seed (ArithmeticSeed.program 4 pc)
  | .copy i pc => if pc=.seal .done then .jump (afterCopy i)
      else (copyBinding i).instruction (Label.copy i) (NativeMappedCopy.program id pc)
  | .add pc => if pc=.counter 12 then .jump (.initialErase 2)
      else addBinding.instruction Label.add (RepeatedAdd.program pc)
  | .initialErase pc => if pc=0 then .jump (.clear false 0)
      else (singleBinding (.work .product)).instruction Label.initialErase (NativeErase.program pc)
  | .clear last pc => if pc=2 then .jump (if last then .done else .search DimensionSearch.start)
      else (singleBinding (clearPort last)).instruction (Label.clear last) (NativeUnprepare.program pc)
  | .search .done => .jump (.trim .scan)
  | .search pc => searchBinding.instruction Label.search (DimensionSearch.program pc)
  | .trim .done => .jump (.erase (NativeBatchErase.entry 8 0))
  | .trim pc => (singleBinding (.work .candidate)).instruction Label.trim (NativeTrim.program pc)
  | .erase .done => .jump (.clear true 0)
  | .erase pc => identityBinding.instruction Label.erase (NativeBatchErase.program erasePorts pc)
  | .done => .halt

theorem seed_code (pc : ArithmeticSeed.Label 4) (hh : ArithmeticSeed.program 4 pc≠.halt)
    (_ : ArithmeticSeed.program 4 pc≠.reject) :
    program (.seed pc)=MicrocodeEmbedding.instruction seedBinding.ports Label.seed (ArithmeticSeed.program 4 pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem copy_code (i : Fin 4) (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy i pc)=MicrocodeEmbedding.instruction (copyBinding i).ports (Label.copy i) (NativeMappedCopy.program id pc) := by
  have hn : pc≠.seal .done := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem add_code (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt) (_ : RepeatedAdd.program pc≠.reject) :
    program (.add pc)=MicrocodeEmbedding.instruction addBinding.ports Label.add (RepeatedAdd.program pc) := by
  have hn : pc≠.counter 12 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem initialErase_code (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt) (_ : NativeErase.program pc≠.reject) :
    program (.initialErase pc)=MicrocodeEmbedding.instruction (singleBinding (.work .product)).ports Label.initialErase (NativeErase.program pc) := by
  have hn : pc≠0 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem clear_code (last : Bool) (pc : NativeUnprepare.Label) (hh : NativeUnprepare.program pc≠.halt)
    (_ : NativeUnprepare.program pc≠.reject) :
    program (.clear last pc)=MicrocodeEmbedding.instruction (singleBinding (clearPort last)).ports
      (Label.clear last) (NativeUnprepare.program pc) := by
  have hn : pc≠2 := by intro h;subst pc;exact hh rfl
  simp only [program,hn,ite_false,FinitePortBinding.instruction_eq]

theorem search_code (pc : DimensionSearch.Label) (hh : DimensionSearch.program pc≠.halt) (_ : DimensionSearch.program pc≠.reject) :
    program (.search pc)=MicrocodeEmbedding.instruction searchBinding.ports Label.search (DimensionSearch.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem trim_code (pc : NativeTrim.Label) (hh : NativeTrim.program pc≠.halt) (_ : NativeTrim.program pc≠.reject) :
    program (.trim pc)=MicrocodeEmbedding.instruction (singleBinding (.work .candidate)).ports Label.trim (NativeTrim.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem erase_code (pc : NativeBatchErase.Label 8) (hh : NativeBatchErase.program erasePorts pc≠.halt)
    (_ : NativeBatchErase.program erasePorts pc≠.reject) :
    program (.erase pc)=MicrocodeEmbedding.instruction identityBinding.ports Label.erase (NativeBatchErase.program erasePorts pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg (pc : Label) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port Label := ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port := ⟨fun p => (s p).denote,pos⟩
abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T:=Port) start
noncomputable def nativeMachine := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=14 ∧ nativeMachine.g+1=5 ∧ nativeMachine.q+1=1327 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=14
    decide +kernel
  · change Fintype.card Label-1+1=1327
    decide +kernel

end TransposeFollowup.DimensionLoader


namespace TransposeFollowup.DimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def width (xs : List Bool) : ℕ := 2*xs.length+4
def lengthWord (xs : List Bool) : List Bool := PaddedWord.word 4 id xs

def initial (xs : List Bool) : Bank
  | .source => Counter.marked xs | _ => ⟨[],[]⟩

def seeded (xs : List Bool) : Bank := seedBinding.values (ArithmeticSeed.ready 4 xs).tapes (initial xs)

def copied (xs : List Bool) (k : ℕ) : Bank
  | .work .candidate => if 0<k then Counter.marked (ArithmeticSeed.one (width xs)) else ⟨[],[]⟩
  | .work .square => if 1<k then Counter.marked (ArithmeticSeed.one (width xs)) else ⟨[],[]⟩
  | .work .bits => if 2<k then Counter.marked (ArithmeticSeed.one (width xs)) else ⟨[],[]⟩
  | .work .threshold => if 3<k then Counter.marked (ArithmeticSeed.one (width xs)) else ⟨[],[]⟩
  | p => seeded xs p

def initialWords (xs : List Bool) : DimensionAdvance.Words :=
  let one:=ArithmeticSeed.one (width xs)
  ⟨one,one,one,RepeatedAdd.addWord one one⟩

def afterAdd (xs : List Bool) : Bank :=
  Function.update (copied xs 4) (.work .threshold) (Counter.marked (initialWords xs).threshold)
def afterErase (xs : List Bool) : Bank := Function.update (afterAdd xs) (.work .product) ⟨[],[]⟩

def searchBank (xs : List Bool) (w : DimensionAdvance.Words) : Bank
  | .work p => DimensionSearch.initial w (width xs) (lengthWord xs) p
  | .source => Counter.marked xs | .extra => ⟨[],[]⟩

def trimmed (xs : List Bool) (w : DimensionAdvance.Words) (ys : List Bool) : Bank :=
  Function.update (searchBank xs w) (.work .candidate) (Counter.marked ys)

def finalBank (ys : List Bool) : Bank
  | .work .candidate => Counter.marked ys | _ => ⟨[],[]⟩

def cleanupWords (xs : List Bool) (w : DimensionAdvance.Words) : Fin 8 → List Bool :=
  ![xs,w.square,w.bits,w.threshold,ArithmeticSeed.one (width xs),ArithmeticSeed.zeros (width xs),[true],lengthWord xs]

theorem width_positive (xs : List Bool) : 0<width xs := by unfold width;omega

theorem initial_seed (xs : List Bool) :
    seedBinding.values (ArithmeticSeed.initial xs).tapes (initial xs)=initial xs := by
  funext p
  cases p with
  | work p => cases p <;> rfl
  | _ => rfl

theorem copied_zero (xs : List Bool) : copied xs 0=seeded xs := by
  funext p
  cases p with
  | work p => cases p <;> rfl
  | _ => rfl

theorem copied_unit (xs : List Bool) (k : ℕ) :
    copied xs k (.work .unit)=Counter.marked (ArithmeticSeed.one (width xs)) := rfl

theorem copied_target (xs : List Bool) (i : Fin 4) : copied xs i.val (copyTarget i)=⟨[],[]⟩ := by
  fin_cases i <;> rfl

theorem copied_update (xs : List Bool) (i : Fin 4) :
    Function.update (copied xs i.val) (copyTarget i) (Counter.marked (ArithmeticSeed.one (width xs)))=
      copied xs (i.val+1) := by
  fin_cases i <;> funext p
  all_goals cases p with
    | work p => cases p <;> rfl
    | _ => rfl

theorem cleared_prepared (xs : List Bool) :
    Function.update (afterErase xs) .extra ⟨[],[]⟩=searchBank xs (initialWords xs) := by
  funext p
  cases p with
  | work p => cases p <;> rfl
  | _ => rfl

theorem initial_sized (xs : List Bool) : DimensionAdvance.Sized (initialWords xs) (width xs) := by
  have h := ArithmeticSeed.one_length (width xs) (width_positive xs)
  exact ⟨h,h,h,(RepeatedAdd.addWord_length _ _ rfl).trans h⟩

theorem initial_values (xs : List Bool) : DimensionAdvance.values (initialWords xs)=DimensionCandidate.canonical 1 := by
  have h := ArithmeticSeed.one_length (width xs) (width_positive xs)
  have hf : 2 < 2^width xs := lt_of_lt_of_le (by decide : 2 < 2^4)
    (Nat.pow_le_pow_right (by decide) (by unfold width;omega))
  have ha : Counter.value (RepeatedAdd.addWord (ArithmeticSeed.one (width xs)) (ArithmeticSeed.one (width xs)))=2 := by
    rw [DimensionAdvance.add_value_exact _ _ rfl (by simpa only [h,ArithmeticSeed.one_value] using hf),ArithmeticSeed.one_value]
  unfold DimensionAdvance.values initialWords DimensionCandidate.canonical
  simp only [ArithmeticSeed.one_value,ha]
  rfl

theorem lengthWord_length (xs : List Bool) : (lengthWord xs).length=width xs := PaddedWord.word_length 4 id xs

theorem lengthWord_value (xs : List Bool) : Counter.value (lengthWord xs)=Counter.value xs := by
  simpa only [lengthWord,List.map_id] using PaddedWord.word_value 4 id xs

theorem trimmed_words (xs : List Bool) (w : DimensionAdvance.Words) (ys : List Bool) (j : Fin 8) :
    trimmed xs w ys (erasePorts j)=Counter.marked (cleanupWords xs w j) := by
  fin_cases j <;> rfl

theorem erased_bank (xs : List Bool) (w : DimensionAdvance.Words) (ys : List Bool) :
    NativeBatchErase.stage erasePorts (trimmed xs w ys) 8=
      Function.update (finalBank ys) (.work .scratch) BinaryCarry.preparedOutput := by
  funext p
  cases p <;> try (rename_i q; cases q)
  all_goals simp only [NativeBatchErase.stage,Fin.exists_fin_succ,Fin.exists_fin_zero,
    erasePorts,Fin.val_zero,Fin.val_succ]
  all_goals simp [trimmed,searchBank,finalBank,DimensionSearch.initial,DimensionSearch.bank,
    DimensionAdvance.bank,Function.update]

theorem erased_scratch (ys : List Bool) :
    Function.update (Function.update (finalBank ys) (.work .scratch) BinaryCarry.preparedOutput)
      (.work .scratch) (⟨[],[]⟩ : Tape Bool)=finalBank ys := by
  funext p
  cases p with
  | work p => cases p <;> rfl
  | _ => rfl

end TransposeFollowup.DimensionLoader


namespace TransposeFollowup.DimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_seed (pc : ArithmeticSeed.Label 4) (s : ArithmeticSeed.Bank) (base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed seedBinding.ports Label.seed
      (ArithmeticSeed.cfg pc s (fun p => pos (seedPort p))) (frame base pos)=
      cfg (.seed pc) (seedBinding.values s.tapes base) pos := by
  exact seedBinding.embed_bank_project _ _ _ _ _

theorem seed_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ ArithmeticSeed.budget 4 xs, Trace t (cfg start (initial xs) pos) (cfg (.seed .done) (seeded xs) pos) := by
  obtain ⟨t,ht,htr⟩ := ArithmeticSeed.seed_trace 4 xs (width_positive xs) (fun p => pos (seedPort p))
  have he := MicrocodeEmbedding.trace_embed seedBinding.ports Label.seed (ArithmeticSeed.program 4)
    program (frame (initial xs) pos) seed_code htr
  exact ⟨t,ht,by simpa only [embed_seed,initial_seed,seeded,start] using he⟩

theorem embed_copy (i : Fin 4) (pc : NativeMappedCopy.Label) (a b : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (copyBinding i).ports (Label.copy i)
      (NativeMappedCopy.cfg pc a b (fun p => pos (copyPorts i p))) (frame s pos)=
      cfg (.copy i pc) ((copyBinding i).values (NativeMappedCopy.bank a b) s) pos := by
  exact (copyBinding i).embed_bank_project _ _ _ _ _

theorem copy_call (xs : List Bool) (i : Fin 4) (pos : Port → ℤ) :
    ∃ t ≤ 6*width xs+14, Trace t (cfg (.copy i (.init (.erase 0))) (copied xs i.val) pos)
      (cfg (.copy i (.seal .done)) (copied xs (i.val+1)) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id (ArithmeticSeed.one (width xs)) (fun p => pos (copyPorts i p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding i).ports (Label.copy i) (NativeMappedCopy.program id)
    program (frame (copied xs i.val) pos) (copy_code i) htr
  have hi : (copyBinding i).values (NativeMappedCopy.bank (Counter.marked (ArithmeticSeed.one (width xs))) ⟨[],[]⟩)
      (copied xs i.val)=copied xs i.val := by
    fin_cases i <;> funext p <;> cases p <;> try (rename_i q;cases q)
    all_goals rfl
  have hf : (copyBinding i).values (NativeMappedCopy.bank (Counter.marked (ArithmeticSeed.one (width xs)))
      (Counter.marked (ArithmeticSeed.one (width xs)))) (copied xs i.val)=copied xs (i.val+1) := by
    fin_cases i <;> funext p <;> cases p <;> try (rename_i q;cases q)
    all_goals rfl
  exact ⟨t,by simpa only [ArithmeticSeed.one_length _ (width_positive xs)] using ht,
    by simpa only [embed_copy,List.map_id,hi,hf] using he⟩

theorem embed_add (pc : RepeatedAdd.Label) (xs a : List Bool) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports Label.add
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] a (ArithmeticSeed.one (width xs))) (fun p => pos (addPort p)))
      (frame (copied xs 4) pos)=
      cfg (.add pc) (Function.update (copied xs 4) (.work .threshold) (Counter.marked a)) pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try (rename_i q;cases q)
  all_goals simp only [addBinding,FinitePortBinding.values,RepeatedAdd.ready,RepeatedAdd.Bank.tapes,
    copied,seeded,seedBinding,ArithmeticSeed.ready,
    ArithmeticSeed.Bank.tapes,Function.update,ArithmeticSeed.zeros]
  all_goals first | rfl | (rw [ArithmeticSeed.one_length _ (width_positive xs)];rfl)

theorem add_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 18*width xs+51, Trace t (cfg (.add (.counter 0)) (copied xs 4) pos)
      (cfg (.add (.counter 12)) (afterAdd xs) pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace (ArithmeticSeed.one (width xs)) (ArithmeticSeed.one (width xs))
    rfl (fun p => pos (addPort p))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports Label.add RepeatedAdd.program program
    (frame (copied xs 4) pos) add_code htr
  have hi : Function.update (copied xs 4) (.work .threshold) (Counter.marked (ArithmeticSeed.one (width xs)))=copied xs 4 :=
    Function.update_eq_self _ _
  exact ⟨t,by simpa only [ArithmeticSeed.one_length _ (width_positive xs)] using ht,
    by simpa only [embed_add,hi,afterAdd,initialWords] using he⟩

theorem embed_initialErase (pc : NativeErase.Label) (a : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding (.work .product)).ports Label.initialErase
      (NativeErase.cfg pc a (fun _ => pos (.work .product))).denote (frame s pos)=
      cfg (.initialErase pc) (Function.update s (.work .product) a) pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote Microcode.focus cfg frame
  simp only [← (singleBinding (.work .product)).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try (rename_i q;cases q)
  all_goals rfl

theorem initialErase_call (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*width xs+4, Trace t (cfg (.initialErase 2) (afterAdd xs) pos)
      (cfg (.initialErase 0) (afterErase xs) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace (ArithmeticSeed.zeros (width xs)) (fun _ => pos (.work .product))
  have he := MicrocodeEmbedding.trace_embed (singleBinding (.work .product)).ports Label.initialErase NativeErase.program
    program (frame (afterAdd xs) pos) initialErase_code htr
  have hi : Function.update (afterAdd xs) (.work .product) (Counter.marked (ArithmeticSeed.zeros (width xs)))=afterAdd xs :=
    Function.update_eq_self _ _
  exact ⟨t,by simpa only [ArithmeticSeed.zeros,List.length_replicate] using ht,
    by simpa only [embed_initialErase,hi,afterErase] using he⟩

theorem embed_clear (last : Bool) (pc : NativeUnprepare.Label) (w : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding (clearPort last)).ports (Label.clear last)
      (NativeUnprepare.cfg pc w (fun _ => pos (clearPort last))).denote (frame s pos)=
      cfg (.clear last pc) (Function.update s (clearPort last) w) pos := by
  unfold MicrocodeEmbedding.embed NativeUnprepare.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (singleBinding (clearPort last)).values_eq_extend]
  congr 2 <;> funext p <;> cases last <;> cases p <;> try (rename_i q;cases q)
  all_goals rfl

theorem clear_call (last : Bool) (s : Bank) (hs : s (clearPort last)=BinaryCarry.preparedOutput) (pos : Port → ℤ) :
    ∃ t ≤ 2, Trace t (cfg (.clear last 0) s pos)
      (cfg (.clear last 2) (Function.update s (clearPort last) ⟨[],[]⟩) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeUnprepare.complete_trace (fun _ => pos (clearPort last))
  have he := MicrocodeEmbedding.trace_embed (singleBinding (clearPort last)).ports (Label.clear last) NativeUnprepare.program
    program (frame s pos) (clear_code last) htr
  exact ⟨t,ht,by simpa only [embed_clear,← hs,Function.update_eq_self] using he⟩

theorem jump_trace (pc next : Label) (s : Bank) (pos : Port → ℤ) (hc : program pc=.jump next) :
    Trace 1 (cfg pc s pos) (cfg next s pos) :=
  NativeMicrocode.jump_trace _ _ _ hc

end TransposeFollowup.DimensionLoader


namespace TransposeFollowup.DimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

theorem embed_search (pc : DimensionSearch.Label) (xs : List Bool) (w base : DimensionAdvance.Words) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed searchBinding.ports Label.search
      (DimensionSearch.cfg pc (DimensionSearch.initial w (width xs) (lengthWord xs)) (fun p => pos (.work p)))
      (frame (searchBank xs base) pos)=cfg (.search pc) (searchBank xs w) pos := by
  unfold MicrocodeEmbedding.embed DimensionSearch.cfg cfg frame
  simp only [← searchBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem search_call (xs : List Bool) (n : ℕ) (hn : 1≤n) (hx : Counter.value xs=Transpose.inputLength n)
    (hl : xs.length=(Transpose.inputLength n).size) (pos : Port → ℤ) :
    ∃ w,DimensionAdvance.Sized w (width xs) ∧ DimensionAdvance.values w=DimensionCandidate.canonical n ∧
    ∃ t ≤ 7260*Transpose.inputLength n,
      Trace t (cfg (.search DimensionSearch.start) (searchBank xs (initialWords xs)) pos)
        (cfg (.search .done) (searchBank xs w) pos) := by
  have hm : width xs=DimensionCandidate.width (Transpose.inputLength n) := by unfold width DimensionCandidate.width;rw [hl]
  obtain ⟨w,hw,hv,t,ht,htr⟩ := DimensionSearch.complete_trace n hn (initialWords xs)
    (by rw [← hm];exact initial_sized xs) (initial_values xs) (lengthWord xs)
    ((lengthWord_length xs).trans hm) ((lengthWord_value xs).trans hx) (fun p => pos (.work p))
  rw [← hm] at hw htr
  have he := MicrocodeEmbedding.trace_embed searchBinding.ports Label.search DimensionSearch.program program
    (frame (searchBank xs (initialWords xs)) pos) search_code htr
  exact ⟨w,hw,hv,t,ht,by simpa only [embed_search] using he⟩

theorem embed_trim (pc : NativeTrim.Label) (a : Tape Bool) (s : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding (.work .candidate)).ports Label.trim
      (NativeTrim.cfg pc a (fun _ => pos (.work .candidate))).denote (frame s pos)=
      cfg (.trim pc) (Function.update s (.work .candidate) a) pos := by
  unfold MicrocodeEmbedding.embed NativeTrim.cfg NativeZipper.Config.denote Microcode.Config.denote cfg frame
  simp only [← (singleBinding (.work .candidate)).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> try (rename_i q;cases q)
  all_goals rfl

theorem trim_call (xs : List Bool) (w : DimensionAdvance.Words) (hw : DimensionAdvance.Sized w (width xs)) (pos : Port → ℤ) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=Counter.value w.candidate ∧ ys.length=(Counter.value w.candidate).size ∧
    ∃ t ≤ 4*width xs+10, Trace t (cfg (.trim .scan) (searchBank xs w) pos) (cfg (.trim .done) (trimmed xs w ys) pos) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := NativeTrim.complete_trace w.candidate (fun _ => pos (.work .candidate))
  have he := MicrocodeEmbedding.trace_embed (singleBinding (.work .candidate)).ports Label.trim NativeTrim.program program
    (frame (searchBank xs w) pos) trim_code htr
  have hi : Function.update (searchBank xs w) (.work .candidate) (Counter.marked w.candidate)=searchBank xs w :=
    Function.update_eq_self _ _
  exact ⟨ys,hy,hv,hl,t,by simpa only [hw.1] using ht,by simpa only [embed_trim,hi,trimmed] using he⟩

theorem embed_erase (pc : NativeBatchErase.Label 8) (s base : Bank) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed identityBinding.ports Label.erase (NativeBatchErase.cfg pc s pos) (frame base pos)=
      cfg (.erase pc) s pos := by
  unfold MicrocodeEmbedding.embed NativeBatchErase.cfg cfg frame
  simp only [← identityBinding.values_eq_extend]
  rfl

theorem erase_call (xs : List Bool) (w : DimensionAdvance.Words) (hw : DimensionAdvance.Sized w (width xs))
    (ys : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 4*xs.length+24*width xs+44, Trace t
      (cfg (.erase (NativeBatchErase.entry 8 0)) (trimmed xs w ys) pos)
      (cfg (.erase .done) (Function.update (finalBank ys) (.work .scratch) BinaryCarry.preparedOutput) pos) := by
  obtain ⟨t,ht,htr⟩ := NativeBatchErase.complete_trace erasePorts (cleanupWords xs w) (trimmed xs w ys)
    (trimmed_words xs w ys) pos
  have he := MicrocodeEmbedding.trace_embed identityBinding.ports Label.erase (NativeBatchErase.program erasePorts) program
    (frame (trimmed xs w ys) pos) erase_code htr
  refine ⟨t,?_,by simpa only [embed_erase,erased_bank] using he⟩
  simp only [cleanupWords,Fin.sum_univ_succ,ArithmeticSeed.zeros,ArithmeticSeed.one_length _ (width_positive xs),
    List.length_replicate,List.length_cons,List.length_nil,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,Nat.add_zero,lengthWord_length,hw.2.1,hw.2.2.1,hw.2.2.2] at ht
  omega

end TransposeFollowup.DimensionLoader


namespace TransposeFollowup.DimensionLoader
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

open NativeCountedLoop (trace_trans)

theorem initialize_trace (xs : List Bool) (pos : Port → ℤ) :
    ∃ t ≤ 46*xs.length+46*width xs+270, Trace t (cfg start (initial xs) pos)
      (cfg (.search DimensionSearch.start) (searchBank xs (initialWords xs)) pos) := by
  obtain ⟨a,ha,ta⟩ := seed_call xs pos
  rw [← copied_zero] at ta
  have ja := jump_trace (.seed .done) (.copy 0 (.init (.erase 0))) (copied xs 0) pos rfl
  obtain ⟨b,hb,tb⟩ := copy_call xs 0 pos
  have jb := jump_trace (.copy 0 (.seal .done)) (.copy 1 (.init (.erase 0))) (copied xs 1) pos rfl
  obtain ⟨c,hc,tc⟩ := copy_call xs 1 pos
  have jc := jump_trace (.copy 1 (.seal .done)) (.copy 2 (.init (.erase 0))) (copied xs 2) pos rfl
  obtain ⟨d,hd,td⟩ := copy_call xs 2 pos
  have jd := jump_trace (.copy 2 (.seal .done)) (.copy 3 (.init (.erase 0))) (copied xs 3) pos rfl
  obtain ⟨e,he,te⟩ := copy_call xs 3 pos
  have je := jump_trace (.copy 3 (.seal .done)) (.add (.counter 0)) (copied xs 4) pos rfl
  obtain ⟨f,hf,tf⟩ := add_call xs pos
  have jf := jump_trace (.add (.counter 12)) (.initialErase 2) (afterAdd xs) pos rfl
  obtain ⟨g,hg,tg⟩ := initialErase_call xs pos
  have jg := jump_trace (.initialErase 0) (.clear false 0) (afterErase xs) pos rfl
  obtain ⟨h,hh,th⟩ := clear_call false (afterErase xs) rfl pos
  simp only [show clearPort false=Port.extra from rfl,cleared_prepared] at th
  have jh := jump_trace (.clear false 2) (.search DimensionSearch.start) (searchBank xs (initialWords xs)) pos rfl
  refine ⟨a+1+b+1+c+1+d+1+e+1+f+1+g+1+h+1,?_,trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (ta) ja) tb) jb) tc) jc) td) jd) te) je) tf) jf) tg) jg) th) jh⟩
  unfold ArithmeticSeed.budget at ha
  omega

theorem finalize_trace (xs : List Bool) (w : DimensionAdvance.Words)
    (hw : DimensionAdvance.Sized w (width xs)) (pos : Port → ℤ) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=Counter.value w.candidate ∧ ys.length=(Counter.value w.candidate).size ∧
    ∃ t ≤ 4*xs.length+28*width xs+60, Trace t (cfg (.search .done) (searchBank xs w) pos)
      (cfg .done (finalBank ys) pos) := by
  have j0 := jump_trace (.search .done) (.trim .scan) (searchBank xs w) pos rfl
  obtain ⟨ys,hy,hv,hl,a,ha,ta⟩ := trim_call xs w hw pos
  have ja := jump_trace (.trim .done) (.erase (NativeBatchErase.entry 8 0)) (trimmed xs w ys) pos rfl
  obtain ⟨b,hb,tb⟩ := erase_call xs w hw ys pos
  have jb := jump_trace (.erase .done) (.clear true 0)
    (Function.update (finalBank ys) (.work .scratch) BinaryCarry.preparedOutput) pos rfl
  obtain ⟨c,hc,tc⟩ := clear_call true (Function.update (finalBank ys) (.work .scratch) BinaryCarry.preparedOutput)
    (by simp [clearPort]) pos
  simp only [show clearPort true=Port.work .scratch from rfl,erased_scratch] at tc
  have jc := jump_trace (.clear true 2) .done (finalBank ys) pos rfl
  exact ⟨ys,hy,hv,hl,1+a+1+b+1+c+1,by omega,
    trace_trans (trace_trans (trace_trans (trace_trans (trace_trans (trace_trans j0 ta) ja) tb) jb) tc) jc⟩

def budget (n : ℕ) (xs : List Bool) : ℕ := 7260*Transpose.inputLength n+50*xs.length+74*width xs+330

theorem budget_linear (xs : List Bool) (n : ℕ) (hn : 1≤n) (hl : xs.length=(Transpose.inputLength n).size) :
    budget n xs ≤ 8100*Transpose.inputLength n := by
  have hL : 1≤Transpose.inputLength n := hn.trans (DimensionCandidate.dimension_le_length n hn)
  have hs : xs.length≤Transpose.inputLength n := by rw [hl];exact Nat.size_le.mpr Nat.lt_two_pow_self
  unfold budget width
  omega

theorem complete_trace (xs : List Bool) (n : ℕ) (hn : 1≤n) (hx : Counter.value xs=Transpose.inputLength n)
    (hl : xs.length=(Transpose.inputLength n).size) (pos : Port → ℤ) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8100*Transpose.inputLength n, Trace t (cfg start (initial xs) pos) (cfg .done (finalBank ys) pos) := by
  obtain ⟨a,ha,ta⟩ := initialize_trace xs pos
  obtain ⟨w,hw,hv,b,hb,tb⟩ := search_call xs n hn hx hl pos
  obtain ⟨ys,hy,vy,ly,c,hc,tc⟩ := finalize_trace xs w hw pos
  have hvn : Counter.value w.candidate=n := congrArg DimensionCandidate.State.candidate hv
  rw [hvn] at vy ly
  have hcost : a+b+c ≤ budget n xs := by unfold budget;omega
  exact ⟨ys,hy,vy,ly,a+b+c,hcost.trans (budget_linear xs n hn hl),trace_trans (trace_trans ta tb) tc⟩

theorem native_complete (xs : List Bool) (n : ℕ) (hn : 1≤n) (hx : Counter.value xs=Transpose.inputLength n)
    (hl : xs.length=(Transpose.inputLength n).size) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8100*Transpose.inputLength n,
      Transpose.stepN nativeMachine input t ((cfg start (initial xs) pos).denote nativeEncoding program ip outRev)=
        some ((cfg .done (finalBank ys) pos).denote nativeEncoding program ip outRev) ∧
      Transpose.step nativeMachine input ((cfg .done (finalBank ys) pos).denote nativeEncoding program ip outRev)=none := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace xs n hn hx hl pos
  refine ⟨ys,hy,hv,hl,t,ht,NativeMicrocode.trace_stepN nativeEncoding program input ip outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input ip outRev _).mpr
  simp [NativeMicrocode.Active,cfg,program]

theorem native_call {U J : Type*} {k q : ℕ} (encoding : NativeMicrocode.Encoding U J k q)
    (ports : Port ↪ U) (labels : Label → J) (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject → target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (xs : List Bool) (n : ℕ) (hn : 1≤n) (hx : Counter.value xs=Transpose.inputLength n)
    (hl : xs.length=(Transpose.inputLength n).size) (pos : Port → ℤ)
    (input : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ ys,NativeTrim.Normalized ys ∧ Counter.value ys=n ∧ ys.length=n.size ∧
    ∃ t ≤ 8100*Transpose.inputLength n,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start (initial xs) pos) outerFrame).denote encoding target ip outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (finalBank ys) pos) outerFrame).denote encoding target ip outRev) := by
  obtain ⟨ys,hy,hv,hl,t,ht,htr⟩ := complete_trace xs n hn hx hl pos
  exact ⟨ys,hy,hv,hl,t,ht,MicrocodeEmbedding.native_call encoding ports labels program target outerFrame input ip outRev hc htr⟩

end TransposeFollowup.DimensionLoader
