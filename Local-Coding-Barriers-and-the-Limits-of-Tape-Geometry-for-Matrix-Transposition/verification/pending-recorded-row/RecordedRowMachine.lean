import TransposeFollowup.ReusableRow
import TransposeFollowup.PaddedWordWidth
import TransposeFollowup.InPlaceAdd
import TransposeFollowup.NativeClosedStream
import TransposeFollowup.NativeMappedCopy

/-! Eight physical tapes suffice for a reusable row consumer. Every read,
call transfer, append, index increment, rewind and cleanup is an actual
instruction. Record storage is distinct from the reusable row workspace. -/
namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | stream | index | rowIndex | unit | zero | fuel | scratch | output
  deriving DecidableEq

instance : Fintype Port where
  elems := {.stream,.index,.rowIndex,.unit,.zero,.fuel,.scratch,.output}
  complete := by intro p; cases p <;> simp

def singleBinding (p : Port) : FinitePortBinding (Fin 1) Port where
  ports := ⟨fun _ => p, fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun t => if t=p then some 0 else none
  decode_spec := by
    intro t j; fin_cases j
    change (if t=p then some (0 : Fin 1) else none)=some 0 ↔ p=t
    by_cases h : t=p
    · subst t; simp
    · simp [h,Ne.symm h]

def copyBinding : FinitePortBinding (Fin 2) Port where
  ports := ⟨![.zero,.index], by decide +kernel⟩
  decode := fun t => match t with | .zero => some 0 | .index => some 1 | _ => none
  decode_spec := by intro t j; cases t <;> fin_cases j <;> decide +kernel

def appendBinding (target : Bool) : FinitePortBinding (Fin 2) Port where
  ports := ⟨![if target then .index else .rowIndex,.output], by cases target <;> decide +kernel⟩
  decode := fun t => if t=.output then some 1
    else if t=(if target then .index else .rowIndex) then some 0 else none
  decode_spec := by intro t j; cases target <;> cases t <;> fin_cases j <;> decide +kernel

def addPort : RepeatedAdd.Port → Port
  | .fuel => .fuel | .acc => .index | .factor => .unit | .scratch => .scratch | .zero => .zero

def addBinding : FinitePortBinding RepeatedAdd.Port Port where
  ports := ⟨addPort, by intro a b h; cases a <;> cases b <;> simp_all [addPort]⟩
  decode := fun t => match t with
    | .fuel => some .fuel | .index => some .acc | .unit => some .factor
    | .scratch => some .scratch | .zero => some .zero | _ => none
  decode_spec := by intro t j; cases t <;> cases j <;> decide +kernel

inductive Label
  | rewind (pc : NativeSealBack.Label)
  | copy (pc : NativeMappedCopy.Label)
  | scan
  | append (target : Bool) (pc : Microcode.MappedAppendFamily.Label)
  | increment (pc : RepeatedAdd.Label)
  | advance
  | erase (counter : Bool) (pc : NativeErase.Label)
  | done | reject
  deriving DecidableEq, Fintype

def start : Label := .rewind .back

def program : Microcode.Program Port Label
  | .rewind pc => if pc=.done then .jump (.copy (.init (.erase 0)))
      else (singleBinding .stream).instruction Label.rewind (NativeSealBack.program pc)
  | .copy pc => if pc=.seal .done then .jump .scan
      else copyBinding.instruction Label.copy (NativeMappedCopy.program id pc)
  | .scan => .read .stream (fun s => match s with
      | .data true => .append false 0
      | .data false => .increment (.counter 0)
      | .stop => .erase false 4 | _ => .reject)
  | .append target pc => if pc=7 then
      .jump (if target then .increment (.counter 0) else .append true 0)
      else (appendBinding target).instruction (Label.append target) (Microcode.MappedAppendFamily.program id pc)
  | .increment pc => if pc=.counter 12 then .jump .advance
      else addBinding.instruction Label.increment (RepeatedAdd.program pc)
  | .advance => .act (Microcode.single .stream ⟨none,.right⟩) .scan
  | .erase counter pc => if pc=0 then .jump (if counter then .done else .erase true 2)
      else (singleBinding (if counter then .index else .stream)).instruction (Label.erase counter) (NativeErase.program pc)
  | .done => .halt
  | .reject => .reject

theorem rewind_code (pc : NativeSealBack.Label) (hh : NativeSealBack.program pc≠.halt)
    (_ : NativeSealBack.program pc≠.reject) :
    program (.rewind pc)=MicrocodeEmbedding.instruction (singleBinding .stream).ports
      Label.rewind (NativeSealBack.program pc) := by
  have h : pc≠.done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem copy_code (pc : NativeMappedCopy.Label) (hh : NativeMappedCopy.program id pc≠.halt)
    (_ : NativeMappedCopy.program id pc≠.reject) :
    program (.copy pc)=MicrocodeEmbedding.instruction copyBinding.ports
      Label.copy (NativeMappedCopy.program id pc) := by
  have h : pc≠.seal .done := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem append_code (b : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (hh : Microcode.MappedAppendFamily.program id pc≠.halt)
    (_ : Microcode.MappedAppendFamily.program id pc≠.reject) :
    program (.append b pc)=MicrocodeEmbedding.instruction (appendBinding b).ports
      (Label.append b) (Microcode.MappedAppendFamily.program id pc) := by
  have h : pc≠7 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem increment_code (pc : RepeatedAdd.Label) (hh : RepeatedAdd.program pc≠.halt)
    (_ : RepeatedAdd.program pc≠.reject) :
    program (.increment pc)=MicrocodeEmbedding.instruction addBinding.ports
      Label.increment (RepeatedAdd.program pc) := by
  have h : pc≠.counter 12 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

theorem erase_code (b : Bool) (pc : NativeErase.Label) (hh : NativeErase.program pc≠.halt)
    (_ : NativeErase.program pc≠.reject) :
    program (.erase b pc)=MicrocodeEmbedding.instruction (singleBinding (if b then .index else .stream)).ports
      (Label.erase b) (NativeErase.program pc) := by
  have h : pc≠0 := by intro h; subst pc; exact hh rfl
  simp [program,h,FinitePortBinding.instruction_eq]

structure Work where
  stream : Tape Bool
  index : Tape Bool
  pre : List (Sym Bool)

def bank (row unit : List Bool) (s : Work) : Port → Tape Bool
  | .stream => s.stream | .index => s.index | .rowIndex => Counter.marked row
  | .unit => Counter.marked unit | .zero => Counter.marked (List.replicate unit.length false)
  | .fuel => Counter.marked [true] | .scratch => BinaryCarry.preparedOutput
  | .output => ⟨s.pre,[]⟩

def cfg (pc : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ) : NativeMicrocode.Config Port Label :=
  ⟨⟨pc,fun p => (bank row unit s p).denote⟩,pos⟩

def zipperCfg (pc : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ) : NativeZipper.Config Port Label :=
  ⟨⟨pc,bank row unit s⟩,pos⟩

def frame (row unit : List Bool) (s : Work) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (bank row unit s p).denote,pos⟩

noncomputable def nativeEncoding := NativeMicrocode.initialEncoding (T := Port) start
noncomputable def nativeMachine : Transpose.TM := NativeMicrocode.machine nativeEncoding program

theorem fixed_resources : nativeMachine.k=8 ∧ nativeMachine.g+1=5 ∧
    nativeMachine.q+1=165 ∧ nativeEncoding.label start=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card Port=8
    decide +kernel
  · change Fintype.card Label-1+1=165
    decide +kernel

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem jump_trace (pc next : Label) (row unit : List Bool) (s : Work) (pos : Port → ℤ)
    (h : program pc=.jump next) : Trace 1 (cfg pc row unit s pos) (cfg next row unit s pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,cfg,h]
  · change Trace 0 (NativeMicrocode.step program (cfg pc row unit s pos)) _
    have he : NativeMicrocode.step program (cfg pc row unit s pos)=cfg next row unit s pos := by
      simp [NativeMicrocode.step,Microcode.actualStep,cfg,h]
    rw [he]; exact .refl _

theorem embed_rewind (pc : NativeSealBack.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding .stream).ports Label.rewind
      (NativeSealBack.cfg pc w (fun _ => z)).denote (frame row unit s pos)=
      cfg (.rewind pc) row unit {s with stream:=w} (Function.update pos .stream z) := by
  unfold MicrocodeEmbedding.embed NativeSealBack.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .stream).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_copy (pc : NativeMappedCopy.Label) (index : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed copyBinding.ports Label.copy
      (NativeMappedCopy.cfg pc (Counter.marked (List.replicate unit.length false)) index
        (fun t => pos (copyBinding.ports t))) (frame row unit s pos)=
      cfg (.copy pc) row unit {s with index:=index} pos := by
  unfold MicrocodeEmbedding.embed NativeMappedCopy.cfg cfg frame
  simp only [← copyBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

def sourceWord (b : Bool) (row index : List Bool) := if b then index else row

theorem embed_append (b : Bool) (pc : Microcode.MappedAppendFamily.Label)
    (row unit index : List Bool) (pre : List (Sym Bool)) (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (appendBinding b).ports (Label.append b)
      (NativeMappedAppend.cfg pc (Counter.marked (sourceWord b row index)) ⟨pre,[]⟩
        ![pos (if b then .index else .rowIndex),z]).denote
      (frame row unit {s with index:=Counter.marked index} pos)=
      cfg (.append b pc) row unit {s with index:=Counter.marked index,pre:=pre}
        (Function.update pos .output z) := by
  unfold MicrocodeEmbedding.embed NativeMappedAppend.cfg NativeZipper.Config.denote
    Microcode.Config.denote Microcode.focus2 Microcode.focus cfg frame
  simp only [← (appendBinding b).values_eq_extend]
  cases b <;> congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_increment (pc : RepeatedAdd.Label) (row unit index : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed addBinding.ports Label.increment
      (RepeatedAdd.cfg pc (RepeatedAdd.ready [true] index unit) (fun p => pos (addPort p)))
      (frame row unit s pos)=
      cfg (.increment pc) row unit {s with index:=Counter.marked index} pos := by
  unfold MicrocodeEmbedding.embed RepeatedAdd.cfg cfg frame
  simp only [← addBinding.values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_erase_stream (pc : NativeErase.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) (z : ℤ) :
    MicrocodeEmbedding.embed (singleBinding .stream).ports (Label.erase false)
      (NativeErase.cfg pc w (fun _ => z)).denote (frame row unit s pos)=
      cfg (.erase false pc) row unit {s with stream:=w} (Function.update pos .stream z) := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .stream).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem embed_erase_index (pc : NativeErase.Label) (w : Tape Bool) (row unit : List Bool)
    (s : Work) (pos : Port → ℤ) :
    MicrocodeEmbedding.embed (singleBinding .index).ports (Label.erase true)
      (NativeErase.cfg pc w (fun _ => pos .index)).denote (frame row unit s pos)=
      cfg (.erase true pc) row unit {s with index:=w} pos := by
  unfold MicrocodeEmbedding.embed NativeErase.cfg NativeZipper.Config.denote Microcode.Config.denote
    Microcode.focus cfg frame
  simp only [← (singleBinding .index).values_eq_extend]
  congr 2 <;> funext p <;> cases p <;> rfl

theorem rewind_call (row unit flags : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+4, Trace t
      (cfg (.rewind .back) row unit {s with stream:=RowStream.closedTape flags} pos)
      (cfg (.rewind .done) row unit {s with stream:=Counter.marked flags}
        (Function.update pos .stream (pos .stream-flags.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.rewind_trace flags (fun _ => pos .stream)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .stream).ports Label.rewind
    NativeSealBack.program program (frame row unit s pos) rewind_code htr
  exact ⟨t,ht,by simpa only [embed_rewind,Function.update_eq_self] using he⟩

theorem copy_call (row unit : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 6*unit.length+14, Trace t
      (cfg (.copy (.init (.erase 0))) row unit {s with index:=⟨[],[]⟩} pos)
      (cfg (.copy (.seal .done)) row unit {s with index:=Counter.marked (List.replicate unit.length false)} pos) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedCopy.copy_trace id (List.replicate unit.length false)
    (fun j => pos (copyBinding.ports j))
  have he := MicrocodeEmbedding.trace_embed copyBinding.ports Label.copy
    (NativeMappedCopy.program id) program (frame row unit s pos) copy_code htr
  exact ⟨t,by simpa using ht,by simpa only [List.map_id,embed_copy] using he⟩

theorem append_call (b : Bool) (row unit index : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 4*(sourceWord b row index).length+5, Trace t
      (cfg (.append b 0) row unit {s with index:=Counter.marked index} pos)
      (cfg (.append b 7) row unit
        {s with index:=Counter.marked index,pre:=(symbols (sourceWord b row index)).reverse++s.pre}
        (Function.update pos .output (pos .output+(sourceWord b row index).length))) := by
  obtain ⟨t,ht,htr⟩ := NativeMappedAppend.append_trace id (sourceWord b row index) s.pre
    ![pos (if b then .index else .rowIndex),pos .output]
  have he := MicrocodeEmbedding.trace_embed (appendBinding b).ports (Label.append b)
    (Microcode.MappedAppendFamily.program id) program
    (frame row unit {s with index:=Counter.marked index} pos) (append_code b) htr
  have hpos : NativeMappedAppend.finalPositions
      ![pos (if b then .index else .rowIndex),pos .output] (sourceWord b row index).length=
      ![pos (if b then .index else .rowIndex),pos .output+(sourceWord b row index).length] := by
    funext j; fin_cases j <;> simp [NativeMappedAppend.finalPositions]
  rw [hpos] at he
  exact ⟨t,ht,by simpa only [List.map_id,embed_append,Function.update_eq_self] using he⟩

theorem increment_call (row unit index : List Bool) (h : index.length=unit.length)
    (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 18*unit.length+51, Trace t
      (cfg (.increment (.counter 0)) row unit {s with index:=Counter.marked index} pos)
      (cfg (.increment (.counter 12)) row unit {s with index:=Counter.marked (RepeatedAdd.addWord index unit)} pos) := by
  obtain ⟨t,ht,htr⟩ := RepeatedAdd.single_add_trace index unit h (fun p => pos (addPort p))
  have he := MicrocodeEmbedding.trace_embed addBinding.ports Label.increment
    RepeatedAdd.program program (frame row unit s pos) increment_code htr
  exact ⟨t,ht,by simpa only [embed_increment] using he⟩

theorem erase_stream_call (row unit flags : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+3, Trace t
      (cfg (.erase false 4) row unit {s with stream:=RowStream.closedTape flags} pos)
      (cfg (.erase false 0) row unit {s with stream:=⟨[],[]⟩}
        (Function.update pos .stream (pos .stream-flags.length))) := by
  obtain ⟨t,ht,htr⟩ := NativeClosedStream.erase_trace flags (fun _ => pos .stream)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .stream).ports (Label.erase false)
    NativeErase.program program (frame row unit s pos) (erase_code false) htr
  exact ⟨t,ht,by simpa only [embed_erase_stream,Function.update_eq_self] using he⟩

theorem erase_index_call (row unit index : List Bool) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 4*index.length+4, Trace t
      (cfg (.erase true 2) row unit {s with index:=Counter.marked index} pos)
      (cfg (.erase true 0) row unit {s with index:=⟨[],[]⟩} pos) := by
  obtain ⟨t,ht,htr⟩ := NativeErase.erase_trace index (fun _ => pos .index)
  have he := MicrocodeEmbedding.trace_embed (singleBinding .index).ports (Label.erase true)
    NativeErase.program program (frame row unit s pos) (erase_code true) htr
  exact ⟨t,ht,by simpa only [embed_erase_index] using he⟩

end TransposeFollowup.RowConsumer


/-! Specification of the paid row consumer: true flags select fixed-width
pairs, and a real repeated-addition word is advanced once per input flag.
No arithmetic operation here is charged as a primitive machine step. -/
namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

def targets : List Bool → ℕ → List ℕ
  | [], _ => []
  | b::bs, j => (if b then [j] else []) ++ targets bs (j+1)

def records (row unit : List Bool) : List Bool → List Bool → List (List Bool × List Bool)
  | [], _ => []
  | b::bs, j => (if b then [(row,j)] else []) ++ records row unit bs (RepeatedAdd.addWord j unit)

def encoded (row unit flags j : List Bool) : List Bool :=
  (records row unit flags j).flatMap (fun p => p.1 ++ p.2)

def after (unit flags j : List Bool) : List Bool := RepeatedAdd.repeatWord unit flags.length j

theorem records_length (row unit flags j : List Bool) :
    (records row unit flags j).length = flags.count true := by
  induction flags generalizing j with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [records,ih]

theorem records_width (row unit flags j : List Bool) (hr : row.length=unit.length)
    (hj : j.length=unit.length) :
    ∀ p ∈ records row unit flags j, p.1.length=unit.length ∧ p.2.length=unit.length := by
  induction flags generalizing j with
  | nil => simp [records]
  | cons b bs ih =>
    cases b <;> simp only [records, Bool.false_eq_true, ↓reduceIte, List.nil_append,
      List.singleton_append, List.mem_cons, forall_eq_or_imp]
    · exact ih _ (RepeatedAdd.addWord_length j unit hj)
    · exact ⟨⟨hr,hj⟩, ih _ (RepeatedAdd.addWord_length j unit hj)⟩

theorem encoded_length (row unit flags j : List Bool) (hr : row.length=unit.length)
    (hj : j.length=unit.length) :
    (encoded row unit flags j).length=2*unit.length*(flags.count true) := by
  induction flags generalizing j with
  | nil => simp [encoded,records]
  | cons b bs ih =>
    have h := ih _ (RepeatedAdd.addWord_length j unit hj)
    cases b <;> simp [encoded,records] at h ⊢
    · exact h
    · rw [h,hr,hj]
      simp only [Nat.mul_add,Nat.mul_one]
      omega

theorem records_values (row unit flags j : List Bool) (hj : j.length=unit.length)
    (hu : BinaryCompare.value unit=1)
    (hfit : BinaryCompare.value j+flags.length<2^unit.length) :
    (records row unit flags j).map (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets flags (BinaryCompare.value j)).map (fun k => (BinaryCompare.value row,k)) := by
  induction flags generalizing j with
  | nil => rfl
  | cons b bs ih =>
    have hv : BinaryCompare.value (RepeatedAdd.addWord j unit)=BinaryCompare.value j+1 := by
      rw [RepeatedAdd.addWord_value j unit hj,hu,Nat.mod_eq_of_lt (by simp only [List.length_cons] at hfit; omega)]
    have hh : BinaryCompare.value (RepeatedAdd.addWord j unit)+bs.length<2^unit.length := by
      rw [hv]; simp only [List.length_cons] at hfit; omega
    have h := ih _ (RepeatedAdd.addWord_length j unit hj) hh
    rw [hv] at h
    cases b <;> simpa [records,targets] using h

theorem after_length (unit flags j : List Bool) (hj : j.length=unit.length) :
    (after unit flags j).length=unit.length := RepeatedAdd.repeatWord_length _ _ _ hj

theorem after_value (unit flags j : List Bool) (hj : j.length=unit.length)
    (hu : BinaryCompare.value unit=1)
    (hfit : BinaryCompare.value j+flags.length<2^unit.length) :
    BinaryCompare.value (after unit flags j)=BinaryCompare.value j+flags.length := by
  simpa only [after,hu,Nat.mul_one] using RepeatedAdd.repeatWord_value_exact unit flags.length j hj
    (by simpa only [hu,Nat.mul_one] using hfit)

theorem targets_bounds (flags : List Bool) (j k : ℕ) (h : k ∈ targets flags j) :
    j ≤ k ∧ k<j+flags.length := by
  induction flags generalizing j with
  | nil => simp [targets] at h
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [targets,Bool.false_eq_true,↓reduceIte,List.nil_append] at h
      obtain ⟨hl,hr⟩ := ih (j+1) h
      simp only [List.length_cons]; omega
    | true =>
      simp only [targets,↓reduceIte,List.singleton_append,List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · obtain ⟨hl,hr⟩ := ih (j+1) h
        simp only [List.length_cons]; omega

theorem targets_nodup (flags : List Bool) (j : ℕ) : (targets flags j).Nodup := by
  induction flags generalizing j with
  | nil => simp [targets]
  | cons b bs ih =>
    cases b with
    | false => simpa [targets] using ih (j+1)
    | true =>
      simp only [targets,↓reduceIte,List.singleton_append,List.nodup_cons]
      exact ⟨fun h => by have := (targets_bounds bs (j+1) j h).1; omega,ih (j+1)⟩

theorem targets_map_range (f : ℕ → Bool) (n j : ℕ) :
    targets ((List.range n).map f) j =
      (List.range n).filterMap (fun k => if f k then some (j+k) else none) := by
  induction n generalizing f j with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map,List.map_cons,List.map_map,targets]
    rw [ih]
    cases h : f 0 <;> simp [h,List.filterMap_map,Nat.add_comm,Nat.add_left_comm]

theorem mem_targets_range (f : ℕ → Bool) (n k : ℕ) :
    k ∈ targets ((List.range n).map f) 0 ↔ k<n ∧ f k=true := by
  rw [targets_map_range]
  simp only [Nat.zero_add,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    split_ifs at h with hb
    · have he : j=k := Option.some.inj h
      subst j; exact ⟨hj,hb⟩
  · rintro ⟨hk,hf⟩
    exact ⟨k,hk,by simp [hf]⟩

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

def cursor (before todo : List Bool) : Tape Bool :=
  ⟨(symbols before).reverse++[.start],symbols todo++[.stop]⟩

def work (before todo index : List Bool) (pre : List (Sym Bool)) : Work :=
  ⟨cursor before todo,Counter.marked index,pre⟩

def emitted (b : Bool) (row index : List Bool) : List Bool := if b then row++index else []

def positions (pos : Port → ℤ) (r o : ℤ) : Port → ℤ :=
  fun p => pos p + if p=.stream then r else if p=.output then o else 0

theorem positions_zero (pos : Port → ℤ) : positions pos 0 0=pos := by
  funext p; cases p <;> simp [positions]

theorem positions_add (pos : Port → ℤ) (r o r' o' : ℤ) :
    positions (positions pos r o) r' o'=positions pos (r+r') (o+o') := by
  funext p; cases p <;> simp [positions,add_assoc]

theorem positions_output (pos : Port → ℤ) (o : ℤ) :
    Function.update pos .output (pos .output+o)=positions pos 0 o := by
  funext p; cases p <;> simp [positions]

theorem cursor_initial (xs : List Bool) : cursor [] xs=Counter.marked xs := rfl

theorem cursor_final (xs : List Bool) : cursor xs []=RowStream.closedTape xs := by
  simp [cursor,RowStream.closedTape,symbols,List.map_reverse]

theorem cursor_advance (before todo : List Bool) (b : Bool) :
    (cursor before (b::todo)).moveRight=cursor (before++[b]) todo := by
  simp [cursor,Tape.moveRight,Tape.read,symbols,List.reverse_append]

theorem encoded_cons (row unit index bs : List Bool) (b : Bool) :
    encoded row unit (b::bs) index = emitted b row index ++
      encoded row unit bs (RepeatedAdd.addWord index unit) := by
  cases b <;> simp [encoded,records,emitted]

theorem after_cons (unit index bs : List Bool) (b : Bool) :
    after unit (b::bs) index=after unit bs (RepeatedAdd.addWord index unit) := rfl

theorem one_step (pc next : Label) (row unit : List Bool) (s z : Work)
    (pos pos' : Port → ℤ) (ha : program pc≠.halt ∧ program pc≠.reject)
    (he : NativeZipper.step program (zipperCfg pc row unit s pos)=zipperCfg next row unit z pos') :
    Trace 1 (cfg pc row unit s pos) (cfg next row unit z pos') := by
  have h := congrArg NativeZipper.Config.denote he
  rw [NativeZipper.step_denote] at h
  change NativeMicrocode.step program (cfg pc row unit s pos)=cfg next row unit z pos' at h
  apply OperationalTrace.Trace.cons
  · exact ha
  · rw [h]; exact .refl _

theorem read_flag (row unit before todo index : List Bool) (b : Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .scan row unit (work before (b::todo) index pre) pos)
      (cfg (if b then .append false 0 else .increment (.counter 0)) row unit
        (work before (b::todo) index pre) pos) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · cases b <;> simp [NativeZipper.step,Microcode.step,program,zipperCfg,bank,work,cursor,Tape.read,symbols]

theorem read_stop (row unit before index : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .scan row unit (work before [] index pre) pos)
      (cfg (.erase false 4) row unit (work before [] index pre) pos) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · simp [NativeZipper.step,Microcode.step,program,zipperCfg,bank,work,cursor,Tape.read,symbols]

theorem advance_tapes (row unit before todo index : List Bool) (b : Bool) (pre : List (Sym Bool)) :
    (fun p => (Microcode.single Port.stream ⟨none,.right⟩ p).apply
      (bank row unit (work before (b::todo) index pre) p))=
      bank row unit (work (before++[b]) todo index pre) := by
  funext p; cases p <;> try rfl
  exact cursor_advance before todo b

theorem advance_positions (pos : Port → ℤ) :
    (fun p => (NativeMicrocode.direction (Microcode.single Port.stream ⟨none,.right⟩ p).move).shift (pos p))=
      positions pos 1 0 := by
  funext p; cases p <;> simp [positions,Microcode.single,NativeMicrocode.direction,Transpose.Dir.shift]

theorem advance_trace (row unit before todo index : List Bool) (b : Bool)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    Trace 1 (cfg .advance row unit (work before (b::todo) index pre) pos)
      (cfg .scan row unit (work (before++[b]) todo index pre) (positions pos 1 0)) := by
  apply one_step
  · exact ⟨by simp [program],by simp [program]⟩
  · simp only [NativeZipper.step,Microcode.step,program,zipperCfg,advance_tapes,advance_positions]

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem append_pair (row unit index : List Bool) (hr : row.length=unit.length)
    (hj : index.length=unit.length) (s : Work) (pos : Port → ℤ) :
    ∃ t ≤ 8*unit.length+12, Trace t
      (cfg (.append false 0) row unit {s with index:=Counter.marked index} pos)
      (cfg (.increment (.counter 0)) row unit
        {s with index:=Counter.marked index,pre:=(symbols (row++index)).reverse++s.pre}
        (positions pos 0 (row.length+index.length))) := by
  obtain ⟨a,ha,ta⟩ := append_call false row unit index s pos
  simp only [sourceWord,Bool.false_eq_true,↓reduceIte,positions_output] at ha ta
  let s1 : Work := {s with index:=Counter.marked index,pre:=(symbols row).reverse++s.pre}
  let p1 := positions pos 0 row.length
  have ja := jump_trace (.append false 7) (.append true 0) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := append_call true row unit index s1 p1
  simp only [sourceWord,↓reduceIte,positions_output] at hb tb
  let s2 : Work := {s1 with index:=Counter.marked index,pre:=(symbols index).reverse++s1.pre}
  let p2 := positions p1 0 index.length
  have jb := jump_trace (.append true 7) (.increment (.counter 0)) row unit s2 p2 rfl
  have whole := trace_trans (trace_trans (trace_trans ta ja) tb) jb
  refine ⟨a+1+b+1,by omega,?_⟩
  simpa only [s1,s2,p1,p2,positions_add,add_zero,symbols,List.map_append,List.reverse_append,List.append_assoc] using whole

theorem flag_trace (row unit before todo index : List Bool) (b : Bool)
    (hr : row.length=unit.length) (hj : index.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 18*unit.length+54+(if b then 8*unit.length+12 else 0), Trace t
      (cfg .scan row unit (work before (b::todo) index pre) pos)
      (cfg .scan row unit (work (before++[b]) todo (RepeatedAdd.addWord index unit)
        ((symbols (emitted b row index)).reverse++pre))
        (positions pos 1 (emitted b row index).length)) := by
  let s := work before (b::todo) index pre
  have rd := read_flag row unit before todo index b pre pos
  cases b with
  | false =>
    obtain ⟨a,ha,ta⟩ := increment_call row unit index hj s pos
    let s1 := work before (false::todo) (RepeatedAdd.addWord index unit) pre
    have ja := jump_trace (.increment (.counter 12)) .advance row unit s1 pos rfl
    have mv := advance_trace row unit before todo (RepeatedAdd.addWord index unit) false pre pos
    have whole := trace_trans (trace_trans (trace_trans rd ta) ja) mv
    exact ⟨1+a+1+1,by simp; omega,by simpa only [emitted,Bool.false_eq_true,↓reduceIte,symbols,
      List.map_nil,List.reverse_nil,List.nil_append,List.length_nil,Nat.cast_zero] using whole⟩
  | true =>
    obtain ⟨a,ha,ta⟩ := append_pair row unit index hr hj s pos
    let pre1 := (symbols (row++index)).reverse++pre
    let s1 := work before (true::todo) index pre1
    let p1 := positions pos 0 (row.length+index.length)
    obtain ⟨c,hc,tc⟩ := increment_call row unit index hj s1 p1
    let s2 := work before (true::todo) (RepeatedAdd.addWord index unit) pre1
    have jc := jump_trace (.increment (.counter 12)) .advance row unit s2 p1 rfl
    have mv := advance_trace row unit before todo (RepeatedAdd.addWord index unit) true pre1 p1
    have whole := trace_trans (trace_trans (trace_trans (trace_trans rd ta) tc) jc) mv
    refine ⟨1+a+c+1+1,by simp; omega,?_⟩
    simpa only [emitted,↓reduceIte,pre1,p1,positions_add,zero_add,add_zero,List.length_append,Nat.cast_add] using whole

def loopBudget (m : ℕ) (flags : List Bool) : ℕ :=
  flags.length*(18*m+54)+flags.count true*(8*m+12)

theorem loop_trace (row unit before flags index : List Bool) (hr : row.length=unit.length)
    (hj : index.length=unit.length) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ loopBudget unit.length flags, Trace t
      (cfg .scan row unit (work before flags index pre) pos)
      (cfg .scan row unit (work (before++flags) [] (after unit flags index)
        ((symbols (encoded row unit flags index)).reverse++pre))
        (positions pos flags.length (encoded row unit flags index).length)) := by
  induction flags generalizing before index pre pos with
  | nil =>
    refine ⟨0,by simp [loopBudget],?_⟩
    simpa only [after,RepeatedAdd.repeatWord,encoded,records,List.flatMap_nil,symbols,List.map_nil,
      List.reverse_nil,List.nil_append,List.append_nil,List.length_nil,Nat.cast_zero,positions_zero] using
      (OperationalTrace.Trace.refl (cfg .scan row unit (work before [] index pre) pos) : Trace 0 _ _)
  | cons b bs ih =>
    obtain ⟨a,ha,ta⟩ := flag_trace row unit before bs index b hr hj pre pos
    obtain ⟨c,hc,tc⟩ := ih (before++[b]) (RepeatedAdd.addWord index unit)
      (RepeatedAdd.addWord_length index unit hj) ((symbols (emitted b row index)).reverse++pre)
      (positions pos 1 (emitted b row index).length)
    refine ⟨a+c,?_,?_⟩
    · cases b <;> simp [loopBudget] at ha hc ⊢ <;> nlinarith
    · have whole := trace_trans ta tc
      simpa only [encoded_cons,after_cons,positions_add,List.length_cons,Nat.cast_add,Nat.cast_one,
        symbols,List.map_append,List.reverse_append,List.append_assoc,List.singleton_append,List.length_append,
        add_comm] using whole

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false

theorem positions_stream (pos : Port → ℤ) (r : ℤ) :
    Function.update pos .stream (pos .stream+r)=positions pos r 0 := by
  funext p; cases p <;> simp [positions]

def initial (flags : List Bool) (pre : List (Sym Bool)) : Work :=
  ⟨RowStream.closedTape flags,⟨[],[]⟩,pre⟩

def final (pre : List (Sym Bool)) : Work := ⟨⟨[],[]⟩,⟨[],[]⟩,pre⟩

def zeroWord (unit : List Bool) := List.replicate unit.length false

def output (row unit flags : List Bool) := encoded row unit flags (zeroWord unit)

def budget (m : ℕ) (flags : List Bool) : ℕ :=
  flags.length*(18*m+58)+flags.count true*(8*m+12)+10*m+30

theorem prepare_trace (row unit flags : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+6*unit.length+20, Trace t
      (cfg start row unit (initial flags pre) pos)
      (cfg .scan row unit (work [] flags (zeroWord unit) pre)
        (positions pos (-(flags.length : ℤ)) 0)) := by
  obtain ⟨a,ha,ta⟩ := rewind_call row unit flags (initial flags pre) pos
  simp only [sub_eq_add_neg,positions_stream] at ta
  let s1 : Work := ⟨Counter.marked flags,⟨[],[]⟩,pre⟩
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have ja := jump_trace (.rewind .done) (.copy (.init (.erase 0))) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := copy_call row unit s1 p1
  let s2 : Work := ⟨Counter.marked flags,Counter.marked (zeroWord unit),pre⟩
  have jb := jump_trace (.copy (.seal .done)) .scan row unit s2 p1 rfl
  exact ⟨a+1+b+1,by omega,trace_trans (trace_trans (trace_trans ta ja) tb) jb⟩

theorem finish_trace (row unit flags index : List Bool) (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ 2*flags.length+4*index.length+10, Trace t
      (cfg .scan row unit (work flags [] index pre) pos)
      (cfg .done row unit (final pre) (positions pos (-(flags.length : ℤ)) 0)) := by
  have rd := read_stop row unit flags index pre pos
  let s0 := work flags [] index pre
  obtain ⟨a,ha,ta⟩ := erase_stream_call row unit flags s0 pos
  have hs : {s0 with stream:=RowStream.closedTape flags}=s0 := by simp [s0,work,cursor_final]
  rw [hs] at ta
  simp only [sub_eq_add_neg,positions_stream] at ta
  let s1 : Work := ⟨⟨[],[]⟩,Counter.marked index,pre⟩
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have ja := jump_trace (.erase false 0) (.erase true 2) row unit s1 p1 rfl
  obtain ⟨b,hb,tb⟩ := erase_index_call row unit index s1 p1
  have jb := jump_trace (.erase true 0) .done row unit (final pre) p1 rfl
  exact ⟨1+a+1+b+1,by omega,trace_trans (trace_trans (trace_trans (trace_trans rd ta) ja) tb) jb⟩

theorem complete_trace (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) :
    ∃ t ≤ budget unit.length flags, Trace t
      (cfg start row unit (initial flags pre) pos)
      (cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
        (positions pos (-(flags.length : ℤ)) (output row unit flags).length)) := by
  obtain ⟨a,ha,ta⟩ := prepare_trace row unit flags pre pos
  let p1 := positions pos (-(flags.length : ℤ)) 0
  have hz : (zeroWord unit).length=unit.length := List.length_replicate ..
  obtain ⟨b,hb,tb⟩ := loop_trace row unit [] flags (zeroWord unit) hr hz pre p1
  simp only [List.nil_append] at tb
  let pre1 := (symbols (output row unit flags)).reverse++pre
  let p2 := positions p1 flags.length (output row unit flags).length
  obtain ⟨c,hc,tc⟩ := finish_trace row unit flags (after unit flags (zeroWord unit)) pre1 p2
  rw [after_length unit flags (zeroWord unit) hz] at hc
  have whole := trace_trans (trace_trans ta tb) tc
  refine ⟨a+b+c,?_,?_⟩
  · unfold budget loopBudget at *
    nlinarith
  · simpa only [p1,p2,pre1,positions_add,neg_add_cancel,zero_add,add_zero] using whole

theorem budget_le (m : ℕ) (flags : List Bool) :
    budget m flags ≤ flags.length*(26*m+70)+10*m+30 := by
  have h := List.count_le_length (l:=flags) (a:=true)
  unfold budget
  nlinarith

theorem output_length (row unit flags : List Bool) (hr : row.length=unit.length) :
    (output row unit flags).length=2*unit.length*(flags.count true) :=
  encoded_length row unit flags (zeroWord unit) hr (List.length_replicate ..)

theorem native_complete (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget unit.length flags,
      Transpose.stepN nativeMachine input t
        ((cfg start row unit (initial flags pre) pos).denote nativeEncoding program inputPos outRev)=
        some ((cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
          (positions pos (-(flags.length : ℤ)) (output row unit flags).length)).denote
          nativeEncoding program inputPos outRev) ∧
      Transpose.step nativeMachine input
        ((cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
          (positions pos (-(flags.length : ℤ)) (output row unit flags).length)).denote
          nativeEncoding program inputPos outRev)=none := by
  obtain ⟨t,ht,htr⟩ := complete_trace row unit flags hr pre pos
  refine ⟨t,ht,NativeMicrocode.trace_stepN nativeEncoding program input inputPos outRev htr,?_⟩
  apply (NativeMicrocode.step_none_iff nativeEncoding program input inputPos outRev _).mpr
  intro h; exact h.1 rfl

theorem native_call {U J : Type*} {k q : ℕ}
    (encoding : NativeMicrocode.Encoding U J k q) (ports : Port ↪ U) (labels : Label → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pc≠.halt → program pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pc))
    (row unit flags : List Bool) (hr : row.length=unit.length)
    (pre : List (Sym Bool)) (pos : Port → ℤ) (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ t ≤ budget unit.length flags,
      Transpose.stepN (NativeMicrocode.machine encoding target) input t
        ((MicrocodeEmbedding.embed ports labels (cfg start row unit (initial flags pre) pos) outerFrame).denote
          encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels
          (cfg .done row unit (final ((symbols (output row unit flags)).reverse++pre))
            (positions pos (-(flags.length : ℤ)) (output row unit flags).length)) outerFrame).denote
          encoding target inputPos outRev) := by
  obtain ⟨t,ht,htr⟩ := complete_trace row unit flags hr pre pos
  exact ⟨t,ht,MicrocodeEmbedding.native_call encoding ports labels program target
    outerFrame input inputPos outRev hc htr⟩

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RowConsumer
open FixedTapeCompiler
set_option autoImplicit false

theorem values_zero (row unit flags : List Bool) (hu : BinaryCompare.value unit=1)
    (hfit : flags.length<2^unit.length) :
    (records row unit flags (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets flags 0).map (fun j => (BinaryCompare.value row,j)) := by
  simpa only [zeroWord,RepeatedAdd.zero_value,Nat.zero_add] using
    records_values row unit flags (zeroWord unit) (List.length_replicate ..) hu
      (by simpa only [zeroWord,RepeatedAdd.zero_value,Nat.zero_add] using hfit)

theorem dense_targets (F : RationalMobius) {N : ℕ} (i j : Fin N) :
    j.val ∈ targets (F.denseRow i) 0 ↔ j ∈ F.neighbors i := by
  rw [F.denseRow_eq_range,mem_targets_range,F.mem_neighbors]
  exact (and_iff_right j.isLt).trans (F.denseHit_spec i j)

theorem dense_record_values (F : RationalMobius) {N : ℕ} (i : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    (records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) =
      (targets (F.denseRow i) 0).map (fun j => (i.val,j)) := by
  simpa only [hi] using values_zero row unit (F.denseRow i) hu (by simpa only [F.denseRow_length] using hfit)

theorem dense_record_mem (F : RationalMobius) {N : ℕ} (i j : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    (i.val,j.val) ∈ (records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2)) ↔ j ∈ F.neighbors i := by
  rw [dense_record_values F i row unit hu hi hfit]
  simpa only [List.mem_map,Prod.mk.injEq,true_and,exists_eq_right] using dense_targets F i j

theorem dense_record_nodup (F : RationalMobius) {N : ℕ} (i : Fin N)
    (row unit : List Bool) (hu : BinaryCompare.value unit=1)
    (hi : BinaryCompare.value row=i.val) (hfit : N<2^unit.length) :
    ((records row unit (F.denseRow i) (zeroWord unit)).map
      (fun p => (BinaryCompare.value p.1,BinaryCompare.value p.2))).Nodup := by
  rw [dense_record_values F i row unit hu hi hfit]
  exact (targets_nodup (F.denseRow i) 0).map (fun _ _ h => congrArg Prod.snd h)

theorem common_index_fit (F : RationalMobius) (source : List Bool) :
    Counter.value source<2^(PaddedWord.word (PaddedWord.commonConstant F) id source).length := by
  rw [← PaddedWord.common_value F source,NativeCounter.word_value]
  exact BinaryCarry.value_lt _

theorem total_budget (F : RationalMobius) (N : ℕ) (source flags : List Bool)
    (hN : 1 ≤ N) (hl : source.length ≤ (N+1).size) (hf : flags.length=N) :
    N*budget (PaddedWord.word (PaddedWord.commonConstant F) id source).length flags ≤
      (72*(F.integerOperandConstant^2).size+920)*Transpose.inputLength N := by
  let m := (PaddedWord.word (PaddedWord.commonConstant F) id source).length
  have hc := budget_le m flags
  rw [hf] at hc
  have hmore : 10*m+30 ≤ N*(10*m+30) := Nat.le_mul_of_pos_left _ hN
  have hstep : budget m flags ≤ N*(36*m+100) := by nlinarith
  have hm : 36*m+100 ≤ (36*PaddedWord.commonConstant F+100)+72*(N+1).size := by
    dsimp [m]; rw [PaddedWord.word_length]; omega
  have h := dense_scan_budget (36*PaddedWord.commonConstant F+100) 72 N hN
  have he : 2*(36*PaddedWord.commonConstant F+100+3*72)=72*(F.integerOperandConstant^2).size+920 := by
    unfold PaddedWord.commonConstant; ring
  calc
    _ ≤ N*(N*(36*m+100)) := Nat.mul_le_mul_left _ hstep
    _ ≤ N*(N*((36*PaddedWord.commonConstant F+100)+72*(N+1).size)) := by gcongr
    _ ≤ _ := by simpa only [he] using h

end TransposeFollowup.RowConsumer

namespace TransposeFollowup.RecordedRow
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

inductive Port | row (p : RowExecution.Port) | output
  deriving DecidableEq, Fintype

def rowBinding : FinitePortBinding RowExecution.Port Port where
  ports := ⟨Port.row,fun _ _ h => Port.row.inj h⟩
  decode := fun p => match p with | .row t => some t | .output => none
  decode_spec := by
    intro p t
    change (match p with | .row u => some u | .output => none)=some t ↔ Port.row t=p
    cases p <;> simp [eq_comm]

def consumerPort : RowConsumer.Port → Port
  | .stream => .row .stream | .index => .row .counter
  | .rowIndex => .row (.prep (.images (.source (.shared .index))))
  | .unit => .row (.prep (.images (.source (.shared .unit))))
  | .zero => .row (.prep (.images (.source (.shared .zero))))
  | .fuel => .row (.prep (.images (.source (.shared .fuel))))
  | .scratch => .row (.prep (.images (.source (.shared .scratch))))
  | .output => .output

def consumerBinding : FinitePortBinding RowConsumer.Port Port where
  ports := ⟨consumerPort,by decide +kernel⟩
  decode := fun p => match p with
    | .row .stream => some .stream | .row .counter => some .index
    | .row (.prep (.images (.source (.shared .index)))) => some .rowIndex
    | .row (.prep (.images (.source (.shared .unit)))) => some .unit
    | .row (.prep (.images (.source (.shared .zero)))) => some .zero
    | .row (.prep (.images (.source (.shared .fuel)))) => some .fuel
    | .row (.prep (.images (.source (.shared .scratch)))) => some .scratch
    | .output => some .output | _ => none
  decode_spec := by decide +kernel

inductive Label (F : RationalMobius)
  | row (pc : ReusableRow.Label F)
  | consume (saved : Bool) (pc : RowConsumer.Label)
  | done (saved : Bool)
  deriving DecidableEq, Fintype

def start (F : RationalMobius) : Label F := .row (ReusableRow.start F)

def program (F : RationalMobius) : Microcode.Program Port (Label F)
  | .row (.done saved) => .jump (.consume saved RowConsumer.start)
  | .row pc => rowBinding.instruction Label.row (ReusableRow.program F pc)
  | .consume saved .done => .jump (.done saved)
  | .consume saved pc => consumerBinding.instruction (Label.consume saved) (RowConsumer.program pc)
  | .done _ => .halt

theorem row_code (F : RationalMobius) (pc : ReusableRow.Label F)
    (hh : ReusableRow.program F pc≠.halt) (_ : ReusableRow.program F pc≠.reject) :
    program F (.row pc)=MicrocodeEmbedding.instruction rowBinding.ports Label.row (ReusableRow.program F pc) := by
  cases pc <;> try exact rowBinding.instruction_eq _ _
  exact False.elim (hh rfl)

theorem consumer_code (F : RationalMobius) (saved : Bool) (pc : RowConsumer.Label)
    (hh : RowConsumer.program pc≠.halt) (_ : RowConsumer.program pc≠.reject) :
    program F (.consume saved pc)=MicrocodeEmbedding.instruction consumerBinding.ports
      (Label.consume saved) (RowConsumer.program pc) := by
  cases pc <;> simp_all only [program,FinitePortBinding.instruction_eq,RowConsumer.program]
  exact False.elim (hh rfl)


abbrev Bank := Port → Tape Bool

def liftBank (b : RowExecution.Bank) (pre : List (Sym Bool)) : Bank
  | .row p => b p | .output => ⟨pre,[]⟩

def initial (n iw : List Bool) (pre : List (Sym Bool)) := liftBank (RowExecution.initial n iw) pre

def consumerBank (n iw : List Bool) (w : RowConsumer.Work) : Bank :=
  consumerBinding.values (RowConsumer.bank iw (ArithmeticSeed.one n.length) w) (initial n iw w.pre)

def cfg {F : RationalMobius} (pc : Label F) (s : Bank) (pos : Port → ℤ) : NativeMicrocode.Config Port (Label F) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩

def frame (s : Bank) (pos : Port → ℤ) : MicrocodeEmbedding.Frame Port :=
  ⟨fun p => (s p).denote,pos⟩

def rowPositions (pos : Port → ℤ) (flags : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.row .stream then (flags.length : ℤ) else 0

def finalPositions (pos : Port → ℤ) (bits : List Bool) : Port → ℤ :=
  fun p => pos p+if p=.output then (bits.length : ℤ) else 0

abbrev Trace (F : RationalMobius) := OperationalTrace.Trace (NativeMicrocode.step (program F)) (NativeMicrocode.Active (program F))

theorem consumer_initial (n iw flags : List Bool) (hm : 0<n.length) (pre : List (Sym Bool)) :
    consumerBank n iw (RowConsumer.initial flags pre)=
      liftBank (RowCleanup.retainedRow n iw (RowStream.closedTape flags)) pre := by
  funext p
  fin_cases p <;>
    simp only [consumerBank,consumerBinding,FinitePortBinding.values,RowConsumer.bank,RowConsumer.initial,
      initial,liftBank,RowCleanup.retainedRow,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      ArithmeticSeed.one_length _ hm,ArithmeticSeed.zeros,Function.update] <;> rfl

theorem consumer_final (n iw : List Bool) (hm : 0<n.length) (pre : List (Sym Bool)) :
    consumerBank n iw (RowConsumer.final pre)=initial n iw pre := by
  funext p
  fin_cases p <;>
    simp only [consumerBank,consumerBinding,FinitePortBinding.values,RowConsumer.bank,RowConsumer.final,
      initial,liftBank,RowExecution.initial,RowExecution.prepBank,
      RowPreparation.initial,RowPreparation.Bank.tapes,SourceImages.initial,SourceImages.Bank.tapes,
      SourceEndpoints.initial,SourceEndpoints.Bank.tapes,EndpointClip.initial,EndpointClip.Bank.tapes,
      ArithmeticSeed.one_length _ hm,ArithmeticSeed.zeros] <;> rfl

end TransposeFollowup.RecordedRow
