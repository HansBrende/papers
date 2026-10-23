import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.NativeMatchingXorMaskLayout
import TransposeFollowup.NativeExpanderShearTagBank
import TransposeFollowup.ExpanderShearClock
import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeMappedCopy

/-! Paid preparation of both matching tag banks from retained binary dimensions
and the generated raw opcode stream. All copies, rewinds, layout and clock
construction are actual fixed-control calls. -/
namespace TransposeFollowup.NativeExpanderShearPrepare
open FixedTapeCompiler CopyMachine
open NativeCountedLoop (trace_trans)
set_option autoImplicit false
variable {q : ℕ}

inductive Extra (q : ℕ) | half | opcode | count (side : Bool)
  | mask (side : Bool) (p : Fin q) | tag (side : Bool) (p : Fin q)
  deriving DecidableEq, Fintype
abbrev Port (q : ℕ) := ExpanderShearClock.Port ⊕ Extra q
abbrev Bank (q : ℕ) := Port q → Tape Bool

def clockBinding : FinitePortBinding ExpanderShearClock.Port (Port q) where
  ports := ⟨Sum.inl,Sum.inl_injective⟩
  decode := fun p => match p with | .inl p => some p | .inr _ => none
  decode_spec := by intro p t; cases p <;> simp [eq_comm]

def copyBinding (side : Bool) : FinitePortBinding (Fin 2) (Port q) where
  ports := ⟨![.inr .half,.inr (.count side)],by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩
  decode := fun p => match p with
    | .inr .half => some 0 | .inr (.count b) => if b=side then some 1 else none | _ => none
  decode_spec := by
    intro p t
    change _ ↔ (![.inr .half,.inr (.count side)] : Fin 2 → Port q) t=p
    cases p with
    | inl p => fin_cases t <;> simp
    | inr p => cases p <;> fin_cases t <;> simp [eq_comm]

def rewindBinding : FinitePortBinding (Fin 1) (Port q) where
  ports := ⟨fun _ => .inr .opcode,fun _ _ _ => Subsingleton.elim _ _⟩
  decode := fun p => match p with | .inr .opcode => some 0 | _ => none
  decode_spec := by
    intro p t
    change _ ↔ (Sum.inr Extra.opcode : Port q)=p
    fin_cases t
    cases p with
    | inl p => simp
    | inr p => cases p <;> simp

def layoutPort : NativeMatchingXorMaskLayout.Port q → Port q
  | .count b => .inr (.count b) | .opcode => .inr .opcode | .mask b p => .inr (.mask b p)
def layoutBinding : FinitePortBinding (NativeMatchingXorMaskLayout.Port q) (Port q) where
  ports := ⟨layoutPort,by intro a b h; cases a <;> cases b <;> simp_all [layoutPort]⟩
  decode := fun p => match p with
    | .inr (.count b) => some (.count b) | .inr .opcode => some .opcode
    | .inr (.mask b p) => some (.mask b p) | _ => none
  decode_spec := by
    intro p t
    change _ ↔ layoutPort t=p
    cases p with
    | inl p => cases t <;> simp [layoutPort]
    | inr p => cases p <;> cases t <;> simp [layoutPort,eq_comm]

def tagPort (side : Bool) : NativeExpanderShearTagBank.Port q → Port q
  | .mask p => .inr (.mask side p) | .tag p => .inr (.tag side p) | .clock => .inl .result

def tagBinding (side : Bool) : FinitePortBinding (NativeExpanderShearTagBank.Port q) (Port q) where
  ports := ⟨tagPort side,by intro a b h; cases a <;> cases b <;> simp_all [tagPort]⟩
  decode := fun p => match p with
    | .inl .result => some .clock
    | .inr (.mask b j) => if b=side then some (.mask j) else none
    | .inr (.tag b j) => if b=side then some (.tag j) else none | _ => none
  decode_spec := by
    intro p t
    change _ ↔ tagPort side t=p
    cases p with
    | inl p => cases p <;> cases t <;> simp [tagPort]
    | inr p => cases p <;> cases t <;> simp [tagPort,eq_comm]

inductive Label (q : ℕ)
  | copy (side : Bool) (pc : NativeMappedCopy.Label)
  | rewind (pc : NativeSpanRewind.Label)
  | clock (pc : ExpanderShearClock.Label)
  | layout (pc : NativeMatchingXorMaskLayout.Label q)
  | tags (side : Bool) (pc : NativeExpanderShearTagBank.Label q)
  | done
  deriving DecidableEq, Fintype

def start : Label q := .copy false (.init (.erase 0))
def program (pivot : Fin q) : Microcode.Program (Port q) (Label q)
  | .copy side (.seal .done) => .jump (if side then .rewind .left else .copy true (.init (.erase 0)))
  | .copy side pc => (copyBinding side).instruction (Label.copy side) (NativeMappedCopy.program id pc)
  | .rewind .done => .jump (.clock ExpanderShearClock.start)
  | .rewind pc => rewindBinding.instruction Label.rewind (NativeSpanRewind.program pc)
  | .clock .done => .jump (.layout .leftA)
  | .clock pc => clockBinding.instruction Label.clock (ExpanderShearClock.program pc)
  | .layout .done => .jump (.tags false (NativeExpanderShearTagBank.entry q 0))
  | .layout pc => layoutBinding.instruction Label.layout (NativeMatchingXorMaskLayout.program pivot pc)
  | .tags side .done => .jump (if side then .done else .tags true (NativeExpanderShearTagBank.entry q 0))
  | .tags side pc => (tagBinding side).instruction (Label.tags side) (NativeExpanderShearTagBank.program q pc)
  | .done => .halt

theorem copy_code (pivot : Fin q) (side : Bool) (pc : NativeMappedCopy.Label)
    (hh : NativeMappedCopy.program id pc ≠ .halt) (_ : NativeMappedCopy.program id pc ≠ .reject) :
    program pivot (.copy side pc)=MicrocodeEmbedding.instruction (copyBinding side).ports
      (Label.copy side) (NativeMappedCopy.program id pc) := by
  cases pc with
  | «seal» pc => cases pc <;> simp_all [program,NativeMappedCopy.program,NativeSealBack.program,FinitePortBinding.instruction_eq,MicrocodeEmbedding.instruction]
  | _ => simp only [program,FinitePortBinding.instruction_eq]

theorem rewind_code (pivot : Fin q) (pc : NativeSpanRewind.Label)
    (hh : NativeSpanRewind.program pc ≠ .halt) (_ : NativeSpanRewind.program pc ≠ .reject) :
    program pivot (.rewind pc)=MicrocodeEmbedding.instruction rewindBinding.ports Label.rewind (NativeSpanRewind.program pc) := by
  cases pc <;> simp_all [program,NativeSpanRewind.program,FinitePortBinding.instruction_eq]

theorem clock_code (pivot : Fin q) (pc : ExpanderShearClock.Label)
    (hh : ExpanderShearClock.program pc ≠ .halt) (_ : ExpanderShearClock.program pc ≠ .reject) :
    program pivot (.clock pc)=MicrocodeEmbedding.instruction clockBinding.ports Label.clock (ExpanderShearClock.program pc) := by
  cases pc <;> simp_all [program,ExpanderShearClock.program,FinitePortBinding.instruction_eq]

theorem layout_code (pivot : Fin q) (pc : NativeMatchingXorMaskLayout.Label q)
    (hh : NativeMatchingXorMaskLayout.program pivot pc ≠ .halt) (_ : NativeMatchingXorMaskLayout.program pivot pc ≠ .reject) :
    program pivot (.layout pc)=MicrocodeEmbedding.instruction layoutBinding.ports Label.layout
      (NativeMatchingXorMaskLayout.program pivot pc) := by
  cases pc <;> simp_all [program,NativeMatchingXorMaskLayout.program,FinitePortBinding.instruction_eq]

theorem tags_code (pivot : Fin q) (side : Bool) (pc : NativeExpanderShearTagBank.Label q)
    (hh : NativeExpanderShearTagBank.program q pc ≠ .halt) (_ : NativeExpanderShearTagBank.program q pc ≠ .reject) :
    program pivot (.tags side pc)=MicrocodeEmbedding.instruction (tagBinding side).ports (Label.tags side)
      (NativeExpanderShearTagBank.program q pc) := by
  cases pc <;> simp_all [program,NativeExpanderShearTagBank.program,FinitePortBinding.instruction_eq]

def cfg (pc : Label q) (s : Bank q) (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) (Label q) :=
  ⟨⟨pc,fun p => (s p).denote⟩,pos⟩
def frame (s : Bank q) (pos : Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) := ⟨fun p => (s p).denote,pos⟩
abbrev Trace (pivot : Fin q) := OperationalTrace.Trace (NativeMicrocode.step (program pivot)) (NativeMicrocode.Active (program pivot))

theorem embed_bank {U J : Type*} (binding : FinitePortBinding U (Port q)) (labels : J → Label q)
    (pc : J) (s : U → Tape Bool) (rp : U → ℤ) (f : Bank q) (pos : Port q → ℤ) :
    MicrocodeEmbedding.embed binding.ports labels (⟨⟨pc,fun p => (s p).denote⟩,rp⟩ : NativeMicrocode.Config U J)
      (frame f pos)=cfg (labels pc) (binding.values s f) (binding.values rp pos) := by
  exact NativeExpanderShearFrames.embed_work binding labels pc s f pos rp

theorem project_pos {U : Type*} (binding : FinitePortBinding U (Port q)) (pos : Port q → ℤ) :
    binding.values (fun p => pos (binding.ports p)) pos=pos := by
  exact binding.values_project pos


def initial (xs ms bits : List Bool) : Bank q
  | .inl p => RadiusBuilder.initial xs p
  | .inr .half => Counter.marked ms
  | .inr .opcode => ⟨(symbols bits).reverse,[]⟩
  | _ => ⟨[],[]⟩
def copied (xs ms bits : List Bool) (a b : Bool) : Bank q
  | .inr (.count false) => if a then Counter.marked ms else ⟨[],[]⟩
  | .inr (.count true) => if b then Counter.marked ms else ⟨[],[]⟩
  | p => initial xs ms bits p

def rewound (xs ms bits : List Bool) : Bank q
  | .inr .opcode => ⟨[],symbols bits⟩
  | p => copied xs ms bits true true p

def clocked (xs ms bits : List Bool) : Bank q
  | .inl p => ExpanderShearClock.final xs p
  | p => rewound xs ms bits p

def rewindPos (pos : Port q → ℤ) (bits : List Bool) : Port q → ℤ :=
  Function.update pos (.inr .opcode) (pos (.inr .opcode)-bits.length)

def laidOut (xs ms : List Bool) (a b : List (List (Bool×Bool))) : Bank q :=
  layoutBinding.values (NativeMatchingXorMaskLayout.finish ms a b)
    (clocked xs ms (NativeMatchingXorMasks.encode (a++b)))

def finalPos (pos : Port q → ℤ) (m : ℕ) : Port q → ℤ
  | .inr (.mask true p) => pos (.inr (.mask true p))-m
  | p => pos p

def flags (a b : List (List (Bool×Bool))) (side : Bool) (p : Fin q) : List Bool :=
  if side then (MatchingXorMasksSemantics.flags b p).reverse else MatchingXorMasksSemantics.flags a p

def tagged (xs ms : List Bool) (a b : List (List (Bool×Bool))) (doneA doneB : Bool) : Bank q
  | .inr (.tag side p) => if (if side then doneB else doneA) then
      Counter.marked (NativeMatchingXorTagStream.expanded (ExpanderShearClock.word xs).length (flags a b side p))
      else ⟨[],[]⟩
  | p => laidOut xs ms a b p
abbrev final (xs ms : List Bool) (a b : List (List (Bool×Bool))) : Bank q := tagged xs ms a b true true

def budget (q : ℕ) (xs ms bits : List Bool) (m : ℕ) : ℕ :=
  ExpanderShearClock.budget xs +20*ms.length+2*bits.length+m*(6*q+24)+68+
    2*q*(6*m*(ExpanderShearClock.word xs).length+9*m+17)

theorem copy_call (pivot : Fin q) (side : Bool) (xs ms bits : List Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 6*ms.length+14, Trace pivot t
      (cfg (.copy side (.init (.erase 0))) (copied xs ms bits side false) pos)
      (cfg (.copy side (.seal .done)) (copied xs ms bits true side) pos) := by
  obtain ⟨t,ht,tr⟩ := NativeMappedCopy.copy_trace id ms (fun p => pos ((copyBinding side).ports p))
  have he := MicrocodeEmbedding.trace_embed (copyBinding side).ports (Label.copy side)
    (NativeMappedCopy.program id) (program pivot) (frame (copied xs ms bits side false) pos) (copy_code pivot side) tr
  simp only [NativeMappedCopy.cfg,embed_bank,project_pos,List.map_id_fun,id_eq] at he
  have hi : (copyBinding (q:=q) side).values (NativeMappedCopy.bank (Counter.marked ms) ⟨[],[]⟩)
      (copied xs ms bits side false)=copied xs ms bits side false := by
    funext p; cases side <;> cases p with
    | inl p => rfl
    | inr p => cases p with
      | count b => cases b <;> rfl
      | _ => rfl
  have hf : (copyBinding (q:=q) side).values (NativeMappedCopy.bank (Counter.marked ms) (Counter.marked ms))
      (copied xs ms bits side false)=copied xs ms bits true side := by
    funext p; cases side <;> cases p with
    | inl p => rfl
    | inr p => cases p with
      | count b => cases b <;> rfl
      | _ => rfl
  exact ⟨t,ht,by simpa only [hi,hf] using he⟩

theorem rewind_call (pivot : Fin q) (xs ms bits : List Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 2*bits.length+3, Trace pivot t
      (cfg (.rewind .left) (copied xs ms bits true true) pos)
      (cfg (.rewind .done) (rewound xs ms bits) (rewindPos pos bits)) := by
  obtain ⟨t,ht,tr⟩ := NativeSpanRewind.rewind_trace (symbols bits)
    (by intro s hs; simp only [symbols,List.mem_map] at hs; rcases hs with ⟨b,_,rfl⟩; simp)
    (fun p => pos (rewindBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed rewindBinding.ports Label.rewind NativeSpanRewind.program
    (program pivot) (frame (copied xs ms bits true true) pos) (rewind_code pivot) tr
  simp only [NativeSpanRewind.cfg,NativeZipper.Config.denote,Microcode.Config.denote,embed_bank,project_pos] at he
  have hi : (rewindBinding (q:=q)).values (fun _ : Fin 1 => (⟨(symbols bits).reverse,[]⟩ : Tape Bool))
      (copied xs ms bits true true)=copied xs ms bits true true := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p <;> rfl
  have hf : (rewindBinding (q:=q)).values (fun _ : Fin 1 => (⟨[],symbols bits⟩ : Tape Bool))
      (copied xs ms bits true true)=rewound xs ms bits := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p <;> rfl
  have hp : rewindBinding.values (fun p => pos (rewindBinding.ports p)-(symbols bits).length) pos=rewindPos pos bits := by
    funext p; cases p with
    | inl p => simp [FinitePortBinding.values,rewindBinding,rewindPos]
    | inr p => cases p with
      | opcode =>
        change pos (.inr .opcode)-((symbols bits).length:ℤ)=pos (.inr .opcode)-(bits.length:ℤ)
        simp [symbols]
      | _ => rfl
  exact ⟨t,by simpa [symbols] using ht,by simpa only [hi,hf,hp] using he⟩

theorem clock_call (pivot : Fin q) (xs ms bits : List Bool) (hx : 0<Counter.value xs) (pos : Port q → ℤ) :
    ∃ t ≤ ExpanderShearClock.budget xs, Trace pivot t
      (cfg (.clock ExpanderShearClock.start) (rewound xs ms bits) pos)
      (cfg (.clock .done) (clocked xs ms bits) pos) := by
  obtain ⟨t,ht,tr⟩ := ExpanderShearClock.complete_trace xs hx (fun p => pos (clockBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed clockBinding.ports Label.clock ExpanderShearClock.program
    (program pivot) (frame (rewound xs ms bits) pos) (clock_code pivot) tr
  simp only [ExpanderShearClock.cfg,embed_bank,project_pos] at he
  have hi : (clockBinding (q:=q)).values (RadiusBuilder.initial xs) (rewound xs ms bits)=rewound xs ms bits := by
    funext p; cases p with
    | inl p => rfl
    | inr p => rfl
  have hf : (clockBinding (q:=q)).values (ExpanderShearClock.final xs) (rewound xs ms bits)=clocked xs ms bits := by
    funext p; cases p <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using he⟩


theorem encode_length (rows : List (List (Bool×Bool))) (hr : ∀x∈rows,x.length=q) :
    (NativeMatchingXorMasks.encode rows).length=2*q*rows.length := by
  induction rows with
  | nil => simp [NativeMatchingXorMasks.encode]
  | cons a rows ih =>
    have ha := hr a (by simp)
    have ht : ∀x∈rows,x.length=q := by intro x hx; exact hr x (by simp [hx])
    have hrow : (NativeMatchingXorMaskRow.encode a).length=2*a.length := by
      induction a with
      | nil => rfl
      | cons x a ih => simp [NativeMatchingXorMaskRow.encode] at *; omega
    rw [NativeMatchingXorMasks.encode,List.flatMap_cons,List.length_append,hrow]
    change 2*a.length+(NativeMatchingXorMasks.encode rows).length=_
    rw [ih ht,ha,List.length_cons];ring

theorem layout_call (pivot : Fin q) (a b : List (List (Bool×Bool)))
    (ha : ∀x∈a,x.length=q) (hb : ∀x∈b,x.length=q) (hab : b.length=a.length)
    (xs ms : List Bool) (hv : Counter.value ms=a.length) (pos : Port q → ℤ) :
    ∃ t ≤ a.length*(6*q+24)+8*ms.length+27, Trace pivot t
      (cfg (.layout .leftA) (clocked xs ms (NativeMatchingXorMasks.encode (a++b)))
        (rewindPos pos (NativeMatchingXorMasks.encode (a++b))))
      (cfg (.layout .done) (laidOut xs ms a b) (finalPos pos a.length)) := by
  let bits := NativeMatchingXorMasks.encode (a++b)
  let rp := rewindPos pos bits
  obtain ⟨t,ht,tr⟩ := NativeMatchingXorMaskLayout.complete_trace pivot a b ha hb hab ms hv
    (fun p => rp (layoutBinding.ports p))
  have he := MicrocodeEmbedding.trace_embed layoutBinding.ports Label.layout (NativeMatchingXorMaskLayout.program pivot)
    (program pivot) (frame (clocked xs ms bits) rp) (layout_code pivot) tr
  simp only [NativeMatchingXorMaskLayout.cfg,NativeZipper.Config.denote,Microcode.Config.denote,embed_bank,project_pos] at he
  have hi : (layoutBinding (q:=q)).values (NativeMatchingXorMaskLayout.initial ms bits)
      (clocked xs ms bits)=clocked xs ms bits := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p with
      | count side => cases side <;> rfl
      | mask side j => cases side <;> rfl
      | _ => rfl
  have hlen : bits.length=4*q*a.length := by
    dsimp [bits]
    rw [encode_length (a++b) (by intro x hx; rcases List.mem_append.mp hx with h|h; exact ha x h; exact hb x h),List.length_append,hab]
    ring
  have hp : layoutBinding.values
      (NativeMatchingXorMaskLayout.finalPos (fun p => rp (layoutBinding.ports p)) a.length) rp=finalPos pos a.length := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p with
      | count side => cases side <;> rfl
      | mask side j => cases side <;> rfl
      | opcode =>
        change pos (.inr .opcode)-(bits.length:ℤ)+4*(q:ℤ)*a.length=pos (.inr .opcode)
        rw [hlen]; push_cast; ring
      | half => rfl
      | tag side j => rfl
  dsimp only [bits] at hi
  rw [hi,hp] at he
  exact ⟨t,ht,he⟩

theorem tags_call (pivot : Fin q) (side : Bool) (xs ms : List Bool)
    (a b : List (List (Bool×Bool))) (hab : b.length=a.length) (pos : Port q → ℤ) :
    ∃ t ≤ q*(6*a.length*(ExpanderShearClock.word xs).length+9*a.length+17), Trace pivot t
      (cfg (.tags side (NativeExpanderShearTagBank.entry q 0)) (tagged xs ms a b side false) pos)
      (cfg (.tags side .done) (tagged xs ms a b true side) pos) := by
  have hlen : ∀j : Fin q,(flags a b side j).length=a.length := by
    intro j; cases side <;> simp [flags,MatchingXorMasksSemantics.flags,hab]
  obtain ⟨t,ht,tr⟩ := NativeExpanderShearTagBank.complete_trace (flags a b side) (ExpanderShearClock.word xs)
    a.length hlen (fun p => pos ((tagBinding side).ports p))
  have he := MicrocodeEmbedding.trace_embed (tagBinding side).ports (Label.tags side)
    (NativeExpanderShearTagBank.program q) (program pivot) (frame (tagged xs ms a b side false) pos)
    (tags_code pivot side) tr
  simp only [NativeExpanderShearTagBank.cfg,embed_bank,project_pos] at he
  have hi : (tagBinding (q:=q) side).values (NativeExpanderShearTagBank.initial (flags a b side) (ExpanderShearClock.word xs))
      (tagged xs ms a b side false)=tagged xs ms a b side false := by
    funext p; cases side <;> cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p with
      | mask side j => cases side <;> rfl
      | tag side j => cases side <;> rfl
      | _ => rfl
  have hf : (tagBinding (q:=q) side).values (NativeExpanderShearTagBank.final (flags a b side) (ExpanderShearClock.word xs))
      (tagged xs ms a b side false)=tagged xs ms a b true side := by
    funext p; cases side <;> cases p with
    | inl p => cases p <;> rfl
    | inr p => cases p with
      | mask side j => cases side <;> rfl
      | tag side j => cases side <;> simp [FinitePortBinding.values,tagBinding,NativeExpanderShearTagBank.final,
          NativeExpanderShearTagBank.stage,tagged,flags,j.isLt]
      | _ => rfl
  exact ⟨t,ht,by simpa only [hi,hf] using he⟩

theorem complete_trace (pivot : Fin q) (a b : List (List (Bool×Bool)))
    (ha : ∀x∈a,x.length=q) (hb : ∀x∈b,x.length=q) (hab : b.length=a.length)
    (xs ms : List Bool) (hx : 0<Counter.value xs) (hv : Counter.value ms=a.length) (pos : Port q → ℤ) :
    ∃ t ≤ budget q xs ms (NativeMatchingXorMasks.encode (a++b)) a.length, Trace pivot t
      (cfg start (initial xs ms (NativeMatchingXorMasks.encode (a++b))) pos)
      (cfg .done (final xs ms a b) (finalPos pos a.length)) := by
  let bits := NativeMatchingXorMasks.encode (a++b)
  obtain ⟨s,hs,ts⟩ := copy_call pivot false xs ms bits pos
  obtain ⟨u,hu,tu⟩ := copy_call pivot true xs ms bits pos
  obtain ⟨v,hv',tv⟩ := rewind_call pivot xs ms bits pos
  obtain ⟨w,hw,tw⟩ := clock_call pivot xs ms bits hx (rewindPos pos bits)
  obtain ⟨x,hx',tx⟩ := layout_call pivot a b ha hb hab xs ms hv pos
  obtain ⟨y,hy,ty⟩ := tags_call pivot false xs ms a b hab (finalPos pos a.length)
  obtain ⟨z,hz,tz⟩ := tags_call pivot true xs ms a b hab (finalPos pos a.length)
  have j1 : Trace pivot 1 (cfg (.copy false (.seal .done)) (copied xs ms bits true false) pos)
      (cfg (.copy true (.init (.erase 0))) (copied xs ms bits true false) pos) := NativeMicrocode.jump_trace _ _ _ rfl
  have j2 : Trace pivot 1 (cfg (.copy true (.seal .done)) (copied xs ms bits true true) pos)
      (cfg (.rewind .left) (copied xs ms bits true true) pos) := NativeMicrocode.jump_trace _ _ _ rfl
  have j3 : Trace pivot 1 (cfg (.rewind .done) (rewound xs ms bits) (rewindPos pos bits))
      (cfg (.clock ExpanderShearClock.start) (rewound xs ms bits) (rewindPos pos bits)) := NativeMicrocode.jump_trace _ _ _ rfl
  have j4 : Trace pivot 1 (cfg (.clock .done) (clocked xs ms bits) (rewindPos pos bits))
      (cfg (.layout .leftA) (clocked xs ms bits) (rewindPos pos bits)) := NativeMicrocode.jump_trace _ _ _ rfl
  have j5 : Trace pivot 1 (cfg (.layout .done) (laidOut xs ms a b) (finalPos pos a.length))
      (cfg (.tags false (NativeExpanderShearTagBank.entry q 0)) (laidOut xs ms a b) (finalPos pos a.length)) := NativeMicrocode.jump_trace _ _ _ rfl
  have j6 : Trace pivot 1 (cfg (.tags false .done) (tagged xs ms a b true false) (finalPos pos a.length))
      (cfg (.tags true (NativeExpanderShearTagBank.entry q 0)) (tagged xs ms a b true false) (finalPos pos a.length)) := NativeMicrocode.jump_trace _ _ _ rfl
  have j7 : Trace pivot 1 (cfg (.tags true .done) (final xs ms a b) (finalPos pos a.length))
      (cfg .done (final xs ms a b) (finalPos pos a.length)) := NativeMicrocode.jump_trace _ _ _ rfl
  have hi : copied (q:=q) xs ms bits false false=initial xs ms bits := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p with
      | count side => cases side <;> rfl
      | _ => rfl
  have hj : tagged (q:=q) xs ms a b false false=laidOut xs ms a b := by
    funext p; cases p with
    | inl p => rfl
    | inr p => cases p with
      | tag side j => cases side <;> rfl
      | _ => rfl
  rw [hi] at ts
  rw [hj] at ty
  refine ⟨_,?_,trace_trans ts (trace_trans j1 (trace_trans tu (trace_trans j2 (trace_trans tv
    (trace_trans j3 (trace_trans tw (trace_trans j4 (trace_trans tx (trace_trans j5 (trace_trans ty
      (trace_trans j6 (trace_trans tz j7))))))))))))⟩
  unfold budget
  dsimp [bits] at *
  nlinarith

@[simp] theorem final_tag (xs ms : List Bool) (a b : List (List (Bool×Bool))) (side : Bool) (p : Fin q) :
    final xs ms a b (.inr (.tag side p))=Counter.marked
      (NativeMatchingXorTagStream.expanded (ExpanderShearClock.word xs).length (flags a b side p)) := by
  cases side <;> rfl
@[simp] theorem final_dimension (xs ms : List Bool) (a b : List (List (Bool×Bool))) :
    final (q:=q) xs ms a b (.inl .source)=Counter.marked xs := rfl
@[simp] theorem final_half (xs ms : List Bool) (a b : List (List (Bool×Bool))) :
    final (q:=q) xs ms a b (.inr .half)=Counter.marked ms := rfl
@[simp] theorem final_clock (xs ms : List Bool) (a b : List (List (Bool×Bool))) :
    final (q:=q) xs ms a b (.inl .result)=Counter.marked (ExpanderShearClock.word xs) := rfl
@[simp] theorem final_tag_pos (pos : Port q → ℤ) (m : ℕ) (side : Bool) (p : Fin q) :
    finalPos pos m (.inr (.tag side p))=pos (.inr (.tag side p)) := rfl


noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (start (q:=q))
noncomputable def nativeMachine (pivot : Fin q) := NativeMicrocode.machine (nativeEncoding q) (program pivot)

theorem native_call {U J : Type*} {k t : ℕ} (pivot : Fin q)
    (encoding : NativeMicrocode.Encoding U J k t) (ports : Port q ↪ U) (labels : Label q → J)
    (target : Microcode.Program U J) (outerFrame : MicrocodeEmbedding.Frame U)
    (hc : ∀ pc,program pivot pc≠.halt → program pivot pc≠.reject →
      target (labels pc)=MicrocodeEmbedding.instruction ports labels (program pivot pc))
    (a b : List (List (Bool×Bool)))
    (ha : ∀x∈a,x.length=q) (hb : ∀x∈b,x.length=q) (hab : b.length=a.length)
    (xs ms : List Bool) (hx : 0<Counter.value xs) (hv : Counter.value ms=a.length) (pos : Port q → ℤ)
    (input : List Bool) (inputPos : ℤ) (outRev : List Bool) :
    ∃ steps ≤ budget q xs ms (NativeMatchingXorMasks.encode (a++b)) a.length,
      Transpose.stepN (NativeMicrocode.machine encoding target) input steps
        ((MicrocodeEmbedding.embed ports labels (cfg start (initial xs ms (NativeMatchingXorMasks.encode (a++b))) pos)
          outerFrame).denote encoding target inputPos outRev)=
        some ((MicrocodeEmbedding.embed ports labels (cfg .done (final xs ms a b) (finalPos pos a.length))
          outerFrame).denote encoding target inputPos outRev) := by
  obtain ⟨steps,ht,htr⟩ := complete_trace pivot a b ha hb hab xs ms hx hv pos
  exact ⟨steps,ht,MicrocodeEmbedding.native_call encoding ports labels (program pivot) target
    outerFrame input inputPos outRev hc htr⟩

theorem fixed_resources (pivot : Fin q) :
    (nativeMachine pivot).k=11+Fintype.card (Extra q) ∧ (nativeMachine pivot).g+1=5 ∧
      (nativeEncoding q).label start=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (ExpanderShearClock.Port ⊕ Extra q)=_
  rw [Fintype.card_sum,show Fintype.card ExpanderShearClock.Port=11 by decide +kernel]

end TransposeFollowup.NativeExpanderShearPrepare
