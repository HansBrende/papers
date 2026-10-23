import TransposeFollowup.NativeExpanderShearFrames
import TransposeFollowup.NativeMatchingXorClose

/-! Paid layout of the two matching-mask banks. Two physical binary copies
of m control the A and B halves. A flags grow rightwards; B flags grow
leftwards, reversing the generator's descending target-row order. All
markers, sealing, head restoration and caller jumps are included. -/
namespace TransposeFollowup.NativeMatchingXorMaskLayout
open FixedTapeCompiler CopyMachine MatchingXorMasksSemantics
set_option autoImplicit false
variable {q : ℕ}
inductive Port (q : ℕ) | count (reverse : Bool) | opcode | mask (reverse : Bool) (p : Fin q)
  deriving DecidableEq, Fintype
abbrev Bank (q : ℕ) := Port q → Tape Bool
inductive Label (q : ℕ)
  | leftA | markA | markB | masks (reverse : Bool) (pc : NativeMatchingXorMasks.Label q)
  | close (pc : NativeMatchingXorClose.Label) | sealB | done
  deriving DecidableEq, Fintype

def masksPort (reverse : Bool) : NativeMatchingXorMasks.Port q → Port q
  | none => .count reverse | some none => .opcode | some (some p) => .mask reverse p

theorem masksPort_injective (reverse : Bool) : Function.Injective (masksPort (q:=q) reverse) := by
  intro p t h
  cases p with
  | none => cases t with
    | none => rfl
    | some t => cases t <;> simp [masksPort] at h
  | some p => cases t with
    | none => cases p <;> simp [masksPort] at h
    | some t => cases p <;> cases t <;> simp_all [masksPort]

def masksBinding (reverse : Bool) : FinitePortBinding (NativeMatchingXorMasks.Port q) (Port q) where
  ports := ⟨masksPort reverse,masksPort_injective reverse⟩
  decode := fun p => match p with
    | .count b => if b=reverse then some none else none
    | .opcode => some (some none)
    | .mask b p => if b=reverse then some (some (some p)) else none
  decode_spec := by
    intro p t
    change (match p with
      | .count b => if b=reverse then some none else none
      | .opcode => some (some none)
      | .mask b p => if b=reverse then some (some (some p)) else none)=some t ↔ masksPort reverse t=p
    cases p <;> cases t <;> simp [masksPort]
    all_goals try (split_ifs <;> simp_all)
    all_goals rename_i t; cases t <;> simp_all [masksPort,eq_comm]

def closeBinding : FinitePortBinding (Fin q) (Port q) where
  ports := ⟨Port.mask false,by intro a b h; exact (Port.mask.inj h).2⟩
  decode := fun p => match p with | .mask false p => some p | _ => none
  decode_spec := by
    intro p t
    change (match p with | .mask false p => some p | _ => none)=some t ↔ Port.mask false t=p
    cases p with
    | count b => simp
    | opcode => simp
    | mask b j => cases b <;> simp [eq_comm]

def program (pivot : Fin q) : Microcode.Program (Port q) (Label q)
  | .leftA => .act (fun p => ⟨none,match p with | .mask false _ => .left | _ => .stay⟩) .markA
  | .markA => .act (fun p => match p with | .mask false _ => ⟨some .start,.right⟩ | _ => ⟨none,.stay⟩) .markB
  | .markB => .act (fun p => match p with | .mask true _ => ⟨some .stop,.left⟩ | _ => ⟨none,.stay⟩) (.masks false (.count 0))
  | .masks reverse (.count pc) => if pc=12 then
      .jump (if reverse then .close .seal else .masks true (.count 0))
    else (masksBinding reverse).instruction (Label.masks reverse) (NativeMatchingXorMasks.program reverse (.count pc))
  | .masks reverse pc => (masksBinding reverse).instruction (Label.masks reverse) (NativeMatchingXorMasks.program reverse pc)
  | .close .done => .jump .sealB
  | .close pc => closeBinding.instruction Label.close (NativeMatchingXorClose.program pivot pc)
  | .sealB => .act (fun p => match p with | .mask true _ => ⟨some .start,.right⟩ | _ => ⟨none,.stay⟩) .done
  | .done => .halt

theorem masks_code (pivot : Fin q) (reverse : Bool) (pc : NativeMatchingXorMasks.Label q)
    (hh : NativeMatchingXorMasks.program reverse pc≠.halt)
    (_ : NativeMatchingXorMasks.program reverse pc≠.reject) :
    program pivot (.masks reverse pc)=MicrocodeEmbedding.instruction (masksBinding reverse).ports
      (Label.masks reverse) (NativeMatchingXorMasks.program reverse pc) := by
  cases pc with
  | count pc =>
    have hn : pc≠12 := fun h => by subst pc; exact hh rfl
    simp [program,hn,FinitePortBinding.instruction_eq]
  | row pc => simp only [program,FinitePortBinding.instruction_eq]

theorem close_code (pivot : Fin q) (pc : NativeMatchingXorClose.Label)
    (hh : NativeMatchingXorClose.program pivot pc≠.halt)
    (_ : NativeMatchingXorClose.program pivot pc≠.reject) :
    program pivot (.close pc)=MicrocodeEmbedding.instruction closeBinding.ports Label.close
      (NativeMatchingXorClose.program pivot pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [program,FinitePortBinding.instruction_eq]

def cfg (pc : Label q) (s : Bank q) (pos : Port q → ℤ) : NativeZipper.Config (Port q) (Label q) := ⟨⟨pc,s⟩,pos⟩
def frame (s : Bank q) (pos : Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) := ⟨fun p => (s p).denote,pos⟩
def bank (ca cb : List Bool) (op : Tape Bool) (ma mb : Fin q → Tape Bool) : Bank q
  | .count false => Counter.marked ca | .count true => Counter.marked cb
  | .opcode => op | .mask false p => ma p | .mask true p => mb p

def initial (xs bits : List Bool) : Bank q
  | .count _ => Counter.marked xs | .opcode => ⟨[],symbols bits⟩ | .mask _ _ => ⟨[],[]⟩
def ready (xs bits : List Bool) : Bank q := bank xs xs ⟨[],symbols bits⟩
  (fun _ => NativeSealBack.openWord []) (fun _ => leftOpen [])
def activePos (pos : Port q → ℤ) (a b : ℕ) : Port q → ℤ
  | .count r => pos (.count r)
  | .opcode => pos .opcode+2*q*(a+b)
  | .mask false p => pos (.mask false p)+a
  | .mask true p => pos (.mask true p)-b-1

def finalPos (pos : Port q → ℤ) (n : ℕ) : Port q → ℤ
  | .count r => pos (.count r)
  | .opcode => pos .opcode+4*q*n
  | .mask false p => pos (.mask false p)
  | .mask true p => pos (.mask true p)-n

def finish (xs : List Bool) (a b : List (List (Bool×Bool))) : Bank q :=
  bank (List.replicate xs.length true) (List.replicate xs.length true)
    ⟨(symbols (NativeMatchingXorMasks.encode (a++b))).reverse,[]⟩
    (fun p => Counter.marked (flags a p)) (fun p => Counter.marked ((flags b p).reverse))

abbrev Trace (pivot : Fin q) := OperationalTrace.Trace (NativeMicrocode.step (program pivot))
  (NativeMicrocode.Active (program pivot))

theorem initialize_trace (pivot : Fin q) (xs bits : List Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 3, Trace pivot t (cfg .leftA (initial xs bits) pos).denote
      (cfg (.masks false (.count 0)) (ready xs bits) (activePos pos 0 0)).denote := by
  have h : NativeZipper.run (program pivot) 3 (cfg .leftA (initial xs bits) pos)=
      cfg (.masks false (.count 0)) (ready xs bits) (activePos pos 0 0) := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,initial,
      Microcode.Action.apply,Tape.write,Tape.moveLeft,Tape.moveRight,Tape.read]
    constructor
    · funext p; cases p with
      | count b => cases b <;> rfl
      | opcode => rfl
      | mask b p => cases b <;> rfl
    · funext p; cases p with
      | count b => cases b <;> simp [activePos,NativeMicrocode.direction,Transpose.Dir.shift]
      | opcode => simp [activePos,NativeMicrocode.direction,Transpose.Dir.shift]
      | mask b p => cases b <;> simp [activePos,NativeMicrocode.direction,Transpose.Dir.shift]
  exact NativeZipper.trace_of_run (program pivot) h

theorem embed_masks (reverse : Bool) (pc : NativeMatchingXorMasks.Label q) (xs : List Bool)
    (op : Tape Bool) (out : Fin q → Tape Bool) (s : Bank q) (pos : Port q → ℤ)
    (rp : NativeMatchingXorMasks.Port q → ℤ) :
    MicrocodeEmbedding.embed (masksBinding reverse).ports (Label.masks reverse)
      (NativeMatchingXorMasks.cfg pc xs op out rp).denote (frame s pos)=
      (cfg (.masks reverse pc) ((masksBinding reverse).values (NativeMatchingXorMasks.bank xs op out) s)
        ((masksBinding reverse).values rp pos)).denote := by
  exact NativeExpanderShearFrames.embed_work (masksBinding reverse) (Label.masks reverse) pc _ s pos rp

theorem masks_call (pivot : Fin q) (reverse : Bool) (rows : List (List (Bool×Bool)))
    (hr : ∀x∈rows,x.length=q) (xs : List Bool) (hv : Counter.value xs=rows.length)
    (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (s : Bank q) (pos : Port q → ℤ) :
    ∃ t ≤ rows.length*(3*q+3)+8*(rows.length+1)+4*xs.length, Trace pivot t
      (cfg (.masks reverse (.count 0))
        ((masksBinding reverse).values (NativeMatchingXorMasks.bank xs ⟨il,symbols (NativeMatchingXorMasks.encode rows)++ir⟩ out) s) pos).denote
      (cfg (.masks reverse (.count 12))
        ((masksBinding reverse).values (NativeMatchingXorMasks.bank (List.replicate xs.length true)
          ⟨(symbols (NativeMatchingXorMasks.encode rows)).reverse++il,ir⟩ (NativeMatchingXorMasks.writeMany reverse rows out)) s)
        ((masksBinding reverse).values
          (NativeMatchingXorMasks.advanceMany reverse rows.length (fun p => pos ((masksBinding reverse).ports p))) pos)).denote := by
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorMasks.complete_trace reverse rows hr xs hv il ir out
    (fun p => pos ((masksBinding reverse).ports p))
  have hp : (masksBinding reverse).values (fun p => pos ((masksBinding reverse).ports p)) pos=pos := by
    funext p; cases p with
    | count b => cases reverse <;> cases b <;> rfl
    | opcode => rfl
    | mask b p => cases reverse <;> cases b <;> rfl
  refine ⟨t,ht,?_⟩
  simpa only [embed_masks,hp] using MicrocodeEmbedding.trace_embed (masksBinding reverse).ports
    (Label.masks reverse) (NativeMatchingXorMasks.program reverse) (program pivot) (frame s pos)
    (masks_code pivot reverse) htr

theorem jump_trace (pivot : Fin q) (a b : Label q) (s : Bank q) (pos : Port q → ℤ)
    (h : program pivot a=.jump b) : Trace pivot 1 (cfg a s pos).denote (cfg b s pos).denote := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote,cfg,h]
  · rw [← NativeZipper.step_denote]
    have he : NativeZipper.step (program pivot) (cfg a s pos)=cfg b s pos := by
      simp [NativeZipper.step,Microcode.step,cfg,h]
    rw [he]; exact .refl _


theorem values_false (c ca cb : List Bool) (op op0 : Tape Bool) (out ma mb : Fin q → Tape Bool) :
    (masksBinding false).values (NativeMatchingXorMasks.bank c op out) (bank ca cb op0 ma mb)=
      bank c cb op out mb := by
  funext p; cases p with
  | count b => cases b <;> rfl
  | opcode => rfl
  | mask b p => cases b <;> rfl

theorem values_true (c ca cb : List Bool) (op op0 : Tape Bool) (out ma mb : Fin q → Tape Bool) :
    (masksBinding true).values (NativeMatchingXorMasks.bank c op out) (bank ca cb op0 ma mb)=
      bank ca c op ma out := by
  funext p; cases p with
  | count b => cases b <;> rfl
  | opcode => rfl
  | mask b p => cases b <;> rfl

theorem advance_false (pos : Port q → ℤ) (a b n : ℕ) :
    (masksBinding false).values
      (NativeMatchingXorMasks.advanceMany false n (fun p => activePos pos a b ((masksBinding false).ports p)))
      (activePos pos a b)=activePos pos (a+n) b := by
  rw [masks_advance]
  funext p; cases p with
  | count c => cases c <;> simp [masksBinding,masksPort,FinitePortBinding.values,activePos]
  | opcode => simp [masksBinding,masksPort,FinitePortBinding.values,activePos];ring
  | mask c p => cases c <;> simp [masksBinding,masksPort,FinitePortBinding.values,activePos] <;> ring

theorem advance_true (pos : Port q → ℤ) (a b n : ℕ) :
    (masksBinding true).values
      (NativeMatchingXorMasks.advanceMany true n (fun p => activePos pos a b ((masksBinding true).ports p)))
      (activePos pos a b)=activePos pos a (b+n) := by
  rw [masks_advance]
  funext p; cases p with
  | count c => cases c <;> simp [masksBinding,masksPort,FinitePortBinding.values,activePos]
  | opcode => simp [masksBinding,masksPort,FinitePortBinding.values,activePos];ring
  | mask c p => cases c <;> simp [masksBinding,masksPort,FinitePortBinding.values,activePos] <;> ring

def afterA (xs : List Bool) (a b : List (List (Bool×Bool))) : Bank q :=
  bank (List.replicate xs.length true) xs
    ⟨(symbols (NativeMatchingXorMasks.encode a)).reverse,symbols (NativeMatchingXorMasks.encode b)⟩
    (fun p => NativeSealBack.openWord (flags a p)) (fun _ => leftOpen [])
def afterB (xs : List Bool) (a b : List (List (Bool×Bool))) : Bank q :=
  bank (List.replicate xs.length true) (List.replicate xs.length true)
    ⟨(symbols (NativeMatchingXorMasks.encode (a++b))).reverse,[]⟩
    (fun p => NativeSealBack.openWord (flags a p)) (fun p => leftOpen ((flags b p).reverse))
def closedA (xs : List Bool) (a b : List (List (Bool×Bool))) : Bank q :=
  bank (List.replicate xs.length true) (List.replicate xs.length true)
    ⟨(symbols (NativeMatchingXorMasks.encode (a++b))).reverse,[]⟩
    (fun p => Counter.marked (flags a p)) (fun p => leftOpen ((flags b p).reverse))
def closedPos (pos : Port q → ℤ) (n : ℕ) : Port q → ℤ
  | .mask false p => pos (.mask false p)
  | p => activePos pos n n p

theorem first_half_trace (pivot : Fin q) (a b : List (List (Bool×Bool)))
    (ha : ∀x∈a,x.length=q) (xs : List Bool) (hv : Counter.value xs=a.length) (pos : Port q → ℤ) :
    ∃ t ≤ a.length*(3*q+3)+8*(a.length+1)+4*xs.length, Trace pivot t
      (cfg (.masks false (.count 0)) (ready xs (NativeMatchingXorMasks.encode (a++b))) (activePos pos 0 0)).denote
      (cfg (.masks false (.count 12)) (afterA xs a b) (activePos pos a.length 0)).denote := by
  have ho : NativeMatchingXorMasks.writeMany false a (fun _ : Fin q => NativeSealBack.openWord [])=
      fun p => NativeSealBack.openWord (flags a p) := by
    funext p; simpa using masks_right a ha (fun _ => []) p
  obtain ⟨t,ht,htr⟩ := masks_call pivot false a ha xs hv [] (symbols (NativeMatchingXorMasks.encode b))
    (fun _ => NativeSealBack.openWord []) (ready xs (NativeMatchingXorMasks.encode (a++b))) (activePos pos 0 0)
  refine ⟨t,ht,?_⟩
  simpa only [ready,afterA,values_false,ho,List.append_nil,List.nil_append,advance_false,zero_add,
    NativeMatchingXorMasks.encode,List.flatMap_append,symbols,List.map_append] using htr

theorem second_half_trace (pivot : Fin q) (a b : List (List (Bool×Bool)))
    (hb : ∀x∈b,x.length=q) (xs : List Bool) (hv : Counter.value xs=b.length) (pos : Port q → ℤ) :
    ∃ t ≤ b.length*(3*q+3)+8*(b.length+1)+4*xs.length, Trace pivot t
      (cfg (.masks true (.count 0)) (afterA xs a b) (activePos pos a.length 0)).denote
      (cfg (.masks true (.count 12)) (afterB xs a b) (activePos pos a.length b.length)).denote := by
  have ho : NativeMatchingXorMasks.writeMany true b (fun _ : Fin q => leftOpen [])=
      fun p => leftOpen ((flags b p).reverse) := by
    funext p; simpa using masks_left b hb (fun _ => []) p
  obtain ⟨t,ht,htr⟩ := masks_call pivot true b hb xs hv ((symbols (NativeMatchingXorMasks.encode a)).reverse) []
    (fun _ => leftOpen []) (afterA xs a b) (activePos pos a.length 0)
  refine ⟨t,ht,?_⟩
  simpa only [afterA,afterB,values_true,ho,List.append_nil,advance_true,zero_add,
    NativeMatchingXorMasks.encode,List.flatMap_append,symbols,List.map_append,List.reverse_append] using htr

theorem embed_close (pc : NativeMatchingXorClose.Label) (out : Fin q → Tape Bool)
    (s : Bank q) (pos : Port q → ℤ) (rp : Fin q → ℤ) :
    MicrocodeEmbedding.embed closeBinding.ports Label.close (NativeMatchingXorClose.cfg pc out rp).denote (frame s pos)=
      (cfg (.close pc) (closeBinding.values out s) (closeBinding.values rp pos)).denote := by
  exact NativeExpanderShearFrames.embed_work closeBinding Label.close pc out s pos rp

theorem close_trace (pivot : Fin q) (a b : List (List (Bool×Bool))) (hab : b.length=a.length)
    (xs : List Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 2*a.length+4, Trace pivot t
      (cfg (.close .seal) (afterB xs a b) (activePos pos a.length a.length)).denote
      (cfg (.close .done) (closedA xs a b) (closedPos pos a.length)).denote := by
  let rows : List (Fin q → Bool) := a.map (fun x p => (x.getD p.val (false,false)).1)
  have hf (p : Fin q) : rows.map (fun f => f p)=flags a p := by simp [rows,flags]
  obtain ⟨t,ht,htr⟩ := NativeMatchingXorClose.complete_trace pivot rows
    (fun p => activePos pos a.length a.length (.mask false p))
  have hi : (closeBinding (q:=q)).values (fun p => NativeSealBack.openWord (flags a p)) (afterB xs a b)=afterB xs a b := by
    funext p; cases p with
    | count b => cases b <;> rfl
    | opcode => rfl
    | mask b p => cases b <;> rfl
  have ho : (closeBinding (q:=q)).values (fun p => Counter.marked (flags a p)) (afterB xs a b)=closedA xs a b := by
    funext p; cases p with
    | count b => cases b <;> rfl
    | opcode => rfl
    | mask b p => cases b <;> rfl
  have hpi : (closeBinding (q:=q)).values (fun p => activePos pos a.length a.length (.mask false p))
      (activePos pos a.length a.length)=activePos pos a.length a.length := by
    funext p;cases p with
    | count b => cases b <;> rfl
    | opcode => rfl
    | mask b p => cases b <;> rfl
  have hpo : (closeBinding (q:=q)).values (fun p => activePos pos a.length a.length (.mask false p)-rows.length)
      (activePos pos a.length a.length)=closedPos pos a.length := by
    funext p;cases p with
    | count b => cases b <;> rfl
    | opcode => rfl
    | mask b p => cases b <;> simp [closeBinding,FinitePortBinding.values,activePos,closedPos,rows]
  refine ⟨t,by simpa [rows] using ht,?_⟩
  have he := MicrocodeEmbedding.trace_embed closeBinding.ports Label.close (NativeMatchingXorClose.program pivot)
    (program pivot) (frame (afterB xs a b) (activePos pos a.length a.length)) (close_code pivot) htr
  simpa only [embed_close,hf,hi,ho,hpi,hpo] using he

theorem sealB_trace (pivot : Fin q) (a b : List (List (Bool×Bool))) (xs : List Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 1, Trace pivot t (cfg .sealB (closedA xs a b) (closedPos pos a.length)).denote
      (cfg .done (finish xs a b) (finalPos pos a.length)).denote := by
  have h : NativeZipper.run (program pivot) 1 (cfg .sealB (closedA xs a b) (closedPos pos a.length))=
      cfg .done (finish xs a b) (finalPos pos a.length) := by
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
      Microcode.Action.apply]
    constructor
    · funext p;cases p with
      | count b => cases b <;> rfl
      | opcode => rfl
      | mask b p => cases b <;> simp [closedA,finish,bank,leftOpen,Counter.marked,Tape.moveRight,Tape.write,Tape.read]
    · funext p;cases p with
      | count b => cases b <;> rfl
      | opcode => simp [closedPos,activePos,finalPos,NativeMicrocode.direction,Transpose.Dir.shift];ring
      | mask b p => cases b <;> simp [closedPos,activePos,finalPos,NativeMicrocode.direction,Transpose.Dir.shift]
  exact NativeZipper.trace_of_run (program pivot) h

theorem complete_trace (pivot : Fin q) (a b : List (List (Bool×Bool)))
    (ha : ∀x∈a,x.length=q) (hb : ∀x∈b,x.length=q) (hab : b.length=a.length)
    (xs : List Bool) (hv : Counter.value xs=a.length) (pos : Port q → ℤ) :
    ∃ t ≤ a.length*(6*q+24)+8*xs.length+27, Trace pivot t
      (cfg .leftA (initial xs (NativeMatchingXorMasks.encode (a++b))) pos).denote
      (cfg .done (finish xs a b) (finalPos pos a.length)).denote := by
  obtain ⟨s,hs,ts⟩ := initialize_trace pivot xs (NativeMatchingXorMasks.encode (a++b)) pos
  obtain ⟨u,hu,tu⟩ := first_half_trace pivot a b ha xs hv pos
  have j1 := jump_trace pivot (.masks false (.count 12)) (.masks true (.count 0))
    (afterA xs a b) (activePos pos a.length 0) (by simp [program])
  obtain ⟨v,hv',tv⟩ := second_half_trace pivot a b hb xs (hv.trans hab.symm) pos
  have j2 := jump_trace pivot (.masks true (.count 12)) (.close .seal)
    (afterB xs a b) (activePos pos a.length a.length) (by simp [program])
  obtain ⟨w,hw,tw⟩ := close_trace pivot a b hab xs pos
  have j3 := jump_trace pivot (.close .done) .sealB (closedA xs a b) (closedPos pos a.length) rfl
  obtain ⟨z,hz,tz⟩ := sealB_trace pivot a b xs pos
  refine ⟨s+u+1+v+1+w+1+z,?_,?_⟩
  · rw [hab] at hv'
    nlinarith
  · rw [hab] at tv
    exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
      (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans
        (NativeCountedLoop.trace_trans ts tu) j1) tv) j2) tw) j3) tz

end TransposeFollowup.NativeMatchingXorMaskLayout
