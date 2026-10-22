import TransposeFollowup.OpcodeGeneratorMeaning
import TransposeFollowup.ExactZipperTrace
import TransposeFollowup.NativeCountedLoop
import TransposeFollowup.FusedPageClockIO
import TransposeFollowup.NativeSpanRewind
import TransposeFollowup.NativeIOUnselectedWork
import TransposeFollowup.NativeIOFusionRun
import TransposeFollowup.NativeIOOnlyWork
import TransposeFollowup.RationalOpcodeWalk

/-! One fixed finite decoder reads the existing two-bit opcode encoding.
The page count q is a machine constant. No input length or row number is
stored in a label. The encoded tape is read without changing its cells. -/
namespace TransposeFollowup.OpcodeDecoder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false

instance : Fintype PageOpcode where
  elems:={.idle,.openEdge,.closeEdge}
  complete:=by intro a;cases a <;> simp
abbrev Ops (q : ℕ) := Fin q → PageOpcode

inductive Label (q : ℕ)
  | first (i : Fin q) (ops : Ops q)
  | moveFirst (i : Fin q) (ops : Ops q) (bit : Bool)
  | second (i : Fin q) (ops : Ops q) (bit : Bool)
  | moveSecond (i : Fin q) (ops : Ops q)
  | done (ops : Ops q)
  | reject
  deriving DecidableEq,Fintype

def atIndex {q : ℕ} (k : ℕ) (ops : Ops q) : Label q :=
  if h:k<q then .first ⟨k,h⟩ ops else .done ops

def decode : Bool → Bool → Option PageOpcode
  | false,false => some .idle
  | true,false => some .openEdge
  | true,true => some .closeEdge
  | false,true => none

def program (q : ℕ) : Microcode.Program (Fin 1) (Label q)
  | .first i ops => .read 0 (fun s => match s with
      | .data b => .moveFirst i ops b | _ => .reject)
  | .moveFirst i ops b => .act (fun _ => ⟨none,.right⟩) (.second i ops b)
  | .second i ops b => .read 0 (fun s => match s with
      | .data c => match decode b c with
        | some a => .moveSecond i (Function.update ops i a) | none => .reject
      | _ => .reject)
  | .moveSecond i ops => .act (fun _ => ⟨none,.right⟩) (atIndex (i.val+1) ops)
  | .done _ => .halt
  | .reject => .reject

def start (q : ℕ) : Label q := atIndex 0 (fun _ => .idle)
def cfg {q : ℕ} (pc : Label q) (word : Tape Bool) (pos : Fin 1 → ℤ) : NativeZipper.Config (Fin 1) (Label q) :=
  ⟨⟨pc,fun _ => word⟩,pos⟩

theorem four_steps {q : ℕ} (i : Fin q) (ops : Ops q) (a : PageOpcode)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program q) 4 (cfg (.first i ops) ⟨pre,symbols (PageLoop.opcodeBits a)++post⟩ pos)=
      cfg (atIndex (i.val+1) (Function.update ops i a)) ⟨(symbols (PageLoop.opcodeBits a)).reverse++pre,post⟩
        (NativeZipper.shiftPositions pos 2) := by
  cases a <;> simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    PageLoop.opcodeBits,symbols,Microcode.Action.apply,Tape.read,Tape.moveRight,decode,NativeMicrocode.direction,
    Transpose.Dir.shift]
  all_goals funext p;dsimp [NativeZipper.shiftPositions];omega

theorem four_trace {q : ℕ} (i : Fin q) (ops : Ops q) (a : PageOpcode)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    OperationalTrace.Trace (NativeMicrocode.step (program q)) (NativeMicrocode.Active (program q)) 4
      (cfg (.first i ops) ⟨pre,symbols (PageLoop.opcodeBits a)++post⟩ pos).denote
      (cfg (atIndex (i.val+1) (Function.update ops i a)) ⟨(symbols (PageLoop.opcodeBits a)).reverse++pre,post⟩
        (NativeZipper.shiftPositions pos 2)).denote := by
  have ha : ∀ s,s<4 → NativeMicrocode.Active (program q)
      (NativeZipper.run (program q) s (cfg (.first i ops) ⟨pre,symbols (PageLoop.opcodeBits a)++post⟩ pos)).denote := by
    intro s hs
    interval_cases s <;> cases a <;>
      simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
        PageLoop.opcodeBits,symbols,Microcode.Action.apply,Tape.read,Tape.moveRight,decode,NativeMicrocode.direction,
        Transpose.Dir.shift,NativeMicrocode.Active,NativeZipper.Config.denote,Microcode.Config.denote]
  have h:=NativeZipper.exact_trace (program q) 4 _ ha
  simpa only [four_steps] using h

end TransposeFollowup.OpcodeDecoder


namespace TransposeFollowup.OpcodeDecoder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

def patch (ops base : Ops q) (k : ℕ) : Ops q := fun p => if p.val<k then ops p else base p

theorem patch_zero (ops base : Ops q) : patch ops base 0=base := by funext p;simp [patch]
theorem patch_full (ops base : Ops q) : patch ops base q=ops := by funext p;simp [patch,p.isLt]
theorem patch_update (ops base : Ops q) (k : ℕ) (hk : k<q) :
    Function.update (patch ops base k) ⟨k,hk⟩ (ops ⟨k,hk⟩)=patch ops base (k+1) := by
  funext p
  by_cases hp : p=⟨k,hk⟩
  · subst p;simp [patch]
  · have hv : p.val≠k := by intro h;apply hp;exact Fin.ext h
    have he : p.val<k+1 ↔ p.val<k := by omega
    simp [Function.update_of_ne hp,patch,he]

abbrev Trace (q : ℕ) := OperationalTrace.Trace (NativeMicrocode.step (program q)) (NativeMicrocode.Active (program q))

theorem prefix_trace (ops base : Ops q) (m k : ℕ) (hk : k+m ≤ q)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    Trace q (4*m)
      (cfg (atIndex k (patch ops base k)) ⟨pre,symbols (PrefixMembership.segments (fun p => PageLoop.opcodeBits (ops p)) k m)++post⟩ pos).denote
      (cfg (atIndex (k+m) (patch ops base (k+m)))
        ⟨(symbols (PrefixMembership.segments (fun p => PageLoop.opcodeBits (ops p)) k m)).reverse++pre,post⟩
        (NativeZipper.shiftPositions pos (2*(m:ℤ)))).denote := by
  induction m generalizing k pre pos with
  | zero =>
    simp only [mul_zero,Nat.add_zero,PrefixMembership.segments,symbols,List.map_nil,List.nil_append,
      List.reverse_nil,Nat.cast_zero,NativeZipper.shiftPositions_zero]
    exact .refl _
  | succ m ih =>
    have hkq : k<q:=by omega
    have ha:=four_trace (⟨k,hkq⟩ : Fin q) (patch ops base k) (ops ⟨k,hkq⟩) pre
      (symbols (PrefixMembership.segments (fun p => PageLoop.opcodeBits (ops p)) (k+1) m)++post) pos
    rw [patch_update] at ha
    have hb:=ih (k+1) (by omega) ((symbols (PageLoop.opcodeBits (ops ⟨k,hkq⟩))).reverse++pre)
      (NativeZipper.shiftPositions pos 2)
    have hn : 4+4*m=4*(m+1):=by omega
    have hp : (2:ℤ)+2*m=2*((m+1:ℕ):ℤ):=by push_cast;ring
    have he : k+1+m=k+(m+1):=by omega
    have hs : atIndex k (patch ops base k)=.first ⟨k,hkq⟩ (patch ops base k):=by simp [atIndex,hkq]
    simpa only [PrefixMembership.segments,hkq,↓reduceDIte,symbols,List.map_append,List.append_assoc,
      List.reverse_append,NativeZipper.shiftPositions_add,hn,hp,he,hs] using NativeCountedLoop.trace_trans ha hb

def word (ops : Ops q) : List Bool := (List.ofFn ops).flatMap PageLoop.opcodeBits

theorem segments_word (ops : Ops q) : PrefixMembership.segments (fun p => PageLoop.opcodeBits (ops p)) 0 q=word ops := by
  rw [PrefixMembership.segments_ofFn _ _ _ (by omega)]
  simp [word,List.ofFn_eq_map,List.flatMap_def,Function.comp_def]

theorem opcodeBits_length (a : PageOpcode) : (PageLoop.opcodeBits a).length=2 := by cases a <;> rfl

theorem word_length (ops : Ops q) : (word ops).length=2*q := by
  simp [word,List.length_flatMap,opcodeBits_length,Function.comp_def,List.ofFn_const,Nat.mul_comm]

theorem complete_trace (ops : Ops q) (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    Trace q (4*q) (cfg (start q) ⟨pre,symbols (word ops)++post⟩ pos).denote
      (cfg (.done ops) ⟨(symbols (word ops)).reverse++pre,post⟩ (NativeZipper.shiftPositions pos (2*(q:ℤ)))).denote := by
  have h:=prefix_trace ops (fun _ => .idle) q 0 (by omega) pre post pos
  simpa only [segments_word,Nat.zero_add,patch_zero,patch_full,start,atIndex,lt_self_iff_false,↓reduceDIte] using h

end TransposeFollowup.OpcodeDecoder


namespace TransposeFollowup.OpcodeDecoder
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem invalid_pair (i : Fin q) (ops : Ops q) (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program q) 3 (cfg (.first i ops) ⟨pre,.data false::.data true::post⟩ pos)=
      cfg .reject ⟨.data false::pre,.data true::post⟩ (NativeZipper.shiftPositions pos 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,
    Microcode.Action.apply,Tape.read,Tape.moveRight,decode,NativeMicrocode.direction,Transpose.Dir.shift]
  rfl

theorem malformed_first (i : Fin q) (ops : Ops q) (s : Sym Bool) (hs : ∀ b,s≠.data b)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program q) 1 (cfg (.first i ops) ⟨pre,s::post⟩ pos)=cfg .reject ⟨pre,s::post⟩ pos := by
  cases s <;> simp_all [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Tape.read]

theorem malformed_second (i : Fin q) (ops : Ops q) (b : Bool) (s : Sym Bool) (hs : ∀ b,s≠.data b)
    (pre post : List (Sym Bool)) (pos : Fin 1 → ℤ) :
    NativeZipper.run (program q) 1 (cfg (.second i ops b) ⟨pre,s::post⟩ pos)=cfg .reject ⟨pre,s::post⟩ pos := by
  cases s <;> simp_all [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,Tape.read]

end TransposeFollowup.OpcodeDecoder


/-! Read an opcode vector from the tape and use that decoded vector to
select the fused clock routine. One fixed finite machine supports every
vector of its fixed page count q. The clock word still starts prepared. -/
namespace TransposeFollowup.RowClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port (q : ℕ) := Fin 1 ⊕ ReusablePageClock.Port q
inductive Label (q : ℕ)
  | rewind (pc : NativeSpanRewind.Label)
  | decode (pc : OpcodeDecoder.Label q)
  | clock (ops : OpcodeDecoder.Ops q) (pc : ReusablePageClock.Label)
  deriving DecidableEq,Fintype

def dataBinding (q : ℕ) : FinitePortBinding (Fin 1) (Port q) where
  ports:=Function.Embedding.inl
  decode | .inl p => some p | .inr _ => none
  decode_spec:=by intro p t;cases p <;> simp [eq_comm]
def clockBinding (q : ℕ) : FinitePortBinding (ReusablePageClock.Port q) (Port q) where
  ports:=Function.Embedding.inr
  decode | .inl _ => none | .inr p => some p
  decode_spec:=by intro p t;cases p <;> simp [eq_comm]

def program (q : ℕ) : NativeIO.Program (Port q) (Label q)
  | .rewind .done => .work (.jump (.decode (OpcodeDecoder.start q)))
  | .rewind pc => .work ((dataBinding q).instruction Label.rewind (NativeSpanRewind.program pc))
  | .decode (.done ops) => .work (.jump (.clock ops (.inl .read)))
  | .decode pc => .work ((dataBinding q).instruction Label.decode (OpcodeDecoder.program q pc))
  | .clock ops pc => .work ((clockBinding q).instruction (Label.clock ops) (ReusablePageClock.program ops pc))
def selected (q : ℕ) : Label q → Bool
  | .clock _ pc => FusedPageClock.selected pc
  | _ => false

def cfg (pc : Label q) (data clock : Tape Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ)
    (ip : ℤ) (outRev : List Bool) : NativeIO.Config (Port q) (Label q) :=
  ⟨⟨⟨pc,Sum.elim (fun _ => data.denote) (PageClock.bank clock)⟩,Sum.elim dpos cpos⟩,ip,outRev⟩
def frame (data clock : Tape Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) : MicrocodeEmbedding.Frame (Port q) :=
  ⟨Sum.elim (fun _ => data.denote) (PageClock.bank clock),Sum.elim dpos cpos⟩
abbrev Trace (q : ℕ) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program q) (selected q) w) (NativeIOFusion.Active (program q) (selected q))

theorem rewind_code (q : ℕ) (pc : NativeSpanRewind.Label)
    (hh : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program q) (.rewind pc)=MicrocodeEmbedding.instruction (dataBinding q).ports Label.rewind (NativeSpanRewind.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]
theorem decode_code (q : ℕ) (pc : OpcodeDecoder.Label q)
    (hh : OpcodeDecoder.program q pc≠.halt) (_ : OpcodeDecoder.program q pc≠.reject) :
    NativeIO.workProgram (program q) (.decode pc)=MicrocodeEmbedding.instruction (dataBinding q).ports Label.decode (OpcodeDecoder.program q pc) := by
  cases pc with
  | done ops => exact False.elim (hh rfl)
  | _ => simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]
theorem clock_code (ops : OpcodeDecoder.Ops q) (pc : ReusablePageClock.Label) :
    NativeIO.workProgram (program q) (.clock ops pc)=
      MicrocodeEmbedding.instruction (clockBinding q).ports (Label.clock ops) (ReusablePageClock.program ops pc) := by
  simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

theorem embed_decode (pc : OpcodeDecoder.Label q) (data base clock : Tape Bool)
    (dpos basePos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (ip : ℤ) (outRev : List Bool) :
    (⟨MicrocodeEmbedding.embed (dataBinding q).ports Label.decode (OpcodeDecoder.cfg pc data dpos).denote
      (frame base clock basePos cpos),ip,outRev⟩ : NativeIO.Config (Port q) (Label q))=cfg (.decode pc) data clock dpos cpos ip outRev := by
  unfold MicrocodeEmbedding.embed OpcodeDecoder.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [← (dataBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

theorem embed_clock (ops : OpcodeDecoder.Ops q) (pc : ReusablePageClock.Label) (data clock base : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos basePos : ReusablePageClock.Port q → ℤ) (ip : ℤ) (outRev : List Bool) :
    (⟨MicrocodeEmbedding.embed (clockBinding q).ports (Label.clock ops) (ReusablePageClock.cfg pc clock cpos)
      (frame data base dpos basePos),ip,outRev⟩ : NativeIO.Config (Port q) (Label q))=cfg (.clock ops pc) data clock dpos cpos ip outRev := by
  unfold MicrocodeEmbedding.embed ReusablePageClock.cfg frame cfg
  simp only [← (clockBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

theorem embed_rewind (pc : NativeSpanRewind.Label) (data base clock : Tape Bool)
    (dpos basePos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (ip : ℤ) (outRev : List Bool) :
    (⟨MicrocodeEmbedding.embed (dataBinding q).ports Label.rewind (NativeSpanRewind.cfg pc data dpos).denote
      (frame base clock basePos cpos),ip,outRev⟩ : NativeIO.Config (Port q) (Label q))=cfg (.rewind pc) data clock dpos cpos ip outRev := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote frame cfg
  simp only [← (dataBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

end TransposeFollowup.RowClock


namespace TransposeFollowup.RowClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem decode_trace (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (4*q) (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos ip outRev)
      (cfg (.decode (.done ops)) ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ clock
        (NativeZipper.shiftPositions dpos (2*(q:ℤ))) cpos ip outRev) := by
  have h:=NativeIOFusionCalls.unselected_work_trace (dataBinding q).ports Label.decode (OpcodeDecoder.program q)
    (program q) (selected q) (frame ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos) w ip outRev
    (fun _ => rfl) (decode_code q) (OpcodeDecoder.complete_trace ops pre post dpos)
  simpa only [embed_decode] using h

theorem decode_transfer (ops : OpcodeDecoder.Ops q) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg (.decode (.done ops)) data clock dpos cpos ip outRev)
      (cfg (.clock ops (.inl .read)) data clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

theorem decode_and_transfer (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (4*q+1) (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos ip outRev)
      (cfg (.clock ops (.inl .read)) ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ clock
        (NativeZipper.shiftPositions dpos (2*(q:ℤ))) cpos ip outRev) :=
  NativeCountedLoop.trace_trans (decode_trace ops pre post clock dpos cpos w ip outRev)
    (decode_transfer ops _ clock _ cpos w ip outRev)

theorem clock_trace (ops : OpcodeDecoder.Ops q) (data : Tape Bool) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (2*xs.length+3) (cfg (.clock ops (.inl .read)) data (Counter.marked xs) dpos cpos ip outRev)
      (cfg (.clock ops (.inr .done)) data (Counter.marked xs) dpos (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
  have h:=FusedPageClockIO.trace_call ops (clockBinding q).ports (Label.clock ops) (program q) (selected q)
    (frame data (Counter.marked xs) dpos cpos) (fun _ => rfl) (fun pc _ => clock_code ops pc) xs cpos w ip outRev
  simpa only [embed_clock] using h

theorem row_trace (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (4*q+2*xs.length+4)
      (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
  have ha:=decode_and_transfer ops pre post (Counter.marked xs) dpos cpos w ip outRev
  have hb:=clock_trace ops ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ xs (NativeZipper.shiftPositions dpos (2*(q:ℤ))) cpos w ip outRev
  simpa only [show (4*q+1)+(2*xs.length+3)=4*q+2*xs.length+4 by omega] using NativeCountedLoop.trace_trans ha hb

noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (.rewind .left : Label q)
noncomputable def nativeMachine (q : ℕ) := NativeIOFusion.machine (nativeEncoding q) (program q) (selected q)

theorem native_row (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine q) w (4*q+2*xs.length+4)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev))=
      some (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs)
          (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev)) :=
  NativeIOFusion.trace_stepN _ _ _ w (row_trace ops pre post xs dpos cpos w ip outRev)

theorem final_halts (ops : OpcodeDecoder.Ops q) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.step (nativeMachine q) w
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q) (cfg (.clock ops (.inr .done)) data clock dpos cpos ip outRev))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,cfg,program,FinitePortBinding.instruction,ReusablePageClock.program,NativeSealBack.program]

theorem fixed_tapes (q : ℕ) : (nativeMachine q).k=q+2 ∧ (nativeMachine q).g+1=5 ∧
    (nativeEncoding q).label (.rewind .left)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Port q)=q+2
  simp [Port,ReusablePageClock.Port,PageClock.Port];omega

end TransposeFollowup.RowClock


namespace TransposeFollowup.RowClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem decode_page_trajectory (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 4*q) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) s
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=cpos (some p) := by
  have ht:=OperationalTrace.take_trace (OpcodeDecoder.complete_trace ops pre post dpos) s hs
  have he:=OperationalTrace.trace_run (NativeIOFusionCalls.unselected_work_trace (dataBinding q).ports Label.decode (OpcodeDecoder.program q)
    (program q) (selected q) (frame ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos) w ip outRev
    (fun _ => rfl) (decode_code q) ht)
  simp only [embed_decode] at he
  unfold nativeMachine
  rw [NativeIOFusion.run_denote]
  simp only [NativeIOFusion.run]
  rw [he]
  simp only [NativeIOFusion.denote,Equiv.symm_apply_apply,MicrocodeEmbedding.embed]
  have hu : ¬∃ t,(dataBinding q).ports t=Sum.inr (some p) := by rintro ⟨t,h⟩;cases h
  rw [MicrocodeEmbedding.extend_outside (dataBinding q).ports _ hu]
  rfl

theorem clock_suffix_trajectory (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 2*xs.length+3) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) (4*q+1+s)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=cpos (some p)+(ops p).direction*((xs.take s).count true) := by
  have hr:=OperationalTrace.trace_run (decode_and_transfer ops pre post (Counter.marked xs) dpos cpos w ip outRev)
  unfold nativeMachine
  rw [OperationalTrace.run_add]
  rw [NativeIOFusion.run_denote (nativeEncoding q) (program q) (selected q) w (4*q+1)]
  simp only [NativeIOFusion.run]
  rw [hr]
  have h:=FusedPageClockIO.native_page_trajectory (nativeEncoding q) ops (clockBinding q).ports (Label.clock ops)
    (program q) (selected q)
    (frame ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs) (NativeZipper.shiftPositions dpos (2*(q:ℤ))) cpos)
    (fun _ => rfl) (fun pc _ => clock_code ops pc) xs cpos w ip outRev s hs p
  simpa only [embed_clock,show (clockBinding q).ports (some p)=Sum.inr (some p) from rfl] using h

theorem row_page_trajectory (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 4*q+2*xs.length+4) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) s
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=cpos (some p)+(ops p).direction*((xs.take (s-(4*q+1))).count true) := by
  by_cases hd : s ≤ 4*q
  · rw [decode_page_trajectory ops pre post (Counter.marked xs) dpos cpos w ip outRev s hd p]
    simp [show s-(4*q+1)=0 by omega]
  · have he : s=4*q+1+(s-(4*q+1)):=by omega
    conv_lhs => rw [he]
    exact clock_suffix_trajectory ops pre post xs dpos cpos w ip outRev _ (by omega) p

theorem native_record_trajectory (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (R : ℕ)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 14*R+4*q+4) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) s
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg (.decode (OpcodeDecoder.start q)) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩
          (Counter.marked (SevenPhaseClock.word R)) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=recordRun R (ops p) (cpos (some p)) (s-(4*q+1)) := by
  have ht : s ≤ 4*q+2*(SevenPhaseClock.word R).length+4:=by rw [SevenPhaseClock.word_length];omega
  rw [row_page_trajectory ops pre post _ dpos cpos w ip outRev s ht p,SevenPhaseClock.count_ramp,recordRun_eq]

end TransposeFollowup.RowClock


namespace TransposeFollowup.RowClock
open FixedTapeCompiler
set_option autoImplicit false
variable {q : ℕ}

theorem only_work (q : ℕ) : NativeIOFusion.OnlyWork (program q) := by
  intro pc
  cases pc with
  | rewind pc => cases pc <;> exact ⟨_,rfl⟩
  | decode pc => cases pc <;> exact ⟨_,rfl⟩
  | clock ops pc => exact ⟨_,rfl⟩

theorem selected_next_ne_return (pc : Label q) (hs : selected q pc=true) (t : Port q)
    (next : CopyMachine.Sym Bool → Label q)
    (h : NativeIO.workProgram (program q) pc=.read t next) (s : CopyMachine.Sym Bool) (ops : OpcodeDecoder.Ops q) :
    next s≠.clock ops (.inr .done) := by
  cases pc with
  | rewind pc => simp [selected] at hs
  | decode pc => simp [selected] at hs
  | clock a pc =>
    cases hc : ReusablePageClock.program a pc with
    | read u f =>
      simp only [NativeIO.workProgram,program,hc,FinitePortBinding.instruction,Microcode.Instruction.read.injEq] at h
      rcases h with ⟨_,rfl⟩
      intro he
      have hd:= (Label.clock.inj he).2
      exact FusedPageClockIO.read_next_ne_done a pc u f hc s hd
    | _ => simp [NativeIO.workProgram,program,hc,FinitePortBinding.instruction] at h

end TransposeFollowup.RowClock


namespace TransposeFollowup.RowClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem rewind_trace (bits : List Bool) (clock : Tape Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*bits.length+3,Trace q w t
      (cfg (.rewind .left) ⟨(symbols bits).reverse,[]⟩ clock dpos cpos ip outRev)
      (cfg (.rewind .done) ⟨[],symbols bits⟩ clock (fun p => dpos p-bits.length) cpos ip outRev) := by
  have hh : ∀ s ∈ symbols bits,s≠.blank := by
    intro s hs
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
    simp
  obtain ⟨t,ht,htr⟩:=NativeSpanRewind.rewind_trace (symbols bits) hh dpos
  have h:=NativeIOFusionCalls.unselected_work_trace (dataBinding q).ports Label.rewind NativeSpanRewind.program
    (program q) (selected q) (frame ⟨(symbols bits).reverse,[]⟩ clock dpos cpos) w ip outRev
    (fun _ => rfl) (rewind_code q) htr
  refine ⟨t,by simpa only [symbols,List.length_map] using ht,?_⟩
  simpa only [embed_rewind,symbols,List.length_map] using h

theorem rewind_transfer (data clock : Tape Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg (.rewind .done) data clock dpos cpos ip outRev)
      (cfg (.decode (OpcodeDecoder.start q)) data clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

theorem rewound_row (ops : OpcodeDecoder.Ops q) (tail xs : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(OpcodeDecoder.word ops++tail).length+4*q+2*xs.length+8,Trace q w t
      (cfg (.rewind .left) ⟨(symbols (OpcodeDecoder.word ops++tail)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse,symbols tail⟩ (Counter.marked xs)
        (fun p => dpos p-tail.length) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
  obtain ⟨t,ht,ha⟩:=rewind_trace (OpcodeDecoder.word ops++tail) (Counter.marked xs) dpos cpos w ip outRev
  have hb:=rewind_transfer ⟨[],symbols (OpcodeDecoder.word ops++tail)⟩ (Counter.marked xs)
    (fun p => dpos p-(OpcodeDecoder.word ops++tail).length) cpos w ip outRev
  have hc:=row_trace ops [] (symbols tail) xs (fun p => dpos p-(OpcodeDecoder.word ops++tail).length) cpos w ip outRev
  have hp : NativeZipper.shiftPositions (fun p => dpos p-(OpcodeDecoder.word ops++tail).length) (2*(q:ℤ))=
      (fun p => dpos p-tail.length) := by
    funext p
    simp [NativeZipper.shiftPositions,List.length_append,OpcodeDecoder.word_length]
    ring
  have hc' : Trace q w (4*q+2*xs.length+4)
      (cfg (.decode (OpcodeDecoder.start q)) ⟨[],symbols (OpcodeDecoder.word ops++tail)⟩ (Counter.marked xs)
        (fun p => dpos p-(OpcodeDecoder.word ops++tail).length) cpos ip outRev)
      (cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse,symbols tail⟩ (Counter.marked xs)
        (fun p => dpos p-tail.length) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
    simpa only [symbols,List.map_append,List.append_nil,hp] using hc
  exact ⟨t+1+(4*q+2*xs.length+4),by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ha hb) hc'⟩

theorem native_rewound_row (ops : OpcodeDecoder.Ops q) (tail xs : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(OpcodeDecoder.word ops++tail).length+4*q+2*xs.length+8,
      Transpose.stepN (nativeMachine q) w t
        (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
          (cfg (.rewind .left) ⟨(symbols (OpcodeDecoder.word ops++tail)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev))=
        some (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
          (cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse,symbols tail⟩ (Counter.marked xs)
            (fun p => dpos p-tail.length) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev)) := by
  obtain ⟨t,ht,htr⟩:=rewound_row ops tail xs dpos cpos w ip outRev
  exact ⟨t,ht,NativeIOFusion.trace_stepN _ _ _ w htr⟩

end TransposeFollowup.RowClock


/-! A fixed finite loop over a blank-terminated stream of nonempty opcode
rows. It rewinds once and returns from each restored clock call to a guard.
Neither the number of rows nor the clock length is encoded in the labels. -/
namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port (q : ℕ) := RowClock.Port q
inductive Label (q : ℕ)
  | rewind (pc : NativeSpanRewind.Label)
  | body (pc : RowClock.Label q)
  | guard | done | reject
  deriving DecidableEq,Fintype

def bodyBinding (q : ℕ) : FinitePortBinding (Port q) (Port q) where
  ports:=Function.Embedding.refl _
  decode:=some
  decode_spec:=by intros;simp [eq_comm]

def program (q : ℕ) : NativeIO.Program (Port q) (Label q)
  | .rewind .done => .work (.jump .guard)
  | .rewind pc => .work ((RowClock.dataBinding q).instruction Label.rewind (NativeSpanRewind.program pc))
  | .body (.clock _ (.inr .done)) => .work (.jump .guard)
  | .body pc => .work ((bodyBinding q).instruction Label.body (NativeIO.workProgram (RowClock.program q) pc))
  | .guard => .work (.read (.inl 0) (fun s => match s with
      | .blank => .done
      | .data _ => .body (.decode (OpcodeDecoder.start q))
      | _ => .reject))
  | .done => .work .halt
  | .reject => .work .reject

def selected (q : ℕ) : Label q → Bool
  | .body pc => RowClock.selected q pc
  | _ => false

def cfg (pc : Label q) (data clock : Tape Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ)
    (ip : ℤ) (outRev : List Bool) : NativeIO.Config (Port q) (Label q) :=
  ⟨⟨⟨pc,Sum.elim (fun _ => data.denote) (PageClock.bank clock)⟩,Sum.elim dpos cpos⟩,ip,outRev⟩
abbrev Trace (q : ℕ) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program q) (selected q) w) (NativeIOFusion.Active (program q) (selected q))

theorem body_code_except (pc : RowClock.Label q) (h : ∀ ops,pc≠.clock ops (.inr .done)) :
    NativeIO.workProgram (program q) (.body pc)=
      MicrocodeEmbedding.instruction (bodyBinding q).ports Label.body (NativeIO.workProgram (RowClock.program q) pc) := by
  cases pc with
  | clock ops pc =>
    cases pc with
    | inl pc => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]
    | inr pc => cases pc <;> first | exact False.elim (h ops rfl) | simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]
  | _ => simp only [program,NativeIO.workProgram,FinitePortBinding.instruction_eq]

theorem body_code (pc : RowClock.Label q)
    (hh : NativeIO.workProgram (RowClock.program q) pc≠.halt) (_ : NativeIO.workProgram (RowClock.program q) pc≠.reject) :
    NativeIO.workProgram (program q) (.body pc)=
      MicrocodeEmbedding.instruction (bodyBinding q).ports Label.body (NativeIO.workProgram (RowClock.program q) pc) := by
  apply body_code_except pc
  intro ops he
  subst pc
  exact hh rfl

theorem body_read_code (pc : RowClock.Label q) (hs : RowClock.selected q pc=true)
    (t : Port q) (next : Sym Bool → RowClock.Label q)
    (h : NativeIO.workProgram (RowClock.program q) pc=.read t next) (s : Sym Bool) :
    NativeIO.workProgram (program q) (.body (next s))=
      MicrocodeEmbedding.instruction (bodyBinding q).ports Label.body (NativeIO.workProgram (RowClock.program q) (next s)) :=
  body_code_except (next s) (RowClock.selected_next_ne_return pc hs t next h s)

theorem embed_body (pc : RowClock.Label q) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (ip : ℤ) (outRev : List Bool)
    (frame : MicrocodeEmbedding.Frame (Port q)) :
    (⟨MicrocodeEmbedding.embed (bodyBinding q).ports Label.body (RowClock.cfg pc data clock dpos cpos ip outRev).work
      frame,ip,outRev⟩ : NativeIO.Config (Port q) (Label q))=cfg (.body pc) data clock dpos cpos ip outRev := by
  unfold MicrocodeEmbedding.embed RowClock.cfg cfg
  simp only [← (bodyBinding q).values_eq_extend]
  rfl

theorem rewind_code (q : ℕ) (pc : NativeSpanRewind.Label)
    (hh : NativeSpanRewind.program pc≠.halt) (_ : NativeSpanRewind.program pc≠.reject) :
    NativeIO.workProgram (program q) (.rewind pc)=MicrocodeEmbedding.instruction (RowClock.dataBinding q).ports Label.rewind (NativeSpanRewind.program pc) := by
  cases pc with
  | done => exact False.elim (hh rfl)
  | _ => simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

theorem embed_rewind (pc : NativeSpanRewind.Label) (data base clock : Tape Bool)
    (dpos basePos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (ip : ℤ) (outRev : List Bool) :
    (⟨MicrocodeEmbedding.embed (RowClock.dataBinding q).ports Label.rewind (NativeSpanRewind.cfg pc data dpos).denote
      (RowClock.frame base clock basePos cpos),ip,outRev⟩ : NativeIO.Config (Port q) (Label q))=cfg (.rewind pc) data clock dpos cpos ip outRev := by
  unfold MicrocodeEmbedding.embed NativeSpanRewind.cfg NativeZipper.Config.denote Microcode.Config.denote RowClock.frame cfg
  simp only [← (RowClock.dataBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

noncomputable def nativeEncoding (q : ℕ) := NativeMicrocode.initialEncoding (T:=Port q) (.rewind .left : Label q)
noncomputable def nativeMachine (q : ℕ) := NativeIOFusion.machine (nativeEncoding q) (program q) (selected q)

theorem fixed_tapes (q : ℕ) : (nativeMachine q).k=q+2 ∧ (nativeMachine q).g+1=5 ∧
    (nativeEncoding q).label (.rewind .left)=0 := by
  refine ⟨?_,rfl,NativeMicrocode.initialEncoding_start _⟩
  change Fintype.card (Port q)=q+2
  simp [Port,RowClock.Port,ReusablePageClock.Port,PageClock.Port];omega

end TransposeFollowup.RowLoop


namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

def period (q : ℕ) (xs : List Bool) : ℕ := 4*q+2*xs.length+6

theorem body_trace (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (4*q+2*xs.length+4)
      (cfg (.body (.decode (OpcodeDecoder.start q))) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg (.body (.clock ops (.inr .done))) ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
  have ht:=NativeIOFusion.only_work_trace _ (RowClock.only_work q) _ w (RowClock.row_trace ops pre post xs dpos cpos w ip outRev)
  have h:=NativeIOFusionCalls.work_trace (bodyBinding q).ports Label.body (NativeIO.workProgram (RowClock.program q))
    (program q) (RowClock.selected q) (selected q)
    (RowClock.frame ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos) w ip outRev
    (fun _ => rfl) body_code body_read_code ht
  simpa only [embed_body] using h

theorem guard_data (b : Bool) (pre post : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg .guard ⟨pre,.data b::post⟩ clock dpos cpos ip outRev)
      (cfg (.body (.decode (OpcodeDecoder.start q))) ⟨pre,.data b::post⟩ clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep,Sum.elim_inl,denote_read,Tape.read]
    exact .refl _

theorem guard_row (hq : 1 ≤ q) (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg .guard ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos ip outRev)
      (cfg (.body (.decode (OpcodeDecoder.start q))) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ clock dpos cpos ip outRev) := by
  have hlen:=OpcodeDecoder.word_length ops
  cases he : OpcodeDecoder.word ops with
  | nil => rw [he] at hlen;simp at hlen;omega
  | cons b bs => simpa only [symbols,List.map_cons,List.cons_append] using guard_data b pre (symbols bs++post) clock dpos cpos w ip outRev

theorem guard_blank (pre : List (Sym Bool)) (clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg .guard ⟨pre,[]⟩ clock dpos cpos ip outRev)
      (cfg .done ⟨pre,[]⟩ clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep,Sum.elim_inl,denote_read,Tape.read]
    exact .refl _

theorem return_trace (ops : OpcodeDecoder.Ops q) (data clock : Tape Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg (.body (.clock ops (.inr .done))) data clock dpos cpos ip outRev)
      (cfg .guard data clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

theorem iteration_trace (hq : 1 ≤ q) (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (period q xs)
      (cfg .guard ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg .guard ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev) := by
  have ha:=guard_row hq ops pre post (Counter.marked xs) dpos cpos w ip outRev
  have hb:=body_trace ops pre post xs dpos cpos w ip outRev
  have hc:=return_trace ops ⟨(symbols (OpcodeDecoder.word ops)).reverse++pre,post⟩ (Counter.marked xs)
    (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true)) w ip outRev
  simpa only [show 1+(4*q+2*xs.length+4)+1=period q xs by unfold period;omega] using
    NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ha hb) hc

end TransposeFollowup.RowLoop


namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

def bits (rows : List (OpcodeDecoder.Ops q)) : List Bool := rows.flatMap OpcodeDecoder.word
def finishPos (rows : List (OpcodeDecoder.Ops q)) (xs : List Bool) (pos : ReusablePageClock.Port q → ℤ) :
    ReusablePageClock.Port q → ℤ := rows.foldl (fun p ops => PageClock.advance ops p 0 (xs.count true)) pos

theorem bits_length (rows : List (OpcodeDecoder.Ops q)) : (bits rows).length=2*q*rows.length := by
  induction rows with
  | nil => simp [bits]
  | cons ops rows ih =>
    simp only [bits,List.flatMap_cons,List.length_append,OpcodeDecoder.word_length,List.length_cons] at ih ⊢
    rw [ih]
    ring

theorem finish_clock (rows : List (OpcodeDecoder.Ops q)) (xs : List Bool) (pos : ReusablePageClock.Port q → ℤ) :
    finishPos rows xs pos none=pos none := by
  induction rows generalizing pos with
  | nil => rfl
  | cons ops rows ih =>
    change finishPos rows xs (PageClock.advance ops pos 0 (xs.count true)) none=pos none
    rw [ih]
    simp [PageClock.advance]

theorem prefix_trace (hq : 1 ≤ q) (rows : List (OpcodeDecoder.Ops q)) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (rows.length*period q xs)
      (cfg .guard ⟨pre,symbols (bits rows)++post⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg .guard ⟨(symbols (bits rows)).reverse++pre,post⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ)*rows.length)) (finishPos rows xs cpos) ip outRev) := by
  induction rows generalizing pre dpos cpos with
  | nil => simpa only [bits,List.flatMap_nil,symbols,List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,
      Nat.zero_mul,Nat.cast_zero,mul_zero,NativeZipper.shiftPositions_zero,finishPos,List.foldl_nil] using
      (OperationalTrace.Trace.refl (step:=NativeIOFusion.step (program q) (selected q) w)
        (active:=NativeIOFusion.Active (program q) (selected q)) (cfg .guard ⟨pre,post⟩ (Counter.marked xs) dpos cpos ip outRev))
  | cons ops rows ih =>
    have ha:=iteration_trace hq ops pre (symbols (bits rows)++post) xs dpos cpos w ip outRev
    have hb:=ih ((symbols (OpcodeDecoder.word ops)).reverse++pre)
      (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (PageClock.advance ops cpos 0 (xs.count true))
    have hp : NativeZipper.shiftPositions (NativeZipper.shiftPositions dpos (2*(q:ℤ))) (2*(q:ℤ)*rows.length)=
        NativeZipper.shiftPositions dpos (2*(q:ℤ)*(ops::rows).length) := by
      funext p
      simp only [NativeZipper.shiftPositions,List.length_cons,Nat.cast_add,Nat.cast_one]
      ring
    have ht : period q xs+rows.length*period q xs=(ops::rows).length*period q xs := by simp [Nat.add_mul,Nat.add_comm]
    simpa only [bits,List.flatMap_cons,symbols,List.map_append,List.reverse_append,List.append_assoc,finishPos,List.foldl_cons,hp,ht] using
      NativeCountedLoop.trace_trans ha hb

theorem complete_trace (hq : 1 ≤ q) (rows : List (OpcodeDecoder.Ops q)) (pre : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (rows.length*period q xs+1)
      (cfg .guard ⟨pre,symbols (bits rows)⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg .done ⟨(symbols (bits rows)).reverse++pre,[]⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ)*rows.length)) (finishPos rows xs cpos) ip outRev) := by
  have ha:=prefix_trace hq rows pre [] xs dpos cpos w ip outRev
  have hb:=guard_blank ((symbols (bits rows)).reverse++pre) (Counter.marked xs)
    (NativeZipper.shiftPositions dpos (2*(q:ℤ)*rows.length)) (finishPos rows xs cpos) w ip outRev
  simpa only [List.append_nil] using NativeCountedLoop.trace_trans ha hb

theorem native_stream (hq : 1 ≤ q) (rows : List (OpcodeDecoder.Ops q)) (pre : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine q) w (rows.length*period q xs+1)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨pre,symbols (bits rows)⟩ (Counter.marked xs) dpos cpos ip outRev))=
      some (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .done ⟨(symbols (bits rows)).reverse++pre,[]⟩ (Counter.marked xs)
          (NativeZipper.shiftPositions dpos (2*(q:ℤ)*rows.length)) (finishPos rows xs cpos) ip outRev)) :=
  NativeIOFusion.trace_stepN _ _ _ w (complete_trace hq rows pre xs dpos cpos w ip outRev)

theorem final_halts (data clock : Tape Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.step (nativeMachine q) w
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q) (cfg .done data clock dpos cpos ip outRev))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,cfg,program]

end TransposeFollowup.RowLoop


namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem body_page_trajectory (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ 4*q+2*xs.length+4) (p : Fin q) :
    (NativeIOFusion.run (program q) (selected q) w s
      (cfg (.body (.decode (OpcodeDecoder.start q))) ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev)).work.pos
        (.inr (some p))=cpos (some p)+(ops p).direction*((xs.take (s-(4*q+1))).count true) := by
  have ht:=NativeIOFusion.only_work_trace _ (RowClock.only_work q) _ w (RowClock.row_trace ops pre post xs dpos cpos w ip outRev)
  have he:=NativeIOFusionCalls.work_prefix (bodyBinding q).ports Label.body (NativeIO.workProgram (RowClock.program q))
    (program q) (RowClock.selected q) (selected q)
    (RowClock.frame ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos) w ip outRev
    (fun _ => rfl) body_code body_read_code ht s hs
  simp only [embed_body] at he
  rw [he]
  have h:=RowClock.row_page_trajectory ops pre post xs dpos cpos w ip outRev s hs p
  unfold RowClock.nativeMachine at h
  rw [NativeIOFusion.run_denote,NativeIOFusion.only_work_run _ (RowClock.only_work q)] at h
  simp only [MicrocodeEmbedding.embed]
  change Function.extend (bodyBinding q).ports _ _ ((bodyBinding q).ports (.inr (some p)))=_
  rw [MicrocodeEmbedding.extend_at]
  simpa only [NativeIOFusion.denote,Equiv.symm_apply_apply] using h

theorem iteration_page_trajectory (hq : 1 ≤ q) (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ period q xs) (p : Fin q) :
    (NativeIOFusion.run (program q) (selected q) w s
      (cfg .guard ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev)).work.pos
        (.inr (some p))=cpos (some p)+(ops p).direction*((xs.take (s-(4*q+2))).count true) := by
  by_cases hz : s=0
  · subst s;simp [NativeIOFusion.run,OperationalTrace.run,cfg]
  by_cases hf : s=period q xs
  · subst s
    have hr:=OperationalTrace.trace_run (iteration_trace hq ops pre post xs dpos cpos w ip outRev)
    simp only [NativeIOFusion.run]
    rw [hr]
    have hl : xs.length ≤ period q xs-(4*q+2):=by unfold period;omega
    rw [List.take_of_length_le hl]
    rfl
  · have hb : s-1 ≤ 4*q+2*xs.length+4:=by unfold period at hs hf;omega
    have hr:=OperationalTrace.trace_run (guard_row hq ops pre post (Counter.marked xs) dpos cpos w ip outRev)
    have hh:=body_page_trajectory ops pre post xs dpos cpos w ip outRev (s-1) hb p
    simp only [NativeIOFusion.run]
    conv_lhs => rw [show s=1+(s-1) by omega]
    rw [OperationalTrace.run_add,hr]
    simpa only [NativeIOFusion.run,show s-1-(4*q+1)=s-(4*q+2) by omega] using hh

theorem native_iteration_trajectory (hq : 1 ≤ q) (ops : OpcodeDecoder.Ops q) (pre post : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool)
    (s : ℕ) (hs : s ≤ period q xs) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) s
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨pre,symbols (OpcodeDecoder.word ops)++post⟩ (Counter.marked xs) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=
      cpos (some p)+(ops p).direction*((xs.take (s-(4*q+2))).count true) := by
  unfold nativeMachine
  rw [NativeIOFusion.run_denote]
  simpa only [NativeIOFusion.denote,Equiv.symm_apply_apply] using
    iteration_page_trajectory hq ops pre post xs dpos cpos w ip outRev s hs p

end TransposeFollowup.RowLoop


/-! Boundaries and pointwise paths for every row in the same native run.
An arbitrary prefix/suffix split represents any requested row index. -/
namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem stream_prefix (hq : 1 ≤ q) (front tail : List (OpcodeDecoder.Ops q)) (pre : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w (front.length*period q xs)
      (cfg .guard ⟨pre,symbols (bits (front++tail))⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg .guard ⟨(symbols (bits front)).reverse++pre,symbols (bits tail)⟩ (Counter.marked xs)
        (NativeZipper.shiftPositions dpos (2*(q:ℤ)*front.length)) (finishPos front xs cpos) ip outRev) := by
  simpa only [bits,List.flatMap_append,symbols,List.map_append] using
    prefix_trace hq front pre (symbols (bits tail)) xs dpos cpos w ip outRev

theorem native_boundary (hq : 1 ≤ q) (front tail : List (OpcodeDecoder.Ops q)) (pre : List (Sym Bool)) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Transpose.stepN (nativeMachine q) w (front.length*period q xs)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨pre,symbols (bits (front++tail))⟩ (Counter.marked xs) dpos cpos ip outRev))=
      some (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨(symbols (bits front)).reverse++pre,symbols (bits tail)⟩ (Counter.marked xs)
          (NativeZipper.shiftPositions dpos (2*(q:ℤ)*front.length)) (finishPos front xs cpos) ip outRev)) :=
  NativeIOFusion.trace_stepN _ _ _ w (stream_prefix hq front tail pre xs dpos cpos w ip outRev)

theorem native_stream_trajectory (hq : 1 ≤ q) (front tail : List (OpcodeDecoder.Ops q)) (ops : OpcodeDecoder.Ops q)
    (pre : List (Sym Bool)) (xs : List Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (s : ℕ) (hs : s ≤ period q xs) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) (front.length*period q xs+s)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨pre,symbols (bits (front++ops::tail))⟩ (Counter.marked xs) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=
      finishPos front xs cpos (some p)+(ops p).direction*((xs.take (s-(4*q+2))).count true) := by
  have hr:=OperationalTrace.trace_run (stream_prefix hq front (ops::tail) pre xs dpos cpos w ip outRev)
  unfold nativeMachine
  rw [OperationalTrace.run_add,NativeIOFusion.run_denote (nativeEncoding q) (program q) (selected q) w (front.length*period q xs)]
  simp only [NativeIOFusion.run]
  rw [hr]
  simpa only [nativeMachine,bits,List.flatMap_cons,symbols,List.map_append] using
    native_iteration_trajectory hq ops ((symbols (bits front)).reverse++pre) (symbols (bits tail)) xs
      (NativeZipper.shiftPositions dpos (2*(q:ℤ)*front.length)) (finishPos front xs cpos) w ip outRev s hs p

theorem native_record_trajectory (hq : 1 ≤ q) (front tail : List (OpcodeDecoder.Ops q)) (ops : OpcodeDecoder.Ops q)
    (pre : List (Sym Bool)) (R : ℕ) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port q → ℤ)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) (s : ℕ) (hs : s ≤ 14*R+4*q+6) (p : Fin q) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine q) w) (front.length*(14*R+4*q+6)+s)
      (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
        (cfg .guard ⟨pre,symbols (bits (front++ops::tail))⟩ (Counter.marked (SevenPhaseClock.word R)) dpos cpos ip outRev))).workPos
          ((nativeEncoding q).port (.inr (some p)))=
      recordRun R (ops p) (finishPos front (SevenPhaseClock.word R) cpos (some p)) (s-(4*q+2)) := by
  have hp : period q (SevenPhaseClock.word R)=14*R+4*q+6:=by rw [period,SevenPhaseClock.word_length];omega
  have ht:=native_stream_trajectory hq front tail ops pre (SevenPhaseClock.word R) dpos cpos w ip outRev s (by omega) p
  simpa only [hp,SevenPhaseClock.count_ramp,recordRun_eq] using ht

end TransposeFollowup.RowLoop


namespace TransposeFollowup.RowLoop
open FixedTapeCompiler
set_option autoImplicit false

theorem only_work (q : ℕ) : NativeIOFusion.OnlyWork (program q) := by
  intro pc
  unfold program
  split <;> exact ⟨_,rfl⟩

end TransposeFollowup.RowLoop


namespace TransposeFollowup.RowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}

theorem rewind_trace (word : List Bool) (clock : Tape Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*word.length+3,Trace q w t
      (cfg (.rewind .left) ⟨(symbols word).reverse,[]⟩ clock dpos cpos ip outRev)
      (cfg (.rewind .done) ⟨[],symbols word⟩ clock (fun p => dpos p-word.length) cpos ip outRev) := by
  have hh : ∀ s ∈ symbols word,s≠.blank := by
    intro s hs
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp hs
    simp
  obtain ⟨t,ht,htr⟩:=NativeSpanRewind.rewind_trace (symbols word) hh dpos
  have h:=NativeIOFusionCalls.unselected_work_trace (RowClock.dataBinding q).ports Label.rewind NativeSpanRewind.program
    (program q) (selected q) (RowClock.frame ⟨(symbols word).reverse,[]⟩ clock dpos cpos) w ip outRev
    (fun _ => rfl) (rewind_code q) htr
  refine ⟨t,by simpa only [symbols,List.length_map] using ht,?_⟩
  simpa only [embed_rewind,symbols,List.length_map] using h

theorem rewind_transfer (data clock : Tape Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    Trace q w 1 (cfg (.rewind .done) data clock dpos cpos ip outRev)
      (cfg .guard data clock dpos cpos ip outRev) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,cfg,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,cfg,program,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

theorem rewound_stream (hq : 1 ≤ q) (rows : List (OpcodeDecoder.Ops q)) (xs : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(bits rows).length+rows.length*period q xs+5,Trace q w t
      (cfg (.rewind .left) ⟨(symbols (bits rows)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev)
      (cfg .done ⟨(symbols (bits rows)).reverse,[]⟩ (Counter.marked xs) dpos (finishPos rows xs cpos) ip outRev) := by
  obtain ⟨t,ht,ha⟩:=rewind_trace (bits rows) (Counter.marked xs) dpos cpos w ip outRev
  have hb:=rewind_transfer ⟨[],symbols (bits rows)⟩ (Counter.marked xs)
    (fun p => dpos p-(bits rows).length) cpos w ip outRev
  have hc:=complete_trace hq rows [] xs (fun p => dpos p-(bits rows).length) cpos w ip outRev
  have hp : NativeZipper.shiftPositions (fun p => dpos p-(bits rows).length) (2*(q:ℤ)*rows.length)=dpos := by
    funext p
    simp only [NativeZipper.shiftPositions,bits_length,Nat.cast_mul,Nat.cast_ofNat]
    ring
  refine ⟨t+1+(rows.length*period q xs+1),by omega,?_⟩
  simpa only [hp,List.append_nil] using NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ha hb) hc

theorem native_rewound_stream (hq : 1 ≤ q) (rows : List (OpcodeDecoder.Ops q)) (xs : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port q → ℤ) (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 2*(bits rows).length+rows.length*period q xs+5,
      Transpose.stepN (nativeMachine q) w t
        (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
          (cfg (.rewind .left) ⟨(symbols (bits rows)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev))=
        some (NativeIOFusion.denote (nativeEncoding q) (program q) (selected q)
          (cfg .done ⟨(symbols (bits rows)).reverse,[]⟩ (Counter.marked xs) dpos (finishPos rows xs cpos) ip outRev)) := by
  obtain ⟨t,ht,htr⟩:=rewound_stream hq rows xs dpos cpos w ip outRev
  exact ⟨t,ht,NativeIOFusion.trace_stepN _ _ _ w htr⟩

end TransposeFollowup.RowLoop


/-! Apply the actual decoder/clock machine to the exact binary stream
emitted by OpcodeGenerator. The first generated row supplies the movement
vector; neither that vector nor the input dimension is a program parameter. -/
namespace TransposeFollowup.GeneratedRowClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

def rows (F : Fin c → RationalMobius) (n : ℕ) := List.ofFn (fun u : Fin (2*n) => rationalPageOpcode F u)
def bits (F : Fin c → RationalMobius) (n : ℕ) := (rationalOpcodeTape F n).flatMap PageLoop.opcodeBits
def tailBits (F : Fin c → RationalMobius) (n : ℕ) := ((rows F n).tail).flatMap OpcodeDecoder.word

theorem bits_eq_rows (F : Fin c → RationalMobius) (n : ℕ) : bits F n=(rows F n).flatMap OpcodeDecoder.word := by
  simp only [bits,rows,rationalOpcodeTape,rationalOpcodeTable,List.Vector.toList_ofFn,OpcodeDecoder.word,
    List.ofFn_eq_map,List.map_map,List.flatten_eq_flatMap,List.flatMap_assoc,List.flatMap_map,Function.comp_def,id_eq]

theorem first_row (F : Fin c → RationalMobius) (n : ℕ) (hn : 1 ≤ n) :
    bits F n=OpcodeDecoder.word (rationalPageOpcode F (⟨0,by omega⟩ : Fin (2*n)))++tailBits F n := by
  have hne : rows F n≠[] := by simp [rows];omega
  have hh : (rows F n).head hne=rationalPageOpcode F (⟨0,by omega⟩ : Fin (2*n)) := List.head_ofFn hne
  have hr:=List.cons_head_tail hne
  rw [hh] at hr
  rw [bits_eq_rows,← hr,List.flatMap_cons]
  rfl

theorem bits_length (F : Fin c → RationalMobius) (n : ℕ) : (bits F n).length=4*n*rationalPageCount F := by
  simp [bits,List.length_flatMap,OpcodeDecoder.opcodeBits_length,rationalOpcodeTape_length]
  ring

theorem native_first_row (F : Fin c → RationalMobius) (n : ℕ) (hn : 1 ≤ n) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    let ops:=rationalPageOpcode F (⟨0,by omega⟩ : Fin (2*n))
    ∃ t ≤ 8*n*rationalPageCount F+4*rationalPageCount F+2*xs.length+8,
      Transpose.stepN (RowClock.nativeMachine (rationalPageCount F)) w t
        (NativeIOFusion.denote (RowClock.nativeEncoding (rationalPageCount F)) (RowClock.program (rationalPageCount F)) (RowClock.selected (rationalPageCount F))
          (RowClock.cfg (.rewind .left) ⟨(symbols (bits F n)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev))=
        some (NativeIOFusion.denote (RowClock.nativeEncoding (rationalPageCount F)) (RowClock.program (rationalPageCount F)) (RowClock.selected (rationalPageCount F))
          (RowClock.cfg (.clock ops (.inr .done)) ⟨(symbols (OpcodeDecoder.word ops)).reverse,symbols (tailBits F n)⟩ (Counter.marked xs)
            (fun p => dpos p-(tailBits F n).length) (PageClock.advance ops cpos 0 (xs.count true)) ip outRev)) := by
  dsimp only
  have h:=RowClock.native_rewound_row (rationalPageOpcode F (⟨0,by omega⟩ : Fin (2*n))) (tailBits F n) xs dpos cpos w ip outRev
  rw [← first_row F n hn,bits_length] at h
  simpa only [show 2*(4*n*rationalPageCount F)+4*rationalPageCount F+2*xs.length+8=
    8*n*rationalPageCount F+4*rationalPageCount F+2*xs.length+8 by ring] using h

end TransposeFollowup.GeneratedRowClock


/-! The entire exact output format of OpcodeGenerator is consumed by one
fixed native machine. Its entry still explicitly contains the generated
stream and the prepared clock; their construction is not charged here. -/
namespace TransposeFollowup.GeneratedRowLoop
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {c : ℕ}

theorem page_count_positive (F : Fin c → RationalMobius) (hc : 1 ≤ c) : 1 ≤ rationalPageCount F := by
  exact Nat.mul_pos hc (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

theorem native_all_rows (F : Fin c → RationalMobius) (hc : 1 ≤ c) (n : ℕ) (xs : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 16*n*rationalPageCount F+4*n*xs.length+12*n+5,
      Transpose.stepN (RowLoop.nativeMachine (rationalPageCount F)) w t
        (NativeIOFusion.denote (RowLoop.nativeEncoding (rationalPageCount F)) (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F))
          (RowLoop.cfg (.rewind .left) ⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ (Counter.marked xs) dpos cpos ip outRev))=
        some (NativeIOFusion.denote (RowLoop.nativeEncoding (rationalPageCount F)) (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F))
          (RowLoop.cfg .done ⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ (Counter.marked xs) dpos
            (RowLoop.finishPos (GeneratedRowClock.rows F n) xs cpos) ip outRev)) := by
  have hb : RowLoop.bits (GeneratedRowClock.rows F n)=GeneratedRowClock.bits F n:=
    (GeneratedRowClock.bits_eq_rows F n).symm
  have hl : (GeneratedRowClock.rows F n).length=2*n:=by simp [GeneratedRowClock.rows]
  have h:=RowLoop.native_rewound_stream (page_count_positive F hc) (GeneratedRowClock.rows F n) xs dpos cpos w ip outRev
  rw [hb,hl,GeneratedRowClock.bits_length] at h
  have ht : 2*(4*n*rationalPageCount F)+2*n*RowLoop.period (rationalPageCount F) xs+5=
      16*n*rationalPageCount F+4*n*xs.length+12*n+5:=by unfold RowLoop.period;ring
  simpa only [ht] using h

theorem native_all_records (F : Fin c → RationalMobius) (hc : 1 ≤ c) (n R : ℕ)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (w : List Bool) (ip : ℤ) (outRev : List Bool) :
    ∃ t ≤ 16*n*rationalPageCount F+28*n*R+12*n+5,
      Transpose.stepN (RowLoop.nativeMachine (rationalPageCount F)) w t
        (NativeIOFusion.denote (RowLoop.nativeEncoding (rationalPageCount F)) (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F))
          (RowLoop.cfg (.rewind .left) ⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩
            (Counter.marked (SevenPhaseClock.word R)) dpos cpos ip outRev))=
        some (NativeIOFusion.denote (RowLoop.nativeEncoding (rationalPageCount F)) (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F))
          (RowLoop.cfg .done ⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ (Counter.marked (SevenPhaseClock.word R)) dpos
            (RowLoop.finishPos (GeneratedRowClock.rows F n) (SevenPhaseClock.word R) cpos) ip outRev)) := by
  have h:=native_all_rows F hc n (SevenPhaseClock.word R) dpos cpos w ip outRev
  rw [SevenPhaseClock.word_length] at h
  simpa only [show 4*n*(7*R)=28*n*R by ring] using h

end TransposeFollowup.GeneratedRowLoop


/-! A concrete fixed mixed program: paid opcode generation, one charged
transfer, and one fused clock call. The clock is prepared at entry and the
opcode vector is fixed in this program. Runtime opcode decoding and clock
preparation are deliberately not supplied by this composition theorem. -/
namespace TransposeFollowup.GeneratorClock
open FixedTapeCompiler
set_option autoImplicit false
variable {r q : ℕ} {F : Fin (r+1) → RationalMobius}

abbrev Port (q : ℕ) := OpcodeGenerator.Port ⊕ ReusablePageClock.Port q
abbrev Label (F : Fin (r+1) → RationalMobius) := OpcodeGenerator.Label F ⊕ ReusablePageClock.Label

def genBinding (q : ℕ) : FinitePortBinding OpcodeGenerator.Port (Port q) where
  ports:=Function.Embedding.inl
  decode | .inl p => some p | .inr _ => none
  decode_spec:=by intro p t;cases p <;> simp [eq_comm]
def clockBinding (q : ℕ) : FinitePortBinding (ReusablePageClock.Port q) (Port q) where
  ports:=Function.Embedding.inr
  decode | .inl _ => none | .inr p => some p
  decode_spec:=by intro p t;cases p <;> simp [eq_comm]

def program (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) : NativeIO.Program (Port q) (Label F)
  | .inl pc => if pc=.schedule .done then .work (.jump (.inr (.inl .read)))
      else NativeIOEmbedding.boundInstruction (genBinding q) Sum.inl (OpcodeGenerator.program F pc)
  | .inr pc => .work ((clockBinding q).instruction Sum.inr (ReusablePageClock.program ops pc))
def selected (F : Fin (r+1) → RationalMobius) : Label F → Bool
  | .inl _ => false
  | .inr pc => FusedPageClock.selected pc

def join (pc : Label F) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) : NativeIO.Config (Port q) (Label F) where
  work:=⟨⟨pc,Sum.elim g.work.core.tapes c.core.tapes⟩,Sum.elim g.work.pos c.pos⟩
  inputPos:=g.inputPos
  outRev:=g.outRev

def frame (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) : MicrocodeEmbedding.Frame (Port q) :=
  ⟨Sum.elim g.work.core.tapes c.core.tapes,Sum.elim g.work.pos c.pos⟩

theorem gen_code (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) (pc : OpcodeGenerator.Label F)
    (hh : OpcodeGenerator.program F pc≠.work .halt) (_ : OpcodeGenerator.program F pc≠.work .reject) :
    program F ops (.inl pc)=NativeIOEmbedding.instruction (genBinding q).ports Sum.inl (OpcodeGenerator.program F pc) := by
  by_cases he : pc=.schedule .done
  · subst pc;exact False.elim (hh rfl)
  · simp only [program,he,ite_false,NativeIOEmbedding.bound_instruction_eq]

theorem clock_code (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) (pc : ReusablePageClock.Label) :
    NativeIO.workProgram (program F ops) (.inr pc)=
      MicrocodeEmbedding.instruction (clockBinding q).ports Sum.inr (ReusablePageClock.program ops pc) := by
  simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

theorem embed_gen (g base : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) :
    NativeIOEmbedding.embed (genBinding q).ports Sum.inl g (frame base c)=join (.inl g.work.core.pc) g c := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed frame join
  simp only [← (genBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

theorem embed_clock (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c base : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) :
    (⟨MicrocodeEmbedding.embed (clockBinding q).ports Sum.inr c (frame g base),g.inputPos,g.outRev⟩ : NativeIO.Config (Port q) (Label F))=
      join (.inr c.core.pc) g c := by
  unfold MicrocodeEmbedding.embed frame join
  simp only [← (clockBinding q).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

abbrev Trace (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program F ops) (selected F) w) (NativeIOFusion.Active (program F ops) (selected F))

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) (w : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) :
    Trace F ops w 1 (join (.inl (.schedule .done)) g c) (join (.inr (.inl .read)) g c) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,join,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,join,program,ite_true,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

end TransposeFollowup.GeneratorClock


namespace TransposeFollowup.GeneratorClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r q : ℕ}

theorem prepared_trace (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode)
    (clock : List Bool) (cpos : ReusablePageClock.Port q → ℤ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+2*clock.length+4,Trace F ops w t
      (join (.inl (OpcodeGenerator.start F))
        (OpcodeGenerator.cfg (OpcodeGenerator.start F) (RawEnumeration.initial []) gpos 0 outRev)
        (ReusablePageClock.cfg (.inl .read) (Counter.marked clock) cpos))
      (join (.inr (.inr .done))
        (OpcodeGenerator.cfg (.schedule .done) (OpcodeGenerator.finalBank F w xs)
          (OpcodeGenerator.finalPositions F xs gpos) w.length outRev)
        (ReusablePageClock.cfg (.inr .done) (Counter.marked clock) (PageClock.advance ops cpos 0 (clock.count true)))) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=OpcodeGenerator.complete_trace F w n hn hw gpos outRev
  let first:=OpcodeGenerator.cfg (OpcodeGenerator.start F) (RawEnumeration.initial []) gpos 0 outRev
  let last : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F):=OpcodeGenerator.cfg (.schedule .done) (OpcodeGenerator.finalBank F w xs)
    (OpcodeGenerator.finalPositions F xs gpos) w.length outRev
  let initialClock:=ReusablePageClock.cfg (.inl .read) (Counter.marked clock) cpos
  have tg:=NativeIOFusionCalls.unselected_trace (genBinding q).ports Sum.inl (OpcodeGenerator.program F)
    (program F ops) (selected F) (frame first initialClock) w (fun _ => rfl) (gen_code F ops) htr
  simp only [embed_gen] at tg
  have tj:=transfer_trace F ops w last initialClock
  have tc:=FusedPageClockIO.trace_call ops (clockBinding q).ports Sum.inr (program F ops) (selected F)
    (frame last initialClock) (fun _ => rfl) (fun pc _ => clock_code F ops pc) clock cpos w (w.length:ℤ) outRev
  have tc' : Trace F ops w (2*clock.length+3) (join (.inr (.inl .read)) last initialClock)
      (join (.inr (.inr .done)) last
        (ReusablePageClock.cfg (.inr .done) (Counter.marked clock) (PageClock.advance ops cpos 0 (clock.count true)))) := by
    simpa only [show (w.length:ℤ)=last.inputPos from rfl,show outRev=last.outRev from rfl,embed_clock,initialClock,ReusablePageClock.cfg]
      using tc
  refine ⟨xs,hx,hv,hl,t+1+(2*clock.length+3),by omega,?_⟩
  exact NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans tg tj) tc'

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) (q : ℕ) :=
  NativeMicrocode.initialEncoding (T:=Port q) (.inl (OpcodeGenerator.start F) : Label F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) :=
  NativeIOFusion.machine (nativeEncoding F q) (program F ops) (selected F)

theorem native_prepared (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode)
    (clock : List Bool) (cpos : ReusablePageClock.Port q → ℤ)
    (w : List Bool) (n : ℕ) (hn : 1 ≤ n) (hw : w.length=Transpose.inputLength n)
    (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+2*clock.length+4,
      Transpose.stepN (nativeMachine F ops) w t
        (NativeIOFusion.denote (nativeEncoding F q) (program F ops) (selected F)
          (join (.inl (OpcodeGenerator.start F))
            (OpcodeGenerator.cfg (OpcodeGenerator.start F) (RawEnumeration.initial []) gpos 0 outRev)
            (ReusablePageClock.cfg (.inl .read) (Counter.marked clock) cpos)))=
        some (NativeIOFusion.denote (nativeEncoding F q) (program F ops) (selected F)
          (join (.inr (.inr .done))
            (OpcodeGenerator.cfg (.schedule .done) (OpcodeGenerator.finalBank F w xs)
              (OpcodeGenerator.finalPositions F xs gpos) w.length outRev)
            (ReusablePageClock.cfg (.inr .done) (Counter.marked clock) (PageClock.advance ops cpos 0 (clock.count true))))) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=prepared_trace F ops clock cpos w n hn hw gpos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOFusion.trace_stepN _ _ _ w htr⟩

theorem final_halts (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) (w : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (c : NativeMicrocode.Config (ReusablePageClock.Port q) ReusablePageClock.Label) :
    Transpose.step (nativeMachine F ops) w
      (NativeIOFusion.denote (nativeEncoding F q) (program F ops) (selected F) (join (.inr (.inr .done)) g c))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,join,program,FinitePortBinding.instruction,ReusablePageClock.program,NativeSealBack.program]


theorem fixed_resources (F : Fin (r+1) → RationalMobius) (ops : Fin q → PageOpcode) :
    (nativeMachine F ops).k=43+q ∧ (nativeMachine F ops).g+1=5 ∧
    (nativeMachine F ops).q+1=Fintype.card (OpcodeGenerator.Label F)+11 ∧
    (nativeEncoding F q).label (.inl (OpcodeGenerator.start F))=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card (Port q)=43+q
    have h : Fintype.card OpcodeGenerator.Port=42:=by decide +kernel
    simp [Port,ReusablePageClock.Port,PageClock.Port,h];omega
  · change Fintype.card (Label F)-1+1=Fintype.card (OpcodeGenerator.Label F)+11
    have h : Fintype.card ReusablePageClock.Label=11:=by decide +kernel
    simp only [Label,Fintype.card_sum,h]
    omega

end TransposeFollowup.GeneratorClock


/-! Actual generator/consumer wiring. The consumer's data port is the
already-existing generator output port, not a copied or supplied stream. -/
namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r q : ℕ} {F : Fin (r+1) → RationalMobius}
abbrev Port (q : ℕ) := GeneratorClock.Port q
abbrev Label (F : Fin (r+1) → RationalMobius) := OpcodeGenerator.Label F ⊕ RowLoop.Label (rationalPageCount F)

def rowPorts (q : ℕ) : RowLoop.Port q ↪ Port q where
  toFun | .inl _ => .inl VertexScheduler.outputPort | .inr p => .inr p
  inj':=by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
      | inr b => cases h
    | inr a => cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj h)
def rowBinding (q : ℕ) : FinitePortBinding (RowLoop.Port q) (Port q) where
  ports:=rowPorts q
  decode | .inl p => if p=VertexScheduler.outputPort then some (.inl 0) else none | .inr p => some (.inr p)
  decode_spec:=by
    intro u t
    cases u with
    | inl p =>
      cases t with
      | inl t =>
        have ht : t=0:=Subsingleton.elim _ _
        subst t
        change (if p=VertexScheduler.outputPort then some (.inl (0 : Fin 1) : RowLoop.Port q) else none)=some (.inl 0) ↔
          (Sum.inl VertexScheduler.outputPort : Port q)=Sum.inl p
        by_cases hp : p=VertexScheduler.outputPort <;> simp [hp,eq_comm]
      | inr t =>
        change (if p=VertexScheduler.outputPort then some (.inl (0 : Fin 1) : RowLoop.Port q) else none)=some (.inr t) ↔
          (Sum.inr t : Port q)=Sum.inl p
        by_cases hp : p=VertexScheduler.outputPort <;> simp [hp]
    | inr p =>
      cases t with
      | inl t =>
        change some (.inr p : RowLoop.Port q)=some (.inl t) ↔ (Sum.inl VertexScheduler.outputPort : Port q)=Sum.inr p
        simp
      | inr t =>
        change some (.inr p : RowLoop.Port q)=some (.inr t) ↔ (Sum.inr t : Port q)=Sum.inr p
        simp [eq_comm]

def program (F : Fin (r+1) → RationalMobius) : NativeIO.Program (Port (rationalPageCount F)) (Label F)
  | .inl pc => if pc=.schedule .done then .work (.jump (.inr (.rewind .left)))
      else NativeIOEmbedding.boundInstruction (GeneratorClock.genBinding (rationalPageCount F)) Sum.inl (OpcodeGenerator.program F pc)
  | .inr pc => .work ((rowBinding (rationalPageCount F)).instruction Sum.inr (NativeIO.workProgram (RowLoop.program (rationalPageCount F)) pc))
def selected (F : Fin (r+1) → RationalMobius) : Label F → Bool
  | .inl _ => false
  | .inr pc => RowLoop.selected (rationalPageCount F) pc

def join (pc : Label F) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) : NativeIO.Config (Port (rationalPageCount F)) (Label F) where
  work:=⟨⟨pc,Sum.elim g.work.core.tapes (PageClock.bank clock)⟩,Sum.elim g.work.pos cpos⟩
  inputPos:=g.inputPos
  outRev:=g.outRev

def frame (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) : MicrocodeEmbedding.Frame (Port (rationalPageCount F)) :=
  GeneratorClock.frame g (ReusablePageClock.cfg (.inl .read) clock cpos)

def rowJoin (pc : RowLoop.Label (rationalPageCount F)) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (data clock : Tape Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    NativeIO.Config (Port (rationalPageCount F)) (Label F) where
  work:=⟨⟨.inr pc,Sum.elim (Function.update g.work.core.tapes VertexScheduler.outputPort data.denote) (PageClock.bank clock)⟩,
    Sum.elim (Function.update g.work.pos VertexScheduler.outputPort (dpos 0)) cpos⟩
  inputPos:=g.inputPos
  outRev:=g.outRev

abbrev Trace (F : Fin (r+1) → RationalMobius) (w : List Bool) :=
  OperationalTrace.Trace (NativeIOFusion.step (program F) (selected F) w) (NativeIOFusion.Active (program F) (selected F))

theorem gen_code (F : Fin (r+1) → RationalMobius) (pc : OpcodeGenerator.Label F)
    (hh : OpcodeGenerator.program F pc≠.work .halt) (_ : OpcodeGenerator.program F pc≠.work .reject) :
    program F (.inl pc)=NativeIOEmbedding.instruction (GeneratorClock.genBinding (rationalPageCount F)).ports Sum.inl (OpcodeGenerator.program F pc) := by
  by_cases he : pc=.schedule .done
  · subst pc;exact False.elim (hh rfl)
  · simp only [program,he,ite_false,NativeIOEmbedding.bound_instruction_eq]

theorem row_code (F : Fin (r+1) → RationalMobius) (pc : RowLoop.Label (rationalPageCount F)) :
    NativeIO.workProgram (program F) (.inr pc)=
      MicrocodeEmbedding.instruction (rowBinding (rationalPageCount F)).ports Sum.inr (NativeIO.workProgram (RowLoop.program (rationalPageCount F)) pc) := by
  simp only [NativeIO.workProgram,program,FinitePortBinding.instruction_eq]

theorem embed_gen (g base : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    NativeIOEmbedding.embed (GeneratorClock.genBinding (rationalPageCount F)).ports Sum.inl g (frame base clock cpos)=
      join (.inl g.work.core.pc) g clock cpos := by
  unfold NativeIOEmbedding.embed MicrocodeEmbedding.embed frame GeneratorClock.frame join ReusablePageClock.cfg
  simp only [← (GeneratorClock.genBinding (rationalPageCount F)).values_eq_extend]
  congr 2
  · congr 1;funext p;cases p <;> rfl
  · funext p;cases p <;> rfl

theorem embed_row (pc : RowLoop.Label (rationalPageCount F)) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (data clock base : Tape Bool) (dpos : Fin 1 → ℤ) (cpos basePos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    (⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Sum.inr
      (RowLoop.cfg pc data clock dpos cpos g.inputPos g.outRev).work (frame g base basePos),g.inputPos,g.outRev⟩ :
        NativeIO.Config (Port (rationalPageCount F)) (Label F))=rowJoin pc g data clock dpos cpos := by
  unfold MicrocodeEmbedding.embed RowLoop.cfg frame GeneratorClock.frame ReusablePageClock.cfg rowJoin
  simp only [← (rowBinding (rationalPageCount F)).values_eq_extend]
  congr 2
  · congr 1
    funext p
    cases p with
    | inl p => by_cases h : p=VertexScheduler.outputPort <;> simp [rowBinding,FinitePortBinding.values,h]
    | inr p => rfl
  · funext p
    cases p with
    | inl p => by_cases h : p=VertexScheduler.outputPort <;> simp [rowBinding,FinitePortBinding.values,h]
    | inr p => rfl

theorem rowJoin_eq (pc : RowLoop.Label (rationalPageCount F)) (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (data clock : Tape Bool) (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ)
    (ht : g.work.core.tapes VertexScheduler.outputPort=data.denote) (hp : g.work.pos VertexScheduler.outputPort=dpos 0) :
    rowJoin pc g data clock dpos cpos=join (.inr pc) g clock cpos := by
  unfold rowJoin join
  rw [← ht,← hp,Function.update_eq_self,Function.update_eq_self]

theorem transfer_trace (F : Fin (r+1) → RationalMobius) (w : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (clock : Tape Bool) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    Trace F w 1 (join (.inl (.schedule .done)) g clock cpos) (join (.inr (.rewind .left)) g clock cpos) := by
  apply OperationalTrace.Trace.cons
  · apply (NativeIOFusion.active_iff _ _ _).mpr
    simp [NativeIO.Active,join,program]
  · rw [NativeIOFusion.step_unselected _ _ _ _ rfl]
    simp only [NativeIO.step,join,program,ite_true,NativeMicrocode.step,NativeIO.workProgram,Microcode.actualStep]
    exact .refl _

end TransposeFollowup.GeneratorRows


namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler
set_option autoImplicit false
variable {r : ℕ}

theorem row_trace (F : Fin (r+1) → RationalMobius) (outerFrame : MicrocodeEmbedding.Frame (Port (rationalPageCount F)))
    (w : List Bool) (ip : ℤ) (outRev : List Bool) {n : ℕ}
    {c d : NativeIO.Config (RowLoop.Port (rationalPageCount F)) (RowLoop.Label (rationalPageCount F))}
    (h : RowLoop.Trace (rationalPageCount F) w n c d) :
    Trace F w n
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Sum.inr c.work outerFrame,ip,outRev⟩
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Sum.inr d.work outerFrame,ip,outRev⟩ :=
  NativeIOFusionCalls.work_trace (rowBinding (rationalPageCount F)).ports Sum.inr
    (NativeIO.workProgram (RowLoop.program (rationalPageCount F))) (program F)
    (RowLoop.selected (rationalPageCount F)) (selected F) outerFrame w ip outRev (fun _ => rfl)
    (fun pc _ _ => row_code F pc) (fun _ _ _ _ _ _ => row_code F _)
    (NativeIOFusion.only_work_trace _ (RowLoop.only_work _) _ w h)

theorem row_prefix (F : Fin (r+1) → RationalMobius) (outerFrame : MicrocodeEmbedding.Frame (Port (rationalPageCount F)))
    (w : List Bool) (ip : ℤ) (outRev : List Bool) {n : ℕ}
    {c d : NativeIO.Config (RowLoop.Port (rationalPageCount F)) (RowLoop.Label (rationalPageCount F))}
    (h : RowLoop.Trace (rationalPageCount F) w n c d) (s : ℕ) (hs : s ≤ n) :
    NativeIOFusion.run (program F) (selected F) w s
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Sum.inr c.work outerFrame,ip,outRev⟩=
      ⟨MicrocodeEmbedding.embed (rowBinding (rationalPageCount F)).ports Sum.inr
        (NativeIOFusion.run (RowLoop.program (rationalPageCount F)) (RowLoop.selected (rationalPageCount F)) w s c).work outerFrame,ip,outRev⟩ := by
  have ht:=NativeIOFusion.only_work_trace _ (RowLoop.only_work _) _ w h
  have he:=NativeIOFusionCalls.work_prefix (rowBinding (rationalPageCount F)).ports Sum.inr
    (NativeIO.workProgram (RowLoop.program (rationalPageCount F))) (program F)
    (RowLoop.selected (rationalPageCount F)) (selected F) outerFrame w ip outRev (fun _ => rfl)
    (fun pc _ _ => row_code F pc) (fun _ _ _ _ _ _ => row_code F _) ht s hs
  simpa only [NativeIOFusion.only_work_run _ (RowLoop.only_work _)] using he

end TransposeFollowup.GeneratorRows


namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

def first (F : Fin (r+1) → RationalMobius) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :=
  OpcodeGenerator.cfg (OpcodeGenerator.start F) (RawEnumeration.initial []) gpos 0 outRev
def last (F : Fin (r+1) → RationalMobius) (w xs : List Bool) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :=
  OpcodeGenerator.cfg (F:=F) (.schedule .done) (OpcodeGenerator.finalBank F w xs) (OpcodeGenerator.finalPositions F xs gpos) w.length outRev

theorem generated_trace (F : Fin (r+1) → RationalMobius) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length,Trace F w t
      (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos)
      (join (.inl (.schedule .done)) (last F w xs gpos outRev) (Counter.marked clock) cpos) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=OpcodeGenerator.complete_trace F w n hn hw gpos outRev
  have tg:=NativeIOFusionCalls.unselected_trace (GeneratorClock.genBinding (rationalPageCount F)).ports Sum.inl
    (OpcodeGenerator.program F) (program F) (selected F) (frame (first F gpos outRev) (Counter.marked clock) cpos) w
    (fun _ => rfl) (gen_code F) htr
  refine ⟨xs,hx,hv,hl,t,ht,?_⟩
  simpa only [embed_gen,first,last,OpcodeGenerator.cfg,OpcodeGenerator.workCfg] using tg

theorem last_output (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    (last F w xs gpos outRev).work.core.tapes VertexScheduler.outputPort=
      (⟨(symbols (GeneratedRowClock.bits F (Counter.value xs))).reverse,[]⟩ : Tape Bool).denote := by
  change (OpcodeGenerator.finalBank F w xs VertexScheduler.outputPort).denote=_
  rw [OpcodeGenerator.output_tape]
  rfl

theorem output_start_pos (F : Fin (r+1) → RationalMobius) (w xs : List Bool)
    (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    (last F w xs gpos outRev).work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F (Counter.value xs)).length=
      gpos VertexScheduler.outputPort := by
  change OpcodeGenerator.finalPositions F xs gpos VertexScheduler.outputPort-_= _
  rw [OpcodeGenerator.output_head,GeneratedRowClock.bits_length]
  omega

end TransposeFollowup.GeneratorRows


namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem consume_trace (F : Fin (r+1) → RationalMobius)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (n : ℕ) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool)
    (hg : g.work.core.tapes VertexScheduler.outputPort=(⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote) :
    ∃ t ≤ 16*n*rationalPageCount F+4*n*clock.length+12*n+5,Trace F w t
      (join (.inr (.rewind .left)) g (Counter.marked clock) cpos)
      (join (.inr .done) g (Counter.marked clock) (RowLoop.finishPos (GeneratedRowClock.rows F n) clock cpos)) := by
  obtain ⟨t,ht,htr⟩:=RowLoop.rewound_stream (GeneratedRowLoop.page_count_positive F (by omega))
    (GeneratedRowClock.rows F n) clock (fun _ => g.work.pos VertexScheduler.outputPort) cpos w g.inputPos g.outRev
  have h:=row_trace F (frame g (Counter.marked clock) cpos) w g.inputPos g.outRev htr
  simp only [embed_row] at h
  have hb : RowLoop.bits (GeneratedRowClock.rows F n)=GeneratedRowClock.bits F n:=
    (GeneratedRowClock.bits_eq_rows F n).symm
  have hl : (GeneratedRowClock.rows F n).length=2*n:=by simp [GeneratedRowClock.rows]
  have hc : 2*(RowLoop.bits (GeneratedRowClock.rows F n)).length+(GeneratedRowClock.rows F n).length*RowLoop.period (rationalPageCount F) clock+5=
      16*n*rationalPageCount F+4*n*clock.length+12*n+5 := by
    rw [hb,hl,GeneratedRowClock.bits_length]
    unfold RowLoop.period
    ring
  rw [hc] at ht
  rw [hb] at h
  rw [rowJoin_eq _ g _ _ _ _ hg rfl,rowJoin_eq _ g _ _ _ _ hg rfl] at h
  exact ⟨t,ht,h⟩

theorem prepared_trace (F : Fin (r+1) → RationalMobius) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+16*n*rationalPageCount F+4*n*clock.length+12*n+6,Trace F w t
      (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos)
      (join (.inr .done) (last F w xs gpos outRev) (Counter.marked clock)
        (RowLoop.finishPos (GeneratedRowClock.rows F n) clock cpos)) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=generated_trace F clock cpos w n hn hw gpos outRev
  have tj:=transfer_trace F w (last F w xs gpos outRev) (Counter.marked clock) cpos
  have hg : (last F w xs gpos outRev).work.core.tapes VertexScheduler.outputPort=
      (⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote := by
    simpa only [hv] using last_output F w xs gpos outRev
  obtain ⟨b,hb,tb⟩:=consume_trace F (last F w xs gpos outRev) n clock cpos w hg
  exact ⟨xs,hx,hv,hl,a+1+b,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb⟩

noncomputable def nativeEncoding (F : Fin (r+1) → RationalMobius) :=
  NativeMicrocode.initialEncoding (T:=Port (rationalPageCount F)) (.inl (OpcodeGenerator.start F) : Label F)
noncomputable def nativeMachine (F : Fin (r+1) → RationalMobius) :=
  NativeIOFusion.machine (nativeEncoding F) (program F) (selected F)

theorem native_prepared (F : Fin (r+1) → RationalMobius) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+16*n*rationalPageCount F+4*n*clock.length+12*n+6,
      Transpose.stepN (nativeMachine F) w t
        (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
          (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos))=
        some (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
          (join (.inr .done) (last F w xs gpos outRev) (Counter.marked clock)
            (RowLoop.finishPos (GeneratedRowClock.rows F n) clock cpos))) := by
  obtain ⟨xs,hx,hv,hl,t,ht,htr⟩:=prepared_trace F clock cpos w n hn hw gpos outRev
  exact ⟨xs,hx,hv,hl,t,ht,NativeIOFusion.trace_stepN _ _ _ w htr⟩

theorem final_halts (F : Fin (r+1) → RationalMobius) (w : List Bool)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (clock : Tape Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) :
    Transpose.step (nativeMachine F) w
      (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F) (join (.inr .done) g clock cpos))=none := by
  apply (NativeIOFusion.step_none_iff _ _ _ w _).mpr
  rw [NativeIOFusion.active_iff]
  simp [NativeIO.Active,join,program,NativeIO.workProgram,RowLoop.program,FinitePortBinding.instruction]

theorem fixed_resources (F : Fin (r+1) → RationalMobius) :
    (nativeMachine F).k=43+rationalPageCount F ∧ (nativeMachine F).g+1=5 ∧
    (nativeMachine F).q+1=Fintype.card (OpcodeGenerator.Label F)+Fintype.card (RowLoop.Label (rationalPageCount F)) ∧
    (nativeEncoding F).label (.inl (OpcodeGenerator.start F))=0 := by
  refine ⟨?_,rfl,?_,NativeMicrocode.initialEncoding_start _⟩
  · change Fintype.card (Port (rationalPageCount F))=43+rationalPageCount F
    have h : Fintype.card OpcodeGenerator.Port=42:=by decide +kernel
    simp [Port,GeneratorClock.Port,ReusablePageClock.Port,PageClock.Port,h];omega
  · change Fintype.card (Label F)-1+1=_
    simp only [Label,Fintype.card_sum]
    have h : 0<Fintype.card (RowLoop.Label (rationalPageCount F)):=
      Fintype.card_pos_iff.mpr ⟨.guard⟩
    omega

end TransposeFollowup.GeneratorRows


namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem rewind_to_guard (F : Fin (r+1) → RationalMobius)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F)) (n : ℕ) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool)
    (hg : g.work.core.tapes VertexScheduler.outputPort=(⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote) :
    ∃ t ≤ 8*n*rationalPageCount F+4,Trace F w t
      (join (.inr (.rewind .left)) g (Counter.marked clock) cpos)
      (rowJoin .guard g ⟨[],symbols (GeneratedRowClock.bits F n)⟩ (Counter.marked clock)
        (fun _ => g.work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length) cpos) := by
  obtain ⟨t,ht,ha⟩:=RowLoop.rewind_trace (GeneratedRowClock.bits F n) (Counter.marked clock)
    (fun _ => g.work.pos VertexScheduler.outputPort) cpos w g.inputPos g.outRev
  have hb:=RowLoop.rewind_transfer ⟨[],symbols (GeneratedRowClock.bits F n)⟩ (Counter.marked clock)
    (fun _ => g.work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length) cpos w g.inputPos g.outRev
  have h:=row_trace F (frame g (Counter.marked clock) cpos) w g.inputPos g.outRev (NativeCountedLoop.trace_trans ha hb)
  simp only [embed_row] at h
  rw [rowJoin_eq _ g _ _ _ _ hg rfl] at h
  rw [GeneratedRowClock.bits_length] at ht
  exact ⟨t+1,by nlinarith,h⟩

theorem entry_trace (F : Fin (r+1) → RationalMobius) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+8*n*rationalPageCount F+5,Trace F w t
      (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos)
      (rowJoin .guard (last F w xs gpos outRev) ⟨[],symbols (GeneratedRowClock.bits F n)⟩ (Counter.marked clock)
        (fun _ => gpos VertexScheduler.outputPort) cpos) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=generated_trace F clock cpos w n hn hw gpos outRev
  have tj:=transfer_trace F w (last F w xs gpos outRev) (Counter.marked clock) cpos
  have hg : (last F w xs gpos outRev).work.core.tapes VertexScheduler.outputPort=
      (⟨(symbols (GeneratedRowClock.bits F n)).reverse,[]⟩ : Tape Bool).denote := by
    simpa only [hv] using last_output F w xs gpos outRev
  obtain ⟨b,hb,tb⟩:=rewind_to_guard F (last F w xs gpos outRev) n clock cpos w hg
  have hp : (fun _ : Fin 1 => (last F w xs gpos outRev).work.pos VertexScheduler.outputPort-(GeneratedRowClock.bits F n).length)=
      (fun _ => gpos VertexScheduler.outputPort) := by
    funext p
    simpa only [hv] using output_start_pos F w xs gpos outRev
  rw [hp] at tb
  exact ⟨xs,hx,hv,hl,a+1+b,by omega,NativeCountedLoop.trace_trans (NativeCountedLoop.trace_trans ta tj) tb⟩

end TransposeFollowup.GeneratorRows


namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem stream_prefix (F : Fin (r+1) → RationalMobius)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (front tail : List (OpcodeDecoder.Ops (rationalPageCount F))) (pre : List (Sym Bool)) (clock : List Bool)
    (dpos : Fin 1 → ℤ) (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) :
    Trace F w (front.length*RowLoop.period (rationalPageCount F) clock)
      (rowJoin .guard g ⟨pre,symbols (RowLoop.bits (front++tail))⟩ (Counter.marked clock) dpos cpos)
      (rowJoin .guard g ⟨(symbols (RowLoop.bits front)).reverse++pre,symbols (RowLoop.bits tail)⟩ (Counter.marked clock)
        (NativeZipper.shiftPositions dpos (2*(rationalPageCount F:ℤ)*front.length)) (RowLoop.finishPos front clock cpos)) := by
  have h:=row_trace F (frame g (Counter.marked clock) cpos) w g.inputPos g.outRev
    (RowLoop.stream_prefix (GeneratedRowLoop.page_count_positive F (by omega)) front tail pre clock dpos cpos w g.inputPos g.outRev)
  simpa only [embed_row] using h

theorem native_stream_trajectory (F : Fin (r+1) → RationalMobius)
    (g : NativeIO.Config OpcodeGenerator.Port (OpcodeGenerator.Label F))
    (front tail : List (OpcodeDecoder.Ops (rationalPageCount F))) (ops : OpcodeDecoder.Ops (rationalPageCount F))
    (pre : List (Sym Bool)) (clock : List Bool) (dpos : Fin 1 → ℤ)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool)
    (s : ℕ) (hs : s ≤ RowLoop.period (rationalPageCount F) clock) (p : Fin (rationalPageCount F)) :
    (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F) w)
      (front.length*RowLoop.period (rationalPageCount F) clock+s)
      (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
        (rowJoin .guard g ⟨pre,symbols (RowLoop.bits (front++ops::tail))⟩ (Counter.marked clock) dpos cpos))).workPos
          ((nativeEncoding F).port (.inr (some p)))=
      RowLoop.finishPos front clock cpos (some p)+(ops p).direction*((clock.take (s-(4*rationalPageCount F+2))).count true) := by
  have hq:=GeneratedRowLoop.page_count_positive F (by omega)
  have ht:=RowLoop.complete_trace hq (front++ops::tail) pre clock dpos cpos w g.inputPos g.outRev
  have hb : front.length*RowLoop.period (rationalPageCount F) clock+s ≤
      (front++ops::tail).length*RowLoop.period (rationalPageCount F) clock+1 := by
    simp only [List.length_append,List.length_cons]
    nlinarith [Nat.zero_le (tail.length*RowLoop.period (rationalPageCount F) clock)]
  have he:=row_prefix F (frame g (Counter.marked clock) cpos) w g.inputPos g.outRev ht
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

end TransposeFollowup.GeneratorRows


/-! A single raw-input execution produces the stream and supplies every
row boundary and every intermediate page position. The clock is the sole
prepared auxiliary input of this composition theorem. -/
namespace TransposeFollowup.GeneratorRows
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {r : ℕ}

theorem prepared_geometry (F : Fin (r+1) → RationalMobius) (clock : List Bool)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ a ≤ OpcodeGenerator.coefficient F*w.length+8*n*rationalPageCount F+5,
      (∀ front tail,GeneratedRowClock.rows F n=front++tail →
        Transpose.stepN (nativeMachine F) w (a+front.length*RowLoop.period (rationalPageCount F) clock)
          (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
            (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos))=
          some (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
            (rowJoin .guard (last F w xs gpos outRev) ⟨(symbols (RowLoop.bits front)).reverse,symbols (RowLoop.bits tail)⟩
              (Counter.marked clock) (NativeZipper.shiftPositions (fun _ => gpos VertexScheduler.outputPort)
                (2*(rationalPageCount F:ℤ)*front.length)) (RowLoop.finishPos front clock cpos)))) ∧
      (∀ front tail ops,GeneratedRowClock.rows F n=front++ops::tail →
        ∀ s,s ≤ RowLoop.period (rationalPageCount F) clock → ∀ p : Fin (rationalPageCount F),
          (OperationalTrace.run (Transpose.Tape.Impl.next (nativeMachine F) w)
            (a+(front.length*RowLoop.period (rationalPageCount F) clock+s))
            (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
              (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked clock) cpos))).workPos
                ((nativeEncoding F).port (.inr (some p)))=
            RowLoop.finishPos front clock cpos (some p)+(ops p).direction*((clock.take (s-(4*rationalPageCount F+2))).count true)) := by
  obtain ⟨xs,hx,hv,hl,a,ha,ta⟩:=entry_trace F clock cpos w n hn hw gpos outRev
  refine ⟨xs,hx,hv,hl,a,ha,?_,?_⟩
  · intro front tail he
    have hb : GeneratedRowClock.bits F n=RowLoop.bits (front++tail) := by
      rw [GeneratedRowClock.bits_eq_rows,he]
      rfl
    have tp:=stream_prefix F (last F w xs gpos outRev) front tail [] clock
      (fun _ => gpos VertexScheduler.outputPort) cpos w
    have ta':=ta
    rw [hb] at ta'
    simpa only [nativeMachine,List.append_nil] using NativeIOFusion.trace_stepN (nativeEncoding F) (program F) (selected F) w
      (NativeCountedLoop.trace_trans ta' tp)
  · intro front tail ops he s hs p
    have hb : GeneratedRowClock.bits F n=RowLoop.bits (front++ops::tail) := by
      rw [GeneratedRowClock.bits_eq_rows,he]
      rfl
    have hr:=OperationalTrace.trace_run ta
    unfold nativeMachine
    rw [OperationalTrace.run_add,NativeIOFusion.run_denote (nativeEncoding F) (program F) (selected F) w a]
    simp only [NativeIOFusion.run]
    rw [hr,hb]
    simpa only [nativeMachine] using native_stream_trajectory F (last F w xs gpos outRev) front tail ops [] clock
      (fun _ => gpos VertexScheduler.outputPort) cpos w s hs p

theorem native_prepared_records (F : Fin (r+1) → RationalMobius) (R : ℕ)
    (cpos : ReusablePageClock.Port (rationalPageCount F) → ℤ) (w : List Bool) (n : ℕ) (hn : 1 ≤ n)
    (hw : w.length=Transpose.inputLength n) (gpos : OpcodeGenerator.Port → ℤ) (outRev : List Bool) :
    ∃ xs,NativeTrim.Normalized xs ∧ Counter.value xs=n ∧ xs.length=n.size ∧
    ∃ t ≤ OpcodeGenerator.coefficient F*w.length+16*n*rationalPageCount F+28*n*R+12*n+6,
      Transpose.stepN (nativeMachine F) w t
        (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
          (join (.inl (OpcodeGenerator.start F)) (first F gpos outRev) (Counter.marked (SevenPhaseClock.word R)) cpos))=
        some (NativeIOFusion.denote (nativeEncoding F) (program F) (selected F)
          (join (.inr .done) (last F w xs gpos outRev) (Counter.marked (SevenPhaseClock.word R))
            (RowLoop.finishPos (GeneratedRowClock.rows F n) (SevenPhaseClock.word R) cpos))) := by
  have h:=native_prepared F (SevenPhaseClock.word R) cpos w n hn hw gpos outRev
  rw [SevenPhaseClock.word_length] at h
  simpa only [show 4*n*(7*R)=28*n*R by ring] using h

end TransposeFollowup.GeneratorRows
