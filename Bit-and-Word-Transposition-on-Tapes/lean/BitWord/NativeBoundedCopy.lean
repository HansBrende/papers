import TransposeFollowup.NativeSealBack

/-! Copy exactly one unary-clocked block to an isolated raw oracle input.
The source advances; the new input and clock return to their starting heads.
No input length is stored in finite control. -/
namespace BitWord.NativeBoundedCopy
open FixedTapeCompiler CopyMachine TransposeFollowup
set_option autoImplicit false

inductive Label
  | scan | read | emit (b : Bool) | seal | back | backRead | backMove | finish | done | reject
  deriving DecidableEq, Fintype

def program : Microcode.Program (Fin 3) Label
  | .scan => .read 2 (fun s => match s with | .data _ => .read | .stop => .seal | _ => .reject)
  | .read => .read 0 (fun s => match s with | .data b => .emit b | _ => .reject)
  | .emit b => .act (fun p => ⟨if p=1 then some (.data b) else none,.right⟩) .scan
  | .seal => .act (fun p => ⟨if p=1 then some .stop else none,.stay⟩) .back
  | .back => .act (fun p => ⟨none,if p=2 then .left else .stay⟩) .backRead
  | .backRead => .read 2 (fun s => match s with | .data _ => .backMove | .start => .finish | _ => .reject)
  | .backMove => .act (fun p => ⟨none,if p=1 then .left else .stay⟩) .back
  | .finish => .act (fun p => ⟨none,if p=2 then .right else .stay⟩) .done
  | .done => .halt | .reject => .reject

def bank (src dst clock : Tape Bool) : Fin 3 → Tape Bool := ![src,dst,clock]
def cfg (pc : Label) (src dst clock : Tape Bool) (pos : Fin 3 → ℤ) : NativeZipper.Config (Fin 3) Label :=
  ⟨⟨pc,bank src dst clock⟩,pos⟩
def shift (pos : Fin 3 → ℤ) (a b c : ℤ) : Fin 3 → ℤ :=
  fun p => pos p + if p=0 then a else if p=1 then b else c
@[simp] theorem shift_zero (pos : Fin 3 → ℤ) : shift pos 0 0 0=pos := by funext p; simp [shift]
theorem shift_add (pos : Fin 3 → ℤ) (a b c d e f : ℤ) :
    shift (shift pos a b c) d e f=shift pos (a+d) (b+e) (c+f) := by
  funext p; simp [shift]; split_ifs <;> ring

theorem scan_bit (b f : Bool) (sl sr dl dr cl cr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 3 (cfg .scan ⟨sl,.data b::sr⟩ ⟨dl,dr⟩ ⟨cl,.data f::cr⟩ pos)=
      cfg .scan ⟨.data b::sl,sr⟩ ⟨.data b::dl,dr.tail⟩ ⟨.data f::cl,cr⟩ (shift pos 1 1 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,
    Tape.read,Microcode.Action.apply,Tape.write,Tape.moveRight,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp [shift,sub_eq_add_neg]

theorem scan_run (xs fs : List Bool) (hlen : fs.length=xs.length)
    (sl sr dl cl cr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (3*xs.length+2)
      (cfg .scan ⟨sl,symbols xs++sr⟩ ⟨dl,[]⟩ ⟨cl,symbols fs++.stop::cr⟩ pos)=
      cfg .back ⟨(symbols xs).reverse++sl,sr⟩ ⟨(symbols xs).reverse++dl,[.stop]⟩
        ⟨(symbols fs).reverse++cl,.stop::cr⟩ (shift pos xs.length xs.length xs.length) := by
  induction xs generalizing fs sl dl cl pos with
  | nil =>
    have hf : fs=[] := List.eq_nil_of_length_eq_zero hlen
    subst fs
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,Tape.read,symbols,Microcode.Action.apply,Tape.write,NativeMicrocode.direction,Transpose.Dir.shift]
    funext p; fin_cases p <;> simp
  | cons b xs ih =>
    cases fs with
    | nil => simp at hlen
    | cons f fs =>
      have hf : fs.length=xs.length := by simpa using hlen
      rw [show 3*(b::xs).length+2=3+(3*xs.length+2) by simp;omega,NativeZipper.run_add]
      simp only [symbols,List.map_cons,List.cons_append]
      rw [scan_bit]
      simp only [List.tail_nil]
      simp only [symbols] at ih
      rw [ih fs hf,shift_add]
      simp [symbols,List.reverse_cons,List.append_assoc]
      congr 1 <;> congr 1 <;> omega

theorem back_bit (b f : Bool) (src : Tape Bool) (dl dr cl cr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program 3 (cfg .back src ⟨.data b::dl,dr⟩ ⟨.data f::cl,cr⟩ pos)=
      cfg .back src ⟨dl,.data b::dr⟩ ⟨cl,.data f::cr⟩ (shift pos 0 (-1) (-1)) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,
    Tape.read,Microcode.Action.apply,Tape.moveLeft,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext p <;> fin_cases p <;> simp [shift,sub_eq_add_neg]

theorem back_run (xs fs : List Bool) (hlen : fs.length=xs.length)
    (src : Tape Bool) (dl dr cr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    NativeZipper.run program (3*xs.length+3)
      (cfg .back src ⟨symbols xs++dl,dr⟩ ⟨symbols fs++[.start],cr⟩ pos)=
      cfg .done src ⟨dl,(symbols xs).reverse++dr⟩ ⟨[.start],(symbols fs).reverse++cr⟩
        (shift pos 0 (-xs.length) (-xs.length)) := by
  induction xs generalizing fs dr cr pos with
  | nil =>
    have hf : fs=[] := List.eq_nil_of_length_eq_zero hlen
    subst fs
    simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg,bank,
      Tape.read,Microcode.Action.apply,Tape.moveLeft,Tape.moveRight,symbols,NativeMicrocode.direction,Transpose.Dir.shift]
    constructor <;> funext p <;> fin_cases p <;> simp
  | cons b xs ih =>
    cases fs with
    | nil => simp at hlen
    | cons f fs =>
      have hf : fs.length=xs.length := by simpa using hlen
      rw [show 3*(b::xs).length+3=3+(3*xs.length+3) by simp;omega,NativeZipper.run_add]
      simp only [symbols,List.map_cons,List.cons_append]
      rw [back_bit]
      simp only [symbols] at ih
      rw [ih fs hf,shift_add]
      simp [symbols,List.reverse_cons,List.append_assoc]

abbrev Trace := OperationalTrace.Trace (NativeMicrocode.step program) (NativeMicrocode.Active program)

theorem block_trace (xs fs : List Bool) (hlen : fs.length=xs.length)
    (sl sr cr : List (Sym Bool)) (pos : Fin 3 → ℤ) :
    ∃ t≤6*xs.length+5, Trace t
      (cfg .scan ⟨sl,symbols xs++sr⟩ ⟨[.start],[]⟩ ⟨[.start],symbols fs++.stop::cr⟩ pos).denote
      (cfg .done ⟨(symbols xs).reverse++sl,sr⟩ ⟨[.start],symbols xs++[.stop]⟩
        ⟨[.start],symbols fs++.stop::cr⟩ (shift pos xs.length 0 0)).denote := by
  apply NativeZipper.trace_of_run program
  rw [show 6*xs.length+5=(3*xs.length+2)+(3*xs.length+3) by omega,NativeZipper.run_add,scan_run xs fs hlen]
  have hb := back_run xs.reverse fs.reverse (by simpa using hlen)
    (⟨(symbols xs).reverse++sl,sr⟩ : Tape Bool) [.start] [.stop] (.stop::cr)
    (shift pos xs.length xs.length xs.length)
  simpa [symbols,List.map_reverse,shift_add] using hb

end BitWord.NativeBoundedCopy
