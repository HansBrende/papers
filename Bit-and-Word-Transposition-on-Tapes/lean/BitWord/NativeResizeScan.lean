import BitWord.NativeTapeCalls

/-! Fixed-port width conversion driven by two physical unary rulers. -/
namespace BitWord.NativeResizeScan
open FixedTapeCompiler CopyMachine TransposeFollowup
open NativeBankCalls NativeExpanderShearFrames

abbrev Port := Fin 4
inductive Label
  | begin | copy | readBit | writeBit (b : Bool)
  | pad | padWrite | dropRead | dropWrite
  | rewind (long : Bool) (pc : NativeSealBack.Label)
  | done | reject
  deriving DecidableEq, Fintype

def ruler (long : Bool) : Port := if long then 3 else 2

def programCore (expand loop : Bool) : Microcode.Program Port Label
  | .begin => if loop then .read 0 (fun s => match s with | .data _ => .copy | .stop => .done | _ => .reject) else .halt
  | .copy => .read 2 (fun s => match s with | .data _ => .readBit | .stop => .pad | _ => .reject)
  | .readBit => .read 0 (fun s => match s with | .data b => .writeBit b | _ => .reject)
  | .writeBit b => .act (fun p =>
      if p=1 then ⟨some (.data b),.right⟩ else ⟨none,.right⟩) .copy
  | .pad => .read 3 (fun s => match s with
      | .data _ => if expand then .padWrite else .dropRead
      | .stop => .rewind false .back | _ => .reject)
  | .padWrite => .act (fun p => if p=1 then ⟨some (.data false),.right⟩
      else if p=3 then ⟨none,.right⟩ else ⟨none,.stay⟩) .pad
  | .dropRead => .read 0 (fun s => match s with | .data _ => .dropWrite | _ => .reject)
  | .dropWrite => .act (fun p => if p=0 ∨ p=3 then ⟨none,.right⟩ else ⟨none,.stay⟩) .pad
  | .rewind long .done => .jump (if long then .begin else .rewind true .back)
  | .rewind long pc => (singleBinding (ruler long)).instruction (Label.rewind long) (NativeSealBack.program pc)
  | .done => .halt
  | .reject => .reject

abbrev program (expand : Bool) := programCore expand true

def cfg (pc : Label) (src out short long : Tape Bool) (pos : Port → ℤ) :
    NativeZipper.Config Port Label := ⟨⟨pc,![src,out,short,long]⟩,pos⟩

def positions (pos : Port → ℤ) (n m a b : ℕ) : Port → ℤ :=
  ![pos 0+n,pos 1+m,pos 2+a,pos 3+b]

@[simp] theorem positions_zero (pos : Port → ℤ) : positions pos 0 0 0 0=pos := by
  funext i; fin_cases i <;> simp [positions]

theorem positions_add (pos : Port → ℤ) (n m a b n' m' a' b' : ℕ) :
    positions (positions pos n m a b) n' m' a' b' =
      positions pos (n+n') (m+m') (a+a') (b+b') := by
  funext i; fin_cases i <;> simp [positions,Nat.cast_add] <;> ring

def unary (n : ℕ) : List (Sym Bool) := List.replicate n (.data false)
@[simp] theorem unary_zero : unary 0=[] := rfl
@[simp] theorem unary_succ (n : ℕ) : unary (n+1)=.data false::unary n := by
  simp [unary,List.replicate_succ]
theorem unary_append (n m : ℕ) : unary (n+m)=unary n++unary m := by
  exact List.replicate_add n m (Sym.data false)

theorem copy_bit (expand b : Bool) (sl sr al ar bl br : List (Sym Bool))
    (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) 3
      (cfg .copy ⟨sl,.data b::sr⟩ (NativeSealBack.openWord pre)
        ⟨al,.data false::ar⟩ ⟨bl,.data false::br⟩ pos)=
      cfg .copy ⟨.data b::sl,sr⟩ (NativeSealBack.openWord (pre++[b]))
        ⟨.data false::al,ar⟩ ⟨.data false::bl,br⟩ (positions pos 1 1 1 1) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    programCore,cfg,Tape.read,Microcode.Action.apply,Tape.write,Tape.moveRight,
    NativeSealBack.openWord,symbols,List.reverse_append,NativeMicrocode.direction,Transpose.Dir.shift]
  constructor <;> funext i <;> fin_cases i <;> simp [positions]

theorem copy_run (expand : Bool) (xs : List Bool) (sl sr al ar bl br : List (Sym Bool))
    (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) (3*xs.length)
      (cfg .copy ⟨sl,symbols xs++sr⟩ (NativeSealBack.openWord pre)
        ⟨al,unary xs.length++ar⟩ ⟨bl,unary xs.length++br⟩ pos)=
      cfg .copy ⟨(symbols xs).reverse++sl,sr⟩ (NativeSealBack.openWord (pre++xs))
        ⟨unary xs.length++al,ar⟩ ⟨unary xs.length++bl,br⟩
        (positions pos xs.length xs.length xs.length xs.length) := by
  induction xs generalizing sl al bl pre pos with
  | nil => simp [symbols,NativeZipper.run,OperationalTrace.run]
  | cons b xs ih =>
    rw [show 3*(b::xs).length=3+3*xs.length by simp; omega,NativeZipper.run_add]
    change NativeZipper.run (programCore expand loop) (3*xs.length)
      (NativeZipper.run (programCore expand loop) 3
        (cfg .copy ⟨sl,.data b::(symbols xs++sr)⟩ (NativeSealBack.openWord pre)
          ⟨al,.data false::(unary xs.length++ar)⟩ ⟨bl,.data false::(unary xs.length++br)⟩ pos)) = _
    rw [copy_bit (loop := loop),ih,positions_add]
    have hu (n : ℕ) (l : List (Sym Bool)) : unary n++.data false::l=unary (n+1)++l := by
      rw [unary_append n 1]; simp [unary,List.append_assoc]
    simp [symbols,List.reverse_cons,List.append_assoc,hu,Nat.add_comm]

def tailInput (expand : Bool) (extra : List Bool) (rest : List (Sym Bool)) :=
  if expand then rest else symbols extra++rest

def tailOutput (expand : Bool) (extra : List Bool) : List Bool :=
  if expand then List.replicate extra.length false else []

def consumed (expand : Bool) (extra : List Bool) : List Bool := if expand then [] else extra

theorem tail_bit (expand bit : Bool) (sl sr bl br : List (Sym Bool))
    (short : Tape Bool) (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) (if expand then 2 else 3)
      (cfg .pad ⟨sl,tailInput expand [bit] sr⟩ (NativeSealBack.openWord pre)
        short ⟨bl,.data false::br⟩ pos)=
      cfg .pad ⟨(symbols (consumed expand [bit])).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutput expand [bit])) short ⟨.data false::bl,br⟩
        (positions pos (consumed expand [bit]).length (tailOutput expand [bit]).length 0 1) := by
  cases expand <;> simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,
    programCore,cfg,tailInput,tailOutput,consumed,Tape.read,Microcode.Action.apply,Tape.write,Tape.moveRight,
    NativeSealBack.openWord,symbols,List.reverse_append,NativeMicrocode.direction,Transpose.Dir.shift]
  all_goals constructor <;> funext i <;> fin_cases i <;> simp [positions]

theorem tail_run (expand : Bool) (extra : List Bool) (sl sr bl br : List (Sym Bool))
    (short : Tape Bool) (pre : List Bool) (pos : Port → ℤ) (loop : Bool := true) :
    NativeZipper.run (programCore expand loop) ((if expand then 2 else 3)*extra.length)
      (cfg .pad ⟨sl,tailInput expand extra sr⟩ (NativeSealBack.openWord pre)
        short ⟨bl,unary extra.length++br⟩ pos)=
      cfg .pad ⟨(symbols (consumed expand extra)).reverse++sl,sr⟩
        (NativeSealBack.openWord (pre++tailOutput expand extra)) short ⟨unary extra.length++bl,br⟩
        (positions pos (consumed expand extra).length (tailOutput expand extra).length 0 extra.length) := by
  induction extra generalizing sl bl pre pos with
  | nil => cases expand <;> simp [NativeZipper.run,OperationalTrace.run,tailInput,tailOutput,consumed,symbols]
  | cons x xs ih =>
    rw [show (if expand then 2 else 3)*(x::xs).length =
      (if expand then 2 else 3)+(if expand then 2 else 3)*xs.length by cases expand <;> simp <;> omega,NativeZipper.run_add]
    have hs : tailInput expand (x::xs) sr=tailInput expand [x] (tailInput expand xs sr) := by
      cases expand <;> simp [tailInput,symbols]
    rw [hs]
    change NativeZipper.run (programCore expand loop) ((if expand then 2 else 3)*xs.length)
      (NativeZipper.run (programCore expand loop) (if expand then 2 else 3)
        (cfg .pad ⟨sl,tailInput expand [x] (tailInput expand xs sr)⟩ (NativeSealBack.openWord pre)
          short ⟨bl,.data false::(unary xs.length++br)⟩ pos)) = _
    rw [tail_bit (loop := loop),ih,positions_add]
    have hu (n : ℕ) (l : List (Sym Bool)) : unary n++.data false::l=unary (n+1)++l := by
      rw [unary_append n 1]; simp [unary,List.append_assoc]
    cases expand <;> simp [tailOutput,consumed,symbols,List.reverse_cons,List.append_assoc,
      List.replicate_succ,hu,Nat.add_comm]

end BitWord.NativeResizeScan
