import TransposeFollowup.NativeMatchingXorTagStream

/-! Read one physically encoded opcode row. Each two-bit opcode contributes
its first bit to its own page-mask tape. Output direction is fixed for the
call: leftward emission reverses the generator's descending B-row order.
The finite control depends only on the fixed page count, not on the data
size or row width. -/
namespace TransposeFollowup.NativeMatchingXorMaskRow
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port (q : ℕ) := Option (Fin q)
inductive Label (q : ℕ)
  | read (i : Fin (q+1)) | emit (i : Fin q) (b : Bool) | skip (i : Fin q) | done | reject
  deriving DecidableEq, Fintype

def direction (reverse : Bool) : Microcode.Move := if reverse then .left else .right

def program (reverse : Bool) : Microcode.Program (Port q) (Label q)
  | .read i => if hi : i.val<q then
      .read none (fun s => match s with | .data b => .emit ⟨i.val,hi⟩ b | _ => .reject)
    else .jump .done
  | .emit i b => .act (fun p => match p with
      | none => ⟨none,.right⟩
      | some j => if j=i then ⟨some (.data b),direction reverse⟩ else ⟨none,.stay⟩) (.skip i)
  | .skip i => .act (fun p => ⟨none,if p=none then .right else .stay⟩)
      (.read ⟨i.val+1,by omega⟩)
  | .done => .halt
  | .reject => .reject

def bank (input : Tape Bool) (out : Fin q → Tape Bool) : Port q → Tape Bool
  | none => input | some j => out j

def cfg (pc : Label q) (input : Tape Bool) (out : Fin q → Tape Bool)
    (pos : Port q → ℤ) : NativeZipper.Config (Port q) (Label q) := ⟨⟨pc,bank input out⟩,pos⟩

def pushed (reverse b : Bool) (t : Tape Bool) : Tape Bool :=
  if reverse then Tape.moveLeft (Tape.write t (.data b)) else Tape.moveRight (Tape.write t (.data b))

def writeOne (reverse : Bool) (i : ℕ) (b : Bool) (out : Fin q → Tape Bool) : Fin q → Tape Bool :=
  fun j => if j.val=i then pushed reverse b (out j) else out j

def advance (reverse : Bool) (i : ℕ) (pos : Port q → ℤ) : Port q → ℤ
  | none => pos none+2
  | some j => pos (some j)+if j.val=i then (if reverse then -1 else 1) else 0

def encode (xs : List (Bool×Bool)) : List Bool := xs.flatMap (fun p => [p.1,p.2])

def writeMany (reverse : Bool) : ℕ → List (Bool×Bool) → (Fin q → Tape Bool) → (Fin q → Tape Bool)
  | _, [], out => out
  | i, (a,_)::xs, out => writeMany reverse (i+1) xs (writeOne reverse i a out)

def advanceMany (reverse : Bool) : ℕ → ℕ → (Port q → ℤ) → (Port q → ℤ)
  | _, 0, pos => pos
  | i, n+1, pos => advanceMany reverse (i+1) n (advance reverse i pos)

theorem opcode_steps (reverse a b : Bool) (i : Fin q) (il ir : List (Sym Bool))
    (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    NativeZipper.run (program reverse) 3
      (cfg (.read ⟨i.val,by omega⟩) ⟨il,.data a::.data b::ir⟩ out pos)=
      cfg (.read ⟨i.val+1,by omega⟩) ⟨.data b::.data a::il,ir⟩
        (writeOne reverse i.val a out) (advance reverse i.val pos) := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,
    i.isLt,cfg,bank,Tape.read,Microcode.Action.apply]
  constructor
  · congr 1
    funext p
    cases p with
    | none => simp [bank,Tape.moveRight,Tape.write,Tape.read,Microcode.Action.apply]
    | some j =>
      by_cases hj : j=i
      · subst j
        cases reverse <;> simp [bank,writeOne,pushed,direction,Microcode.Action.apply]
      · have hv : j.val≠i.val := fun h => hj (Fin.ext h)
        cases reverse <;> simp [bank,writeOne,pushed,direction,Microcode.Action.apply,hj,hv]
  · funext p
    cases p with
    | none => simp [advance,NativeMicrocode.direction,Transpose.Dir.shift]; ring
    | some j =>
      by_cases hj : j=i
      · subst j; cases reverse <;> simp [advance,direction,NativeMicrocode.direction,Transpose.Dir.shift,sub_eq_add_neg]
      · have hv : j.val≠i.val := fun h => hj (Fin.ext h)
        cases reverse <;> simp [advance,direction,NativeMicrocode.direction,Transpose.Dir.shift,hj,hv]

theorem final_step (reverse : Bool) (input : Tape Bool) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    NativeZipper.run (program reverse) 1 (cfg (.read ⟨q,by omega⟩) input out pos)=cfg .done input out pos := by
  simp [NativeZipper.run,OperationalTrace.run,NativeZipper.step,Microcode.step,program,cfg]

theorem row_run (reverse : Bool) (i : ℕ) (xs : List (Bool×Bool)) (hi : i+xs.length=q)
    (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    NativeZipper.run (program reverse) (3*xs.length+1)
      (cfg (.read ⟨i,by omega⟩) ⟨il,symbols (encode xs)++ir⟩ out pos)=
      cfg .done ⟨(symbols (encode xs)).reverse++il,ir⟩
        (writeMany reverse i xs out) (advanceMany reverse i xs.length pos) := by
  induction xs generalizing i il out pos with
  | nil =>
    have he : i=q := by simpa using hi
    subst i
    simpa [encode,writeMany,advanceMany,symbols] using final_step reverse ⟨il,ir⟩ out pos
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    have hi' : i<q := by simp at hi; omega
    rw [show 3*((a,b)::xs).length+1=3+(3*xs.length+1) by simp;omega,NativeZipper.run_add]
    simp only [encode,List.flatMap_cons,List.cons_append,List.nil_append,symbols,List.map_cons,List.map_append]
    rw [opcode_steps reverse a b ⟨i,hi'⟩]
    have hh := ih (i+1) (by simp at hi;omega) (.data b::.data a::il)
      (writeOne reverse i a out) (advance reverse i pos)
    simpa only [encode,List.flatMap_cons,List.cons_append,List.nil_append,symbols,List.map_cons,
      List.map_append,List.reverse_append,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.singleton_append,writeMany,advanceMany,List.length_cons] using hh

abbrev Trace (reverse : Bool) := OperationalTrace.Trace (NativeMicrocode.step (program (q:=q) reverse))
  (NativeMicrocode.Active (program reverse))

theorem row_trace (reverse : Bool) (xs : List (Bool×Bool)) (hx : xs.length=q)
    (il ir : List (Sym Bool)) (out : Fin q → Tape Bool) (pos : Port q → ℤ) :
    ∃ t ≤ 3*q+1, Trace reverse t
      (cfg (.read ⟨0,by omega⟩) ⟨il,symbols (encode xs)++ir⟩ out pos).denote
      (cfg .done ⟨(symbols (encode xs)).reverse++il,ir⟩
        (writeMany reverse 0 xs out) (advanceMany reverse 0 q pos)).denote := by
  simpa only [hx] using NativeZipper.trace_of_run (program reverse)
    (row_run reverse 0 xs (by simpa using hx) il ir out pos)

end TransposeFollowup.NativeMatchingXorMaskRow
