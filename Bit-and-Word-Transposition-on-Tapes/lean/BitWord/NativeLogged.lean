import TransposeFollowup.FiniteProgramEncodingCore
import TransposeFollowup.NativeCountedLoop

/-! A finite logging controller for a fixed microprogram. Every original step
is recorded on a constant bank of history tracks. After halt, the controller
undoes the work actions outside a designated retained set of tapes. History
records are literal one-hot bits; no growing object is stored in control. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false


abbrev Record (T L : Type*) := L × (T → Sym Bool)

inductive Port (T L : Type*) [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]
  | data (t : T) | log (r : Record T L)
  deriving Fintype

inductive Label (T L : Type*) [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]
  | scan (pc : L) (seen : T → Sym Bool) (next : Fin (Fintype.card T+1))
  | back | check
  | scanLog (found : Option (Record T L)) (next : Fin (Fintype.card (Record T L)+1))
  | unmove (record : Record T L) | restore (record : Record T L)
  | eraseStart | done | reject
  deriving Fintype

variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

noncomputable instance : DecidableEq (Port T L) := Classical.decEq _
noncomputable instance : DecidableEq (Label T L) := Classical.decEq _

noncomputable def sourcePort : Fin (Fintype.card T) → T := (Fintype.equivFin T).symm
noncomputable def historyPort : Fin (Fintype.card (Record T L)) → Record T L :=
  (Fintype.equivFin (Record T L)).symm

def idle : Microcode.Action := ⟨none,.stay⟩

def reverseMove : Microcode.Move → Microcode.Move
  | .left => .right | .right => .left | .stay => .stay

def oldAction (p : Microcode.Program T L) (r : Record T L) (t : T) : Microcode.Action :=
  match p r.1 with | .act a _ => a t | _ => idle

def nextPC (p : Microcode.Program T L) (r : Record T L) : L :=
  match p r.1 with
  | .read t next => next (r.2 t)
  | .act _ next | .jump next => next
  | .halt | .reject => r.1

def forwardActions (p : Microcode.Program T L) (r : Record T L) : Port T L → Microcode.Action
  | .data t => oldAction p r t
  | .log s => ⟨some (.data (decide (r=s))),.right⟩

def backActions : Port T L → Microcode.Action
  | .data _ => idle | .log _ => ⟨none,.left⟩

def undoMove (p : Microcode.Program T L) (keep : T → Bool) (r : Record T L) :
    Port T L → Microcode.Action
  | .data t => if keep t then idle else ⟨none,reverseMove (oldAction p r t).move⟩
  | .log _ => idle

def undoWrite (keep : T → Bool) (r : Record T L) : Port T L → Microcode.Action
  | .data t => if keep t then idle else ⟨some (r.2 t),.stay⟩
  | .log _ => ⟨some .blank,.stay⟩

def eraseStartActions : Port T L → Microcode.Action
  | .data _ => idle | .log _ => ⟨some .blank,.right⟩

def start (pc : L) : Label T L := .scan pc (fun _ => .blank) 0

noncomputable def program (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :
    Microcode.Program (Port T L) (Label T L)
  | .scan pc seen n =>
    if hn : n.val<Fintype.card T then
      .read (.data (sourcePort ⟨n.val,hn⟩)) (fun a =>
        .scan pc (Function.update seen (sourcePort ⟨n.val,hn⟩) a) ⟨n.val+1,by omega⟩)
    else match p pc with
      | .halt => .jump .back
      | .reject => .reject
      | _ => .act (forwardActions p (pc,seen)) (start (nextPC p (pc,seen)))
  | .back => .act backActions .check
  | .check => .read (.log (initial,fun _ => .blank)) (fun a => match a with
      | .start => .eraseStart | .data _ => .scanLog none 0 | _ => .reject)
  | .scanLog found n =>
    if hn : n.val<Fintype.card (Record T L) then
      .read (.log (historyPort ⟨n.val,hn⟩)) (fun a => match a with
        | .data true => .scanLog (some (historyPort ⟨n.val,hn⟩)) ⟨n.val+1,by omega⟩
        | .data false => .scanLog found ⟨n.val+1,by omega⟩
        | _ => .reject)
    else match found with | none => .reject | some r => .jump (.unmove r)
  | .unmove r => .act (undoMove p keep r) (.restore r)
  | .restore r => .act (undoWrite keep r) .back
  | .eraseStart => .act eraseStartActions .done
  | .done => .halt | .reject => .reject

/-- Undoing a recorded action restores its actual old tape, including blanks
and both infinite tails. -/
theorem undo_action (a : Microcode.Action) (t : Turing.Tape (Sym Bool)) :
    ((⟨some t.head,.stay⟩ : Microcode.Action).actual
      ((⟨none,reverseMove a.move⟩ : Microcode.Action).actual (a.actual t)))=t := by
  rcases a with ⟨w,m⟩
  cases w <;> cases m <;>
    simp [Microcode.Action.actual,reverseMove,Turing.Tape.write_self,Turing.Tape.write]

/-- The corresponding absolute head movement is also reversed. -/
theorem undo_position (m : Microcode.Move) (z : ℤ) :
    (NativeMicrocode.direction (reverseMove m)).shift ((NativeMicrocode.direction m).shift z)=z := by
  cases m <;> simp [reverseMove,NativeMicrocode.direction,Transpose.Dir.shift]

noncomputable def encoding (initial : L) :=
  NativeMicrocode.initialEncoding (T := Port T L) (start (T := T) initial)
noncomputable def machine (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :=
  NativeMicrocode.machine (encoding initial) (program p keep initial)

theorem finite_resources (p : Microcode.Program T L) (keep : T → Bool) (initial : L) :
    (machine p keep initial).k=Fintype.card (Port T L) ∧
    (machine p keep initial).g+1=5 ∧ (encoding (T := T) initial).label (start initial)=0 :=
  ⟨rfl,rfl,NativeMicrocode.initialEncoding_start _⟩

end BitWord.NativeLogged
