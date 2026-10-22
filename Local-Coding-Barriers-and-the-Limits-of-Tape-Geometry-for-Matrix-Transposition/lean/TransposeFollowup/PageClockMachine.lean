import TransposeFollowup.NativeClosedStream
import TransposeFollowup.FinitePortBinding
import TransposeFollowup.RecordMotion

/-! A physical Boolean clock drives all blank page tapes simultaneously.
A read followed by an action costs two native transitions per clock cell.
The supplied fixed-size opcode vector can be placed in a caller's finite
control; this primitive does not assume that it has been fetched for free. -/
namespace TransposeFollowup.PageClock
open FixedTapeCompiler CopyMachine
set_option autoImplicit false
variable {q : ℕ}
abbrev Port (q : ℕ) := Option (Fin q)
inductive Label | read | tick (moving : Bool) | done | reject
  deriving DecidableEq,Fintype

def move (op : PageOpcode) : Microcode.Move :=
  match op with | .idle => .stay | .openEdge => .right | .closeEdge => .left

def actions (ops : Fin q → PageOpcode) (b : Bool) : Port q → Microcode.Action
  | none => ⟨none,.right⟩
  | some p => ⟨none,if b then move (ops p) else .stay⟩
def program (ops : Fin q → PageOpcode) : Microcode.Program (Port q) Label
  | .read => .read none (fun s => match s with | .data b => .tick b | .stop => .done | _ => .reject)
  | .tick b => .act (actions ops b) .read
  | .done => .halt
  | .reject => .reject

def bank (clock : Tape Bool) : Port q → Turing.Tape (Sym Bool)
  | none => clock.denote
  | some _ => AbsoluteTape.blank
def cfg (pc : Label) (clock : Tape Bool) (pos : Port q → ℤ) : NativeMicrocode.Config (Port q) Label :=
  ⟨⟨pc,bank clock⟩,pos⟩
def advance (ops : Fin q → PageOpcode) (pos : Port q → ℤ) (cells count : ℕ) : Port q → ℤ
  | none => pos none+cells
  | some p => pos (some p)+(ops p).direction*count
abbrev Trace (ops : Fin q → PageOpcode) :=
  OperationalTrace.Trace (NativeMicrocode.step (program ops)) (NativeMicrocode.Active (program ops))

theorem advance_zero (ops : Fin q → PageOpcode) (pos : Port q → ℤ) : advance ops pos 0 0=pos := by
  funext p;cases p <;> simp [advance]
theorem advance_add (ops : Fin q → PageOpcode) (pos : Port q → ℤ) (a b c d : ℕ) :
    advance ops (advance ops pos a b) c d=advance ops pos (a+c) (b+d) := by
  funext p;cases p <;> simp [advance,add_assoc,mul_add]

theorem blank_move (d : Microcode.Move) :
    (Microcode.Action.actual ⟨none,d⟩ (AbsoluteTape.blank : Turing.Tape (Sym Bool)))=AbsoluteTape.blank := by
  have hb:Turing.ListBlank.mk ([default] : List (Sym Bool))=Turing.ListBlank.mk []:=EraseStream.blanks_eq_nil 1
  cases d <;> simp [Microcode.Action.actual,AbsoluteTape.blank,Turing.Tape.mk₂,hb]

theorem action_bank (ops : Fin q → PageOpcode) (b : Bool) (clock : Tape Bool) :
    (fun p => (actions ops b p).actual (bank clock p))=bank clock.moveRight := by
  funext p;cases p with
  | none => exact (CopyMachine.denote_right clock).symm
  | some p => exact blank_move _

theorem tick_positions (ops : Fin q → PageOpcode) (b : Bool) (pos : Port q → ℤ) :
    (fun p => (NativeMicrocode.direction (actions ops b p).move).shift (pos p))=
      advance ops pos 1 (if b then 1 else 0) := by
  funext p;cases p with
  | none => rfl
  | some p => cases b <;> cases h:ops p <;>
      simp [actions,advance,move,h,NativeMicrocode.direction,Transpose.Dir.shift,PageOpcode.direction,sub_eq_add_neg]

theorem read_data (ops : Fin q → PageOpcode) (b : Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    NativeMicrocode.step (program ops) (cfg .read ⟨pre,.data b::post⟩ pos)=
      cfg (.tick b) ⟨pre,.data b::post⟩ pos := by
  simp [NativeMicrocode.step,Microcode.actualStep,program,cfg,bank,Tape.read]

theorem tick_step (ops : Fin q → PageOpcode) (b : Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    NativeMicrocode.step (program ops) (cfg (.tick b) ⟨pre,.data b::post⟩ pos)=
      cfg .read ⟨.data b::pre,post⟩ (advance ops pos 1 (if b then 1 else 0)) := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,cfg,action_bank,tick_positions,Tape.moveRight,Tape.read,List.tail_cons,List.headD_cons]

theorem two_trace (ops : Fin q → PageOpcode) (b : Bool) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 2 (cfg .read ⟨pre,.data b::post⟩ pos)
      (cfg .read ⟨.data b::pre,post⟩ (advance ops pos 1 (if b then 1 else 0))) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,program,cfg]
  · rw [read_data]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,cfg]
    · rw [tick_step];exact .refl _

theorem stop_trace (ops : Fin q → PageOpcode) (pre post : List (Sym Bool)) (pos : Port q → ℤ) :
    Trace ops 1 (cfg .read ⟨pre,.stop::post⟩ pos) (cfg .done ⟨pre,.stop::post⟩ pos) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,program,cfg]
  · simpa [NativeMicrocode.step,Microcode.actualStep,program,cfg,bank,Tape.read] using
      (OperationalTrace.Trace.refl (step:=NativeMicrocode.step (program ops)) (active:=NativeMicrocode.Active (program ops))
        (cfg .done ⟨pre,.stop::post⟩ pos))

end TransposeFollowup.PageClock
