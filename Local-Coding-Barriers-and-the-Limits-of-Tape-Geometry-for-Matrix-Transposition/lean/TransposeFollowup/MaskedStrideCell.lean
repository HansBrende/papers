import TransposeFollowup.ScheduledNativeIO

/-! One masked stride cell is a paid three-instruction update. It reads the
current bank bit and the previous-group buffer bit before overwriting either.
Prefix stores the output in the buffer; difference stores the original input.
Only two Boolean values are retained in finite control. Group rewinds and
raw IO are separate obligations, not hidden in this cell theorem. -/
namespace TransposeFollowup.MaskedStrideCell
open Classical FixedTapeCompiler
open CopyMachine (Sym)
open ScheduledNativeIO
set_option autoImplicit false

abbrev Mode := Bool × Bool
abbrev State := NativeIO.Config (Fin 2) Mode

def bit : Sym Bool → Bool
  | .data b => b
  | _ => false

def output (mask x prev : Bool) : Bool := Bool.xor x (mask && prev)

def stored (isPrefix mask x prev : Bool) : Bool := if isPrefix then output mask x prev else x

def actions (isPrefix mask : Bool) (m : Mode) : Fin 2 → Microcode.Action :=
  fun t => ⟨some (.data (if t=0 then output mask m.1 m.2 else stored isPrefix mask m.1 m.2)),.right⟩

def schedule (isPrefix mask : Bool) : ℕ → NativeIO.Program (Fin 2) Mode
  | 0 => fun _ => .work (.read 0 (fun s => (bit s,false)))
  | 1 => fun m => .work (.read 1 (fun s => (m.1,bit s)))
  | _+2 => fun m => .work (.act (actions isPrefix mask m) (false,false))

def readMode (c : State) : Mode := (bit (c.work.core.tapes 0).head,bit (c.work.core.tapes 1).head)

def result (isPrefix mask : Bool) (c : State) : State :=
  ⟨⟨⟨(false,false),fun t => (actions isPrefix mask (readMode c) t).actual (c.work.core.tapes t)⟩,
    fun t => c.work.pos t+1⟩,c.inputPos,c.outRev⟩

theorem trajectory_three (isPrefix mask : Bool) (w : List Bool) (c : State) :
    trajectory (schedule isPrefix mask) w c 3=result isPrefix mask c := by
  rfl

theorem active_schedule (isPrefix mask : Bool) (i : ℕ) (c : State) :
    NativeIO.Active (schedule isPrefix mask i) c := by
  cases i with
  | zero => simp [schedule,NativeIO.Active]
  | succ i => cases i <;> simp [schedule,NativeIO.Active]

theorem result_positions (isPrefix mask : Bool) (c : State) (t : Fin 2) :
    (result isPrefix mask c).work.pos t=c.work.pos t+1 := rfl

theorem result_cells (isPrefix mask : Bool) (c : State) (t : Fin 2) (z : ℤ) :
    AbsoluteTape.cells ((result isPrefix mask c).work.core.tapes t)
      ((result isPrefix mask c).work.pos t) z =
      if z=c.work.pos t then
        .data (if t=0 then output mask (readMode c).1 (readMode c).2
          else stored isPrefix mask (readMode c).1 (readMode c).2)
      else AbsoluteTape.cells (c.work.core.tapes t) (c.work.pos t) z := by
  simpa only [result,actions,NativeMicrocode.direction,Transpose.Dir.shift,Option.getD_some] using
    NativeMicrocode.action_cells (actions isPrefix mask (readMode c) t)
      (c.work.core.tapes t) (c.work.pos t) z

theorem native_cell {q : ℕ} (e : NativeMicrocode.Encoding (Fin 2) (Fin 4 × Mode) 2 q)
    (isPrefix mask : Bool) (w : List Bool) (c : State) :
    Transpose.stepN (NativeIO.machine e (program (schedule isPrefix mask) 3)) w 3
      ((lift 0 c).denote e (program (schedule isPrefix mask) 3)) =
      some ((lift 3 (result isPrefix mask c)).denote e (program (schedule isPrefix mask) 3)) ∧
    Transpose.step (NativeIO.machine e (program (schedule isPrefix mask) 3)) w
      ((lift 3 (result isPrefix mask c)).denote e (program (schedule isPrefix mask) 3))=none := by
  simpa [trajectory_three,lift] using
    native_run_and_halt e (schedule isPrefix mask) w c (fun i _ => active_schedule isPrefix mask i _)

theorem state_count (isPrefix mask : Bool) :
    (NativeIO.machine (NativeMicrocode.initialEncoding (T:=Fin 2)
      ((0,(false,false)) : Fin 4 × Mode)) (program (schedule isPrefix mask) 3)).q+1=16 := by
  exact native_state_count (schedule isPrefix mask) 3 (false,false)

end TransposeFollowup.MaskedStrideCell
