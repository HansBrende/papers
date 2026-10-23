import BitWord.NativeLoggedForward
import FixedTapeCompiler.EraseStream

/-! Exact frames while the last one-hot history record is being read and undone. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

/-- Logs point at the current record; all newer record cells are already blank. -/
def atRecord (pc : Label T L) (c : SourceConfig (T := T) (L := L))
    (r : Record T L) (history : List (Record T L)) : LoggedConfig (T := T) (L := L) :=
  ⟨⟨pc,fun z => match z with
      | .data t => c.core.tapes t
      | .log a => Turing.Tape.mk₂ (logSymbols history a ++ [.start]) [.data (decide (r=a))]⟩,
    fun z => match z with | .data t => c.pos t | .log _ => history.length⟩

/-- The literal initial marker has been reached, at absolute history position -1. -/
def atStart (pc : Label T L) (c : SourceConfig (T := T) (L := L)) :
    LoggedConfig (T := T) (L := L) :=
  ⟨⟨pc,fun z => match z with
      | .data t => c.core.tapes t | .log _ => Turing.Tape.mk₂ [] [.start]⟩,
    fun z => match z with | .data t => c.pos t | .log _ => -1⟩

/-- The required final frame: retained source data, blank history, history heads at zero. -/
def cleared (c : SourceConfig (T := T) (L := L)) : LoggedConfig (T := T) (L := L) :=
  ⟨⟨.done,fun z => match z with
      | .data t => c.core.tapes t | .log _ => Turing.Tape.mk₂ [] []⟩,
    fun z => match z with | .data t => c.pos t | .log _ => 0⟩

omit [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L] in
theorem source_step_tape (p : Microcode.Program T L) (c : SourceConfig (T := T) (L := L))
    (t : T) : (NativeMicrocode.step p c).core.tapes t =
      (oldAction p (record c) t).actual (c.core.tapes t) := by
  cases hp : p c.core.pc <;>
    simp [NativeMicrocode.step,Microcode.actualStep,oldAction,record,hp,idle,Microcode.Action.actual]

omit [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L] in
theorem source_step_position (p : Microcode.Program T L) (c : SourceConfig (T := T) (L := L))
    (t : T) : (NativeMicrocode.step p c).pos t =
      (NativeMicrocode.direction (oldAction p (record c) t).move).shift (c.pos t) := by
  cases hp : p c.core.pc <;>
    simp [NativeMicrocode.step,oldAction,record,hp,idle,NativeMicrocode.direction,Transpose.Dir.shift]

theorem back_record_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (r : Record T L) (history : List (Record T L)) :
    NativeMicrocode.step (program p keep initial) (loaded .back c (r::history)) =
      atRecord .check c r history := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,loaded,atRecord]
  congr 1
  · congr 1
    funext z
    cases z <;> simp [backActions,bank,logSymbols,Microcode.Action.actual,idle,Turing.Tape.mk₂]
  · funext z
    cases z <;> simp [backActions,positions,idle,NativeMicrocode.direction,Transpose.Dir.shift]

theorem check_record_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (r : Record T L) (history : List (Record T L)) :
    NativeMicrocode.step (program p keep initial) (atRecord .check c r history) =
      atRecord (.scanLog none 0) c r history := by
  simp [NativeMicrocode.step,Microcode.actualStep,program,atRecord,Turing.Tape.mk₂]

theorem back_start_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) :
    NativeMicrocode.step (program p keep initial) (loaded .back c []) = atStart .check c := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,loaded,atStart]
  congr 1
  · congr 1
    funext z
    cases z <;> simp [backActions,bank,logSymbols,Microcode.Action.actual,idle,Turing.Tape.mk₂]
  · funext z
    cases z <;> simp [backActions,positions,idle,NativeMicrocode.direction,Transpose.Dir.shift]

theorem check_start_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) :
    NativeMicrocode.step (program p keep initial) (atStart .check c) = atStart .eraseStart c := by
  simp [NativeMicrocode.step,Microcode.actualStep,program,atStart,Turing.Tape.mk₂]

theorem erase_start_step (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) :
    NativeMicrocode.step (program p keep initial) (atStart .eraseStart c) = cleared c := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,atStart,cleared]
  congr 1
  · congr 1
    funext z
    cases z <;> simp [eraseStartActions,Microcode.Action.actual,idle,Turing.Tape.mk₂,Turing.Tape.write_mk']
    exact congrArg (fun a => Turing.Tape.mk' a (Turing.ListBlank.mk [])) (EraseStream.blanks_eq_nil 1)
  · funext z
    cases z <;> simp [eraseStartActions,idle,NativeMicrocode.direction,Transpose.Dir.shift]

end BitWord.NativeLogged
