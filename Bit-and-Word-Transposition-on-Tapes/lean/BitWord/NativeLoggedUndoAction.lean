import BitWord.NativeLoggedUndoScan

/-! The two actual reverse actions restore one source transition, leaving only
the deliberately retained tapes and positions at their saved values. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
open CopyMachine (Sym)
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

theorem undo_two_steps (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c saved : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    NativeMicrocode.step (program p keep initial)
      (NativeMicrocode.step (program p keep initial)
        (atRecord (.unmove (record c)) (retain keep (NativeMicrocode.step p c) saved)
          (record c) history)) = loaded .back (retain keep c saved) history := by
  simp only [NativeMicrocode.step,Microcode.actualStep,program,atRecord,loaded]
  congr 1
  · congr 1
    funext z
    cases z with
    | data t =>
      cases hk : keep t
      · simp only [undoWrite,undoMove,retain,hk,Bool.false_eq_true,↓reduceIte,bank]
        change (⟨some (c.core.tapes t).head,.stay⟩ : Microcode.Action).actual
          ((⟨none,reverseMove (oldAction p (record c) t).move⟩ : Microcode.Action).actual
            ((NativeMicrocode.step p c).core.tapes t)) = c.core.tapes t
        rw [source_step_tape]
        exact undo_action (oldAction p (record c) t) (c.core.tapes t)
      · simp [undoWrite,undoMove,retain,hk,bank,idle,Microcode.Action.actual]
    | log r =>
      simp [undoWrite,undoMove,bank,idle,Microcode.Action.actual,Turing.Tape.mk₂,Turing.Tape.write_mk']
      exact congrArg (Turing.Tape.mk' (Turing.ListBlank.mk (logSymbols history r ++ [.start])))
        (EraseStream.blanks_eq_nil 1)
  · funext z
    cases z with
    | data t =>
      cases hk : keep t
      · simp only [undoWrite,undoMove,retain,hk,Bool.false_eq_true,↓reduceIte,positions,
          NativeMicrocode.direction,Transpose.Dir.shift]
        change (NativeMicrocode.direction (reverseMove (oldAction p (record c) t).move)).shift
          ((NativeMicrocode.step p c).pos t) = c.pos t
        rw [source_step_position]
        exact undo_position (oldAction p (record c) t).move (c.pos t)
      · simp [undoWrite,undoMove,retain,hk,positions,idle,NativeMicrocode.direction,Transpose.Dir.shift]
    | log r =>
      simp [undoWrite,undoMove,positions,idle,NativeMicrocode.direction,Transpose.Dir.shift]

/-- Both reverse actions are active microsteps, not a frozen halted execution. -/
theorem undo_record (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c saved : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    Trace p keep initial 2
      (atRecord (.unmove (record c)) (retain keep (NativeMicrocode.step p c) saved)
        (record c) history)
      (loaded .back (retain keep c saved) history) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,program,atRecord]
  · apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,NativeMicrocode.step,Microcode.actualStep,program,atRecord]
    · rw [undo_two_steps]
      exact .refl _
end BitWord.NativeLogged
