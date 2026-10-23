import BitWord.NativeLoggedUndoAction

/-! Complete finite-history replay. The history certificate comes from actual
forward transitions; every undo transition is an active native microstep. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

/-- Read and remove one actual source-step record. -/
theorem unwind_record (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c saved : SourceConfig (T := T) (L := L)) (history : List (Record T L)) :
    Trace p keep initial (Fintype.card (Record T L)+5)
      (loaded .back (retain keep (NativeMicrocode.step p c) saved) (record c::history))
      (loaded .back (retain keep c saved) history) := by
  have ht := NativeCountedLoop.trace_trans
    (read_record p keep initial (retain keep (NativeMicrocode.step p c) saved) (record c) history)
    (undo_record p keep initial c saved history)
  have hh : Trace p keep initial ((Fintype.card (Record T L)+1+2)+1+1)
      (loaded .back (retain keep (NativeMicrocode.step p c) saved) (record c::history))
      (loaded .back (retain keep c saved) history) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,loaded]
    · rw [back_record_step]
      apply OperationalTrace.Trace.cons
      · simp [NativeMicrocode.Active,program,atRecord]
      · rw [check_record_step]
        exact ht
  simpa only [Nat.add_assoc] using hh

/-- Removing the literal history-start markers leaves no dirty history cell. -/
theorem clear_empty_history (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) :
    Trace p keep initial 3 (loaded .back c []) (cleared c) := by
  apply OperationalTrace.Trace.cons
  · simp [NativeMicrocode.Active,program,loaded]
  · rw [back_start_step]
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,program,atStart]
    · rw [check_start_step]
      apply OperationalTrace.Trace.cons
      · simp [NativeMicrocode.Active,program,atStart]
      · rw [erase_start_step]
        exact .refl _

/-- Exact backward replay/reset for every recorded source execution. Only the
chosen retained tapes and positions survive; all history tapes are blank at zero. -/
theorem undo_history (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    {origin c : SourceConfig (T := T) (L := L)} {n : ℕ} {history : List (Record T L)}
    (h : History p origin n c history) (saved : SourceConfig (T := T) (L := L)) :
    Trace p keep initial ((Fintype.card (Record T L)+5)*n+3)
      (loaded .back (retain keep c saved) history) (cleared (retain keep origin saved)) := by
  induction h with
  | nil => simpa using clear_empty_history p keep initial (retain keep origin saved)
  | more h ha ih =>
    have hh := NativeCountedLoop.trace_trans (unwind_record p keep initial _ saved _) ih
    convert hh using 1
    ring
end BitWord.NativeLogged
