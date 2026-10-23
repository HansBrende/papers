import BitWord.NativeLoggedForward

/-! Recording an entire actual active trace; the history is derived from that
trace and is not a premise supplied by the input. -/
namespace BitWord.NativeLogged
open FixedTapeCompiler TransposeFollowup
set_option autoImplicit false
variable {T L : Type*} [Fintype T] [DecidableEq T] [Fintype L] [DecidableEq L]

 theorem history_extend (p : Microcode.Program T L)
    (origin : SourceConfig (T := T) (L := L)) {n c d}
    (ht : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d)
    {r history} (hh : History p origin r c history) :
    ∃ history', History p origin (r+n) d history' := by
  induction ht generalizing r history with
  | refl c => exact ⟨history,by simpa using hh⟩
  | cons ha tr ih =>
    obtain ⟨history',h⟩ := ih (History.more hh ha)
    exact ⟨history',by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h⟩

theorem forward_history (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (origin : SourceConfig (T := T) (L := L)) {n c history}
    (h : History p origin n c history) :
    Trace p keep initial (n*(Fintype.card T+1)) (forward origin []) (forward c history) := by
  induction h with
  | nil => simpa using (OperationalTrace.Trace.refl (forward origin []) : Trace p keep initial 0 _ _)
  | @more n c history hh ha ih =>
    have hs := source_step p keep initial c history ha
    simpa [Nat.add_mul] using NativeCountedLoop.trace_trans ih hs

theorem halt_trace (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    (c : SourceConfig (T := T) (L := L)) (history : List (Record T L))
    (hh : p c.core.pc=.halt) :
    Trace p keep initial (Fintype.card T+1) (forward c history) (loaded .back c history) := by
  have hs := scan_source p keep initial c.core.pc c history (Fintype.card T) le_rfl
    (fun _ => .blank) (by intro i hi; omega)
  have hj : Trace p keep initial 1
      (loaded (.scan c.core.pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history)
      (loaded .back c history) := by
    apply OperationalTrace.Trace.cons
    · simp [NativeMicrocode.Active,loaded,program,hh]
    · have he : NativeMicrocode.step (program p keep initial)
          (loaded (.scan c.core.pc (fun t => (c.core.tapes t).head) (Fin.last (Fintype.card T))) c history)=
          loaded .back c history := by
        simp [NativeMicrocode.step,Microcode.actualStep,loaded,program,hh]
      rw [he]; exact .refl _
  simpa [forward,start] using NativeCountedLoop.trace_trans hs hj

theorem logged_execution (p : Microcode.Program T L) (keep : T → Bool) (initial : L)
    {n : ℕ} {c d : SourceConfig (T := T) (L := L)}
    (ht : OperationalTrace.Trace (NativeMicrocode.step p) (NativeMicrocode.Active p) n c d)
    (hh : p d.core.pc=.halt) :
    ∃ history, History p c n d history ∧
      Trace p keep initial ((n+1)*(Fintype.card T+1))
        (forward c []) (loaded .back d history) := by
  obtain ⟨history,hist⟩ := history_extend p c ht (History.nil (p := p) (initial := c))
  have hist : History p c n d history := by simpa using hist
  refine ⟨history,hist,?_⟩
  simpa [Nat.add_mul] using NativeCountedLoop.trace_trans
    (forward_history p keep initial c hist) (halt_trace p keep initial d history hh)

end BitWord.NativeLogged
