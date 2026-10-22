import TransposeFollowup.NativeMicrocodeCore

/-! Exact finite-program execution in the first paper's machine model.
The run theorem preserves all absolute head positions. Active traces give
the partial stepN semantics, so a frozen halted run cannot count as further
executed instructions. Both halt and reject stop the compiled machine. -/

namespace TransposeFollowup.NativeMicrocode

open FixedTapeCompiler
open Microcode (Instruction Program)

set_option autoImplicit false
variable {T L : Type*} {k q : ℕ}

def Active (p : Program T L) (c : Config T L) : Prop :=
  p c.core.pc ≠ .halt ∧ p c.core.pc ≠ .reject

/-- A jump changes only the control label and consumes exactly one active step. -/
theorem jump_trace (p : Program T L) (c : Config T L) (next : L)
    (h : p c.core.pc = .jump next) :
    OperationalTrace.Trace (step p) (Active p) 1 c
      {c with core := {c.core with pc := next}} := by
  apply OperationalTrace.Trace.cons
  · simp [Active, h]
  · have hs : step p c = {c with core := {c.core with pc := next}} := by
      simp [step, Microcode.actualStep, h]
    rw [hs]
    exact .refl _

theorem step_none_iff (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (c : Config T L) :
    Transpose.step (machine e p) w (c.denote e p inputPos outRev) = none ↔
      ¬ Active p c := by
  cases hp : p c.core.pc <;>
    simp [Transpose.step, Config.denote, machine, delta, hp, Active]

theorem step_some_of_active (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (c : Config T L) (ha : Active p c) :
    Transpose.step (machine e p) w (c.denote e p inputPos outRev) =
      some ((step p c).denote e p inputPos outRev) := by
  cases hs : Transpose.step (machine e p) w (c.denote e p inputPos outRev) with
  | none => exact False.elim ((step_none_iff e p w inputPos outRev c).mp hs ha)
  | some d =>
    have hd : d = (step p c).denote e p inputPos outRev := by
      simpa [NativeMicrocode.totalStep, hs] using step_denote_core e p w inputPos outRev c
    exact congrArg some hd

abbrev run (p : Program T L) := OperationalTrace.run (step p)

theorem run_core (p : Program T L) (n : ℕ) (c : Config T L) :
    (run p n c).core = Microcode.actualRun p n c.core := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simpa only [run, OperationalTrace.run, step] using ih (step p c)

theorem run_denote_core (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) (n : ℕ) (c : Config T L) :
    OperationalTrace.run (NativeMicrocode.totalStep (machine e p) w) n
      (c.denote e p inputPos outRev) = (run p n c).denote e p inputPos outRev := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simpa only [OperationalTrace.run, step_denote_core] using ih (step p c)

/-- A previously checked relative-tape computation transfers to native
states and every cell, measured relative to the actual final head. Input
position and output are preserved. Head resets still require a position
proof; they do not follow from an equality of relative tapes. -/
theorem actual_result_transfers_core (e : Encoding T L k q) (p : Program T L)
    (w : List Bool) (inputPos : ℤ) (outRev : List Bool) (n : ℕ)
    (c : Config T L) (d : Microcode.ActualConfig T L)
    (h : Microcode.actualRun p n c.core = d) :
    let v := OperationalTrace.run (NativeMicrocode.totalStep (machine e p) w) n
      (c.denote e p inputPos outRev)
    v.state = e.label d.pc ∧ v.inPos = inputPos ∧ v.outRev = outRev ∧
      ∀ t z, v.work (e.port t) (v.workPos (e.port t) + z) =
        symbolCode ((d.tapes t).nth z) := by
  dsimp only
  rw [run_denote_core]
  have hc : (run p n c).core = d := (run_core p n c).trans h
  refine ⟨congrArg (fun x : Microcode.ActualConfig T L => e.label x.pc) hc,
    rfl, rfl, ?_⟩
  intro t z
  simp [Config.denote, AbsoluteTape.cells, hc]

theorem trace_stepN (e : Encoding T L k q) (p : Program T L) (w : List Bool)
    (inputPos : ℤ) (outRev : List Bool) {n : ℕ} {c d : Config T L}
    (h : OperationalTrace.Trace (step p) (Active p) n c d) :
    Transpose.stepN (machine e p) w n (c.denote e p inputPos outRev) =
      some (d.denote e p inputPos outRev) := by
  induction h with
  | refl c => rfl
  | cons ha tr ih =>
    rw [Transpose.stepN, step_some_of_active e p w inputPos outRev _ ha]
    exact ih

def blankConfig (start : L) : Config T L where
  core := ⟨start, fun _ => AbsoluteTape.blank⟩
  pos := fun _ => 0

theorem blank_denote (e : Encoding T L k q) (p : Program T L) (start : L)
    (hs : e.label start = 0) :
    (blankConfig start).denote e p 0 [] = Transpose.init (machine e p) := by
  unfold Config.denote blankConfig Transpose.init
  rw [hs]
  congr 1
  funext i z
  rw [AbsoluteTape.blank_cells]
  rfl

theorem operationalRun_eq_iterate {C : Type*} (f : C → C) (n : ℕ) (c : C) :
    OperationalTrace.run f n c = f^[n] c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [OperationalTrace.run, ih, Function.iterate_succ_apply]



theorem inactive_fixed (p : Program T L) (c : Config T L) (ha : ¬ Active p c) :
    step p c = c := by
  cases hp : p c.core.pc <;> simp_all [Active, step, Microcode.actualStep]

/-- Stopping at or before n microsteps yields the original bounded-halting
predicate. This program class itself leaves input and output untouched. -/
theorem computesWithin_of_stopped (e : Encoding T L k q) (p : Program T L)
    (w : List Bool) (start : L) (hs : e.label start = 0) (n : ℕ)
    (hh : ¬ Active p (run p n (blankConfig start))) :
    Transpose.ComputesWithin (machine e p) w [] n := by
  obtain ⟨t, ht, htr⟩ := OperationalTrace.prune (step p) (Active p)
    (inactive_fixed p) n (blankConfig start)
  refine ⟨t, ht, (run p n (blankConfig start)).denote e p 0 [], ?_, ?_, rfl⟩
  · rw [← blank_denote e p start hs]
    exact trace_stepN e p w 0 [] htr
  · exact (step_none_iff e p w 0 [] _).mpr hh

end TransposeFollowup.NativeMicrocode
