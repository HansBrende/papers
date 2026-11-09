import CascadeObstruction.CompilerCore

/-! Complete any prescribed unit-motion and append schedule with arbitrary
time-indexed simultaneous data rules, then compile it to the native model.
-/

namespace CascadeObstruction.Compiler

open Transpose
open scoped BigOperators

set_option autoImplicit false

abbrev DataRule (k g q : ℕ) :=
  Fin (q + 1) → Option Bool → (Fin k → Fin (g + 1)) →
    Fin (q + 1) × (Fin k → Fin (g + 1)) × Bool

variable {k g q T : ℕ}

/-- The moves and append decision depend only on the public time; the next
controller, all new work symbols, and the output bit may depend on the full
old local tuple. -/
def ofSchedule (inputMove : Fin T → Dir) (workMove : Fin T → Fin k → Dir)
    (append : Fin T → Bool) (dataRule : Fin T → DataRule k g q) : Program k g q T :=
  fun t c input scanned =>
    let r := dataRule t c input scanned
    (r.1, inputMove t, fun h => (r.2.1 h, workMove t h),
      if append t then some r.2.2 else none)

/-- Cumulative prescribed movement, frozen after the last instruction. -/
def position (move : Fin T → Dir) : ℕ → ℤ
  | 0 => 0
  | n + 1 => if hn : n < T then (move ⟨n, hn⟩).shift (position move n)
      else position move n

theorem shift_eq_add (d : Dir) (z : ℤ) : d.shift z = z + d.shift 0 := by
  cases d <;> simp [Dir.shift, sub_eq_add_neg]

theorem position_eq_sum (move : Fin T → Dir) (n : ℕ) :
    position move n =
      ∑ i ∈ Finset.range n, if hi : i < T then (move ⟨i, hi⟩).shift 0 else 0 := by
  induction n with
  | zero => simp [position]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : n < T
    · simp only [position, hn, dite_true]
      rw [shift_eq_add, ih]
    · simpa only [position, hn, dite_false, add_zero] using ih

theorem source_input_position (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) (w : List Bool) (n : ℕ) :
    (run (ofSchedule inputMove workMove append dataRule) w n).inputPos =
      position inputMove n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < T <;> simp [run, position, hn, advance, ofSchedule, ih]

theorem source_work_position (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) (w : List Bool) (n : ℕ) (h : Fin k) :
    (run (ofSchedule inputMove workMove append dataRule) w n).workPos h =
      position (fun t => workMove t h) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < T <;> simp [run, position, hn, advance, ofSchedule, ih]

theorem scheduled_input_trajectory (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) (w : List Bool) (n : ℕ) :
    Transpose.Tape.inTraj (machine (ofSchedule inputMove workMove append dataRule)) w n =
      position inputMove n := by
  rw [input_trajectory]
  exact source_input_position inputMove workMove append dataRule w n

theorem scheduled_work_trajectory (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) (w : List Bool) (n : ℕ) (h : Fin k) :
    Transpose.Tape.workTraj (machine (ofSchedule inputMove workMove append dataRule)) w n h =
      position (fun t => workMove t h) n := by
  rw [work_trajectory]
  exact source_work_position inputMove workMove append dataRule w n h

theorem scheduled_append (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) (w : List Bool) (n : ℕ) :
    (Transpose.Tape.outBit (machine (ofSchedule inputMove workMove append dataRule)) w n).isSome =
      if hn : n < T then append ⟨n, hn⟩ else false := by
  rw [outBit_eq]
  by_cases hn : n < T
  · simp only [hn, dite_true, ofSchedule]
    cases append ⟨n, hn⟩ <;> simp
  · simp [hn]

/-- Every data completion of a prescribed schedule is oblivious on all inputs,
including the halted suffix, in the original native definition. -/
theorem scheduled_oblivious (inputMove : Fin T → Dir)
    (workMove : Fin T → Fin k → Dir) (append : Fin T → Bool)
    (dataRule : Fin T → DataRule k g q) :
    Transpose.Tape.ObliviousOn
      (machine (ofSchedule inputMove workMove append dataRule)) Set.univ T := by
  refine ⟨fun w _ => haltsAt _ w, ?_⟩
  intro w _ w' _ n
  refine ⟨?_, ?_, ?_⟩
  · exact (scheduled_input_trajectory inputMove workMove append dataRule w n).trans
      (scheduled_input_trajectory inputMove workMove append dataRule w' n).symm
  · funext h
    exact (scheduled_work_trajectory inputMove workMove append dataRule w n h).trans
      (scheduled_work_trajectory inputMove workMove append dataRule w' n h).symm
  · rw [scheduled_append, scheduled_append]

end CascadeObstruction.Compiler
