import CascadeObstruction.CompilerSchedule

/-! Adapter from a finite tick list to the generic native compiler. -/

namespace CascadeObstruction.Compiler

open Transpose

set_option autoImplicit false

variable {α : Type*} {k g q : ℕ}

theorem position_of_list (xs : List α) (move : α → Dir) (n : ℕ) :
    position (fun i : Fin xs.length => move (xs.get i)) n =
      ((xs.take n).map (fun x => (move x).shift 0)).sum := by
  induction n with
  | zero => simp [position]
  | succ n ih =>
    by_cases hn : n < xs.length
    · simp only [position, hn, dite_true]
      rw [shift_eq_add, ih, ← List.take_concat_get' xs n hn]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, List.get_eq_getElem]
    · simp only [position, hn, dite_false]
      rw [ih]
      have hle := Nat.le_of_not_gt hn
      simp [List.take_of_length_le hle,
        List.take_of_length_le (hle.trans (Nat.le_succ n))]

def ofList (xs : List α) (inputMove : α → Dir) (workMove : α → Fin k → Dir)
    (append : α → Bool) (dataRule : Fin xs.length → DataRule k g q) :
    Program k g q xs.length :=
  ofSchedule (fun t => inputMove (xs.get t))
    (fun t => workMove (xs.get t)) (fun t => append (xs.get t)) dataRule

theorem list_input_trajectory (xs : List α) (inputMove : α → Dir)
    (workMove : α → Fin k → Dir) (append : α → Bool)
    (dataRule : Fin xs.length → DataRule k g q) (w : List Bool) (n : ℕ) :
    Transpose.Tape.inTraj
      (machine (ofList xs inputMove workMove append dataRule)) w n =
        ((xs.take n).map (fun x => (inputMove x).shift 0)).sum := by
  rw [ofList, scheduled_input_trajectory, position_of_list]

theorem list_work_trajectory (xs : List α) (inputMove : α → Dir)
    (workMove : α → Fin k → Dir) (append : α → Bool)
    (dataRule : Fin xs.length → DataRule k g q) (w : List Bool) (n : ℕ) (h : Fin k) :
    Transpose.Tape.workTraj
      (machine (ofList xs inputMove workMove append dataRule)) w n h =
        ((xs.take n).map (fun x => (workMove x h).shift 0)).sum := by
  rw [ofList, scheduled_work_trajectory]
  exact position_of_list xs (fun x => workMove x h) n

end CascadeObstruction.Compiler
