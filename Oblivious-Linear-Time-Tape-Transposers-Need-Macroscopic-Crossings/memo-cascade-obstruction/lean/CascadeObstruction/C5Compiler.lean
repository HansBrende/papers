import CascadeObstruction.C5Trace
import CascadeObstruction.CompilerListSchedule

/-! The concrete tick words use the general simultaneous-update compiler.
The equalities below identify actual native head runs with their exact finite
schedule, for every data rule and input. -/

namespace CascadeObstruction.C5

open Transpose

set_option autoImplicit false

def workHead (h : Fin 2) : Fin 3 := ⟨h.val + 1, by omega⟩

theorem Tick.move_workHead (x : Tick) (h : Fin 2) :
    x.move (workHead h) = dirValue (x.work h) := by
  fin_cases h <;> simp [Tick.move, workHead, Tick.work]

def completion {g q : ℕ} (xs : List Tick)
    (rules : Fin xs.length → Compiler.DataRule 2 g q) :
    Compiler.Program 2 g q xs.length :=
  Compiler.ofList xs Tick.input Tick.work Tick.emit rules

theorem completion_work_trajectory {g q : ℕ} (xs : List Tick)
    (rules : Fin xs.length → Compiler.DataRule 2 g q)
    (w : List Bool) (n : ℕ) (h : Fin 2) :
    Transpose.Tape.workTraj (Compiler.machine (completion xs rules)) w n h =
      position xs (workHead h) n := by
  rw [completion, Compiler.list_work_trajectory]
  simp only [position, Tick.move_workHead, dirValue]

theorem completion_input_trajectory {g q : ℕ} (xs : List Tick)
    (rules : Fin xs.length → Compiler.DataRule 2 g q)
    (w : List Bool) (n : ℕ) :
    Transpose.Tape.inTraj (Compiler.machine (completion xs rules)) w n =
      position xs 0 n := by
  rw [completion, Compiler.list_input_trajectory]
  simp only [position, Tick.move, ite_true, dirValue]

theorem completion_oblivious {g q : ℕ} (xs : List Tick)
    (rules : Fin xs.length → Compiler.DataRule 2 g q) :
    Transpose.Tape.ObliviousOn
      (Compiler.machine (completion xs rules)) Set.univ xs.length :=
  Compiler.scheduled_oblivious _ _ _ _

end CascadeObstruction.C5
