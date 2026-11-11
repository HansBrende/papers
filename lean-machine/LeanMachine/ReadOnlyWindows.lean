import LeanMachine.ReadOnlyProgram
import Mathlib.Tactic

/-! Literal splitting of one read-only execution. Each step has one fixed
data slot, which can be optional for a no-read local step. Only the actual
entry state crosses a window boundary; emitted output is never fed back. -/

namespace LeanMachine.ReadOnlyStep
variable {S D O : Type*}

theorem run_append (left right : List (ReadOnlyStep S D O))
    (s : S) (u v : List D) (hlen : left.length = u.length) :
    run (left ++ right) s (u ++ v) =
      let first := run left s u
      let second := run right first.1 v
      (second.1, first.2 ++ second.2) := by
  induction left generalizing s u with
  | nil =>
    have hu : u = [] := List.length_eq_zero_iff.mp hlen.symm
    subst u
    rfl
  | cons step rest ih =>
    cases u with
    | nil => simp at hlen
    | cons datum us =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa only [List.cons_append, run, List.cons_append] using
        congrArg (fun r : S × List O => (r.1, (step.transition s datum).2 :: r.2))
          (ih (step.transition s datum).1 us hlen)

theorem run_output_length (steps : List (ReadOnlyStep S D O)) (s : S) (data : List D)
    (hlen : steps.length = data.length) : (run steps s data).2.length = steps.length := by
  induction steps generalizing s data with
  | nil => cases data <;> rfl
  | cons step rest ih =>
    cases data with
    | nil => simp at hlen
    | cons datum tail =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa only [run, List.length_cons] using congrArg (fun n => n+1)
        (ih (step.transition s datum).1 tail hlen)

/-- Starting at the actual state after `a` operations, a literal slice emits
exactly the corresponding slice of the one full output record. -/
theorem run_slice_output (steps : List (ReadOnlyStep S D O)) (s : S) (data : List D)
    (hlen : steps.length = data.length) (a n : ℕ) (han : a+n ≤ steps.length) :
    (run ((steps.drop a).take n) (run (steps.take a) s (data.take a)).1
      ((data.drop a).take n)).2 = ((run steps s data).2.drop a).take n := by
  have ha : a ≤ steps.length := by omega
  have hleft : (steps.take a).length = (data.take a).length := by simp [hlen]
  have hfirst := run_append (steps.take a) (steps.drop a) s (data.take a) (data.drop a) hleft
  simp only [List.take_append_drop] at hfirst
  have hout : (run steps s data).2 =
      (run (steps.take a) s (data.take a)).2 ++
        (run (steps.drop a) (run (steps.take a) s (data.take a)).1 (data.drop a)).2 :=
    congrArg Prod.snd hfirst
  have hlenleft : (run (steps.take a) s (data.take a)).2.length = a := by
    rw [run_output_length _ _ _ hleft, List.length_take, min_eq_left ha]
  have hdrop := @List.drop_left O (run (steps.take a) s (data.take a)).2
    (run (steps.drop a) (run (steps.take a) s (data.take a)).1 (data.drop a)).2
  rw [hlenleft] at hdrop
  rw [hout, hdrop]
  have htake : ((steps.drop a).take n).length = ((data.drop a).take n).length := by
    simp [hlen]
  have hsecond := run_append ((steps.drop a).take n) ((steps.drop a).drop n)
    (run (steps.take a) s (data.take a)).1 ((data.drop a).take n) ((data.drop a).drop n) htake
  simp only [List.take_append_drop] at hsecond
  have hlenn : (run ((steps.drop a).take n) (run (steps.take a) s (data.take a)).1
      ((data.drop a).take n)).2.length = n := by
    rw [run_output_length _ _ _ htake, List.length_take, List.length_drop, min_eq_left (by omega)]
  have hh := congrArg Prod.snd hsecond
  have hprefix := @List.take_left O
    (run ((steps.drop a).take n) (run (steps.take a) s (data.take a)).1 ((data.drop a).take n)).2
    (run ((steps.drop a).drop n)
      (run ((steps.drop a).take n) (run (steps.take a) s (data.take a)).1 ((data.drop a).take n)).1
      ((data.drop a).drop n)).2
  rw [hlenn] at hprefix
  rw [hh]
  exact hprefix.symm

end LeanMachine.ReadOnlyStep
