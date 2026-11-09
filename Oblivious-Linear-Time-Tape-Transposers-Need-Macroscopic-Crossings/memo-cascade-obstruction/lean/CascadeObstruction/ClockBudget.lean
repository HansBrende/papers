import TransposeFollowup.ContractingStageClock

/-! Dyadic accounting for an actual unary, two-stage clock.

The hypotheses include the partition of physical execution ticks into stages.
This file does not construct that partition for any particular program.
-/

namespace CascadeObstruction

open TransposeFollowup.RegularMotion

set_option autoImplicit false

/-- One recursive child, two own-work stages, volume contraction one half. -/
abbrev DyadicClock (a P : ℝ) (T : ℕ) :=
  ContractingStageClock 1 2 (1 / 2) a 1 P T

/-- The total physical time is at most twice the root own-work budget. -/
theorem DyadicClock.total_time_le {a P : ℝ} {T : ℕ}
    (cl : DyadicClock a P T) (ha : 0 ≤ a) :
    (T : ℝ) ≤ 2 * a * P := by
  have ht := stage_clock_total_time_bound cl.nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) ha cl.children
    cl.label cl.A cl.E cl.bounded cl.partition cl.budget
  have hr : cl.V [] ≤ P := by simpa using cl.root
  calc
    (T : ℝ) ≤ a * cl.V [] / (1 - 1 / 2) := ht
    _ = 2 * a * cl.V [] := by ring
    _ ≤ 2 * a * P := mul_le_mul_of_nonneg_left hr (by positivity)

/-- All ticks at depth at least `h`, including all later stages, have a
geometric total budget.  There is no bound on the total number of stages. -/
theorem DyadicClock.deep_time_le {a P : ℝ} {T : ℕ}
    (cl : DyadicClock a P T) (ha : 0 ≤ a) (h : ℕ) :
    ((Finset.univ.filter (fun t : Fin T => h ≤ (cl.label t).1.length)).card : ℝ) ≤
      2 * a * P * (1 / 2 : ℝ) ^ h := by
  classical
  have ht := stage_clock_deep_work_bound cl.nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) ha cl.children
    cl.label cl.A cl.E cl.bounded cl.partition cl.budget h
  have hr : cl.V [] ≤ P := by simpa using cl.root
  calc
    _ ≤ a * cl.V [] * (1 / 2 : ℝ) ^ h / (1 - 1 / 2) := ht
    _ = (2 * a * cl.V []) * (1 / 2 : ℝ) ^ h := by ring
    _ ≤ (2 * a * P) * (1 / 2 : ℝ) ^ h :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity)

end CascadeObstruction
