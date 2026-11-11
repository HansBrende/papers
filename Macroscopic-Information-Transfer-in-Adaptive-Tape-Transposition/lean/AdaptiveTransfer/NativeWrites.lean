import Transpose.Statement
import Mathlib.Tactic

/-! The actual native OLD-position write convention. No execution or replay
correctness hypothesis is built into these statements. -/

namespace AdaptiveTransfer

open Transpose

theorem step_work_update {M : TM} {w : List Bool} {c c' : Config M}
    (hstep : step M w c = some c') (h : Fin M.k) (z : ℤ) :
    c'.work h z = if z = c.workPos h then c'.work h (c.workPos h) else c.work h z := by
  unfold step at hstep
  split at hstep
  · contradiction
  · cases hstep
    simp

/-- The symbol at the old scanned location is the actual instruction's write. -/
theorem step_scanned_write {M : TM} {w : List Bool} {c c' : Config M}
    {q : Fin (M.q + 1)} {move : Dir} {acts : Fin M.k → Fin (M.g + 1) × Dir}
    {out : Option Bool}
    (hinstr : M.δ c.state (readInput w c.inPos) (fun i => c.work i (c.workPos i)) =
      some (q, move, acts, out))
    (hstep : step M w c = some c') (h : Fin M.k) :
    c'.work h (c.workPos h) = (acts h).1 := by
  simp only [step, hinstr] at hstep
  cases hstep
  simp

theorem step_preserves_unscanned {M : TM} {w : List Bool} {c c' : Config M}
    (hstep : step M w c = some c') (h : Fin M.k) (z : ℤ)
    (hz : z ≠ c.workPos h) : c'.work h z = c.work h z := by
  rw [step_work_update hstep h z, ite_eq_right hz]

/-- Equality of the OLD observed tuple fixes the whole instruction, even if
unobserved work cells and previous unreadable output differ. -/
theorem instruction_eq_of_old_tuple {M : TM} {w v : List Bool} {c e : Config M}
    (hq : c.state = e.state)
    (hi : readInput w c.inPos = readInput v e.inPos)
    (hw : ∀ h, c.work h (c.workPos h) = e.work h (e.workPos h)) :
    M.δ c.state (readInput w c.inPos) (fun h => c.work h (c.workPos h)) =
      M.δ e.state (readInput v e.inPos) (fun h => e.work h (e.workPos h)) := by
  rw [hq, hi, funext hw]

/-- A prefix consists of successful native transitions, not frozen halt ticks. -/
structure ExecutionPrefix (M : TM) (w : List Bool) (T : ℕ) where
  config : ℕ → Config M
  initial : config 0 = init M
  successful : ∀ t < T, step M w (config t) = some (config (t + 1))

end AdaptiveTransfer
