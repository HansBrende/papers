import TransposeFollowup.OpcodeRamp

/-! Exact per-step motion of a seven-phase record, using the first paper's
native head-direction type. The external clock and instruction fetch still
require a separately charged machine implementation. -/

namespace TransposeFollowup

set_option autoImplicit false

def PageOpcode.move : PageOpcode → Transpose.Dir
  | .idle => .stay
  | .openEdge => .right
  | .closeEdge => .left

def recordDirection (R : ℕ) (op : PageOpcode) (s : ℕ) : Transpose.Dir :=
  if R ≤ s ∧ s < 5 * R then op.move else .stay

def recordRun (R : ℕ) (op : PageOpcode) (z : ℤ) : ℕ → ℤ
  | 0 => z
  | s + 1 => (recordDirection R op s).shift (recordRun R op z s)

theorem recordDirection_shift (R : ℕ) (op : PageOpcode) (s : ℕ) (z : ℤ) :
    (recordDirection R op s).shift z = z + op.direction *
      (cappedRamp (4 * R) R (s + 1) - cappedRamp (4 * R) R s) := by
  by_cases h : R ≤ s ∧ s < 5 * R
  · have hr : cappedRamp (4 * R) R (s + 1) - cappedRamp (4 * R) R s = 1 := by
      dsimp [cappedRamp]
      omega
    rw [recordDirection, ite_eq_left h, hr, mul_one]
    cases op <;> simp [PageOpcode.move, PageOpcode.direction, Transpose.Dir.shift, sub_eq_add_neg]
  · have hr : cappedRamp (4 * R) R (s + 1) - cappedRamp (4 * R) R s = 0 := by
      dsimp [cappedRamp]
      omega
    rw [recordDirection, ite_eq_right h, hr, mul_zero, add_zero]
    rfl

theorem recordRun_eq (R : ℕ) (op : PageOpcode) (z : ℤ) (s : ℕ) :
    recordRun R op z s = z + op.direction * cappedRamp (4 * R) R s := by
  induction s with
  | zero => simp [recordRun, cappedRamp]
  | succ s ih =>
    rw [recordRun, recordDirection_shift, ih]
    ring

theorem recordRun_end (R : ℕ) (op : PageOpcode) (z : ℤ) :
    recordRun R op z (7 * R) = z + op.direction * (4 * R : ℕ) := by
  rw [recordRun_eq]
  have h : cappedRamp (4 * R) R (7 * R) = (4 * R : ℕ) := by
    dsimp [cappedRamp]
    omega
  rw [h]

theorem opcodeRampWalk_recordRun {v k : ℕ} (R offset : ℕ)
    (ops : Fin v → Fin k → PageOpcode) (p : Fin k) (i : Fin v)
    (s : ℕ) (hs : s ≤ 7 * R) :
    recordRun R (ops i p)
      (opcodeRampWalk R offset ops p (offset + 7 * R * i.val)) s =
      opcodeRampWalk R offset ops p (offset + 7 * R * i.val + s) := by
  rw [recordRun_eq]
  have h := opcodeRampWalk_record_delta R offset ops p i s hs
  omega

end TransposeFollowup
