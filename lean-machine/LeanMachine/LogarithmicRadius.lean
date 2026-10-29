import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A finite logarithmic radius with a square-root ball-growth budget. -/

namespace LeanMachine

/-- An explicit radius works from `x >= A^4` onward. The estimate retains
ordinary logarithms, so its constants can be used directly in uniform bounds. -/
theorem exists_logarithmic_radius {A x : ℝ} (hA : 1 < A) (hx : A ^ 4 ≤ x) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ A ^ ℓ ≤ Real.sqrt x ∧ Real.log x / (4 * Real.log A) ≤ ℓ := by
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hx1 : 1 < x := (one_lt_pow₀ hA (by decide : (4 : ℕ) ≠ 0)).trans_le hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hy : 4 ≤ Real.logb A x :=
    (Real.le_logb_iff_rpow_le hA hx0).mpr (by simpa using hx)
  let ℓ := ⌊Real.logb A x / 2⌋₊
  have hu : (ℓ : ℝ) ≤ Real.logb A x / 2 := Nat.floor_le (by linarith)
  have hl := Nat.lt_floor_add_one (Real.logb A x / 2)
  have hlo : Real.logb A x / 4 ≤ (ℓ : ℝ) := by dsimp [ℓ]; linarith
  refine ⟨ℓ, Nat.floor_pos.mpr (by linarith), ?_, ?_⟩
  · calc
      A ^ ℓ = A ^ (ℓ : ℝ) := (Real.rpow_natCast A ℓ).symm
      _ ≤ A ^ (Real.logb A x / 2) := Real.rpow_le_rpow_of_exponent_le hA.le hu
      _ = (A ^ Real.logb A x) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hA0.le]; congr 1; ring
      _ = Real.sqrt x := by rw [Real.rpow_logb hA0 hA.ne' hx0, Real.sqrt_eq_rpow]
  · convert hlo using 1
    rw [Real.logb]; ring

end LeanMachine
