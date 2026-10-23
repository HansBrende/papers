import Mathlib

/-! Explicit expansions of sums over small `Fin n`, used by the certificates. -/

namespace MotionDepthCodes

open scoped BigOperators
set_option autoImplicit false

theorem sum_fin_5 (f : Fin 5 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 :=
  Fin.sum_univ_five f

theorem sum_fin_10 (f : Fin 10 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have h : ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + 0))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  rw [h]
  ring

theorem sum_fin_14 (f : Fin 14 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 +
      f 13 := by
  have h : ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f
      11 + (f 12 + (f 13 + 0))))))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  rw [h]
  ring

theorem sum_fin_16 (f : Fin 16 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 +
      f 13 + f 14 + f 15 := by
  have h : ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f
      11 + (f 12 + (f 13 + (f 14 + (f 15 + 0))))))))))))))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    rfl
  rw [h]
  ring

end MotionDepthCodes
