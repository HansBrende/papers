import TransposeFollowup.SL2TraceProjection
import TransposeFollowup.ScalarCentralizerProjection
import Mathlib.LinearAlgebra.BilinearMap

/-! Exact real adjoint identities for selecting the frame needed by cubic
packing. Nilpotent test directions avoid a discriminant denominator. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- Columns are the row-major coordinates of `I`, `b`, `x`, and `y`. -/
def directionFrame (b x y : RMat) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, b 0 0, x 0 0, y 0 0;
     0, b 0 1, x 0 1, y 0 1;
     0, b 1 0, x 1 0, y 1 0;
     1, b 1 1, x 1 1, y 1 1]

theorem directionFrame_det_formula (b x y : RMat) :
    (directionFrame b x y).det =
      (b 1 1 - b 0 0) * (x 0 1 * y 1 0 - x 1 0 * y 0 1) +
      (x 0 0 - x 1 1) * (b 0 1 * y 1 0 - b 1 0 * y 0 1) +
      (y 1 1 - y 0 0) * (b 0 1 * x 1 0 - b 1 0 * x 0 1) := by
  rw [directionFrame, Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  ring

theorem directionFrame_nilpotent_brackets (b e : RMat)
    (hb : Matrix.trace b = 0) (he : Matrix.trace e = 0) (hed : e.det = 0) :
    (directionFrame b (e * b - b * e)
      (e * (e * b - b * e) - (e * b - b * e) * e)).det =
        4 * Matrix.trace (e * b) ^ 3 := by
  have hb' : b 1 1 = -b 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hb
    linarith
  have he' : e 1 1 = -e 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at he
    linarith
  have hed' : e 0 0 ^ 2 + e 0 1 * e 1 0 = 0 := by
    simp only [Matrix.det_fin_two, he'] at hed
    nlinarith only [hed]
  rw [directionFrame_det_formula]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.trace, Matrix.diag, hb', he']
  linear_combination
    -16 * (b 0 0 ^ 2 + b 0 1 * b 1 0) *
      (2 * e 0 0 * b 0 0 + e 0 1 * b 1 0 + e 1 0 * b 0 1) * hed'

theorem exists_nilpotent_trace_test (b : RMat) {ρ : ℝ} (hρ : 0 < ρ)
    (hpivot : ∃ i, ρ ≤ |noncentralCoordinates b i|) :
    ∃ e : RMat, Matrix.trace e = 0 ∧ e.det = 0 ∧
      (∀ i j, |e i j| ≤ 1) ∧ ρ / 3 ≤ |Matrix.trace (e * b)| := by
  by_cases hy : ρ / 3 ≤ |b 1 0|
  · refine ⟨!![0, 1; 0, 0], ?_, ?_, ?_, ?_⟩
    · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    · norm_num [Matrix.det_fin_two]
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num
    · simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] using hy
  by_cases hx : ρ / 3 ≤ |b 0 1|
  · refine ⟨!![0, 0; 1, 0], ?_, ?_, ?_, ?_⟩
    · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    · norm_num [Matrix.det_fin_two]
    · intro i j; fin_cases i <;> fin_cases j <;> norm_num
    · simpa [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two] using hx
  refine ⟨!![1, 1; -1, -1], ?_, ?_, ?_, ?_⟩
  · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · norm_num [Matrix.det_fin_two]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · have hz : ρ / 3 ≤ |b 0 0 - b 1 1 + b 1 0 - b 0 1| := by
      obtain ⟨i, hi⟩ := hpivot
      have hx' : |b 0 1| < ρ / 3 := lt_of_not_ge hx
      have hy' : |b 1 0| < ρ / 3 := lt_of_not_ge hy
      fin_cases i
      · change ρ ≤ |b 0 0 - b 1 1| at hi
        have hh : |b 0 0 - b 1 1| ≤
            |b 0 0 - b 1 1 + b 1 0 - b 0 1| + |b 1 0| + |b 0 1| := by
          have h₁ := norm_sub_le (b 0 0 - b 1 1 + b 1 0 - b 0 1) (b 1 0)
          simp only [Real.norm_eq_abs] at h₁
          have h₂ := abs_add_le (b 0 0 - b 1 1 - b 0 1) (b 0 1)
          have heq : b 0 0 - b 1 1 + b 1 0 - b 0 1 - b 1 0 =
              b 0 0 - b 1 1 - b 0 1 := by ring
          rw [heq] at h₁
          rw [sub_add_cancel] at h₂
          linarith
        linarith
      · change ρ ≤ |b 0 1| at hi
        linarith
      · change ρ ≤ |b 1 0| at hi
        linarith
    convert hz using 1
    congr 1
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem conjugation_sub_inverse_conjugation (g : G) (b : RMat) :
    (g : RMat) * b * (g⁻¹ : G) - (g⁻¹ : G) * b * (g : RMat) =
      Matrix.trace (g : RMat) • ((g : RMat) * b - b * (g : RMat)) := by
  have hi : ((g⁻¹ : G) : RMat) = Matrix.trace (g : RMat) • (1 : RMat) - (g : RMat) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  rw [hi]
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]
  module

/-- The last two columns of the frame determinant form a bilinear map. -/
def directionVolume (b : RMat) : RMat →ₗ[ℝ] RMat →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (directionFrame b x y).det)
    (by intro x z y; simp only [directionFrame_det_formula, Matrix.add_apply]; ring)
    (by intro t x y; simp only [directionFrame_det_formula, Matrix.smul_apply, smul_eq_mul]; ring)
    (by intro x y z; simp only [directionFrame_det_formula, Matrix.add_apply]; ring)
    (by intro t x y; simp only [directionFrame_det_formula, Matrix.smul_apply, smul_eq_mul]; ring)

theorem directionVolume_apply (b x y : RMat) :
    directionVolume b x y = (directionFrame b x y).det := rfl

end TransposeFollowup.SL2Projection
