import TransposeFollowup.ScalarCentralizerProjection

/-! Exact real algebra for the scalar-amplification step. The common
centralizer is represented by the existing `scalarAffine` coordinates.
The trace separation identity requires no diagonalization or spectral gap. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem scalarAffine_mul (a : RMat) (s t p q : ℝ) :
    scalarAffine a s t * scalarAffine a p q =
      scalarAffine a (s * p - t * q * a.det)
        (s * q + t * p + t * q * Matrix.trace a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarAffine, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.trace, Matrix.diag] <;> ring

theorem scalarAffine_adjugate (a : RMat) (s t : ℝ) :
    (scalarAffine a s t).adjugate =
      scalarAffine a (s + t * Matrix.trace a) (-t) := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarAffine, Matrix.trace, Matrix.diag, Fin.sum_univ_two] <;> ring

theorem scalarAffine_discriminant (a : RMat) (s t : ℝ) :
    (Matrix.trace (scalarAffine a s t)) ^ 2 - 4 * (scalarAffine a s t).det =
      t ^ 2 * ((Matrix.trace a) ^ 2 - 4 * a.det) := by
  simp only [scalarAffine, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scalarAffine_coefficient_square_identity (a : RMat) (s t p q : ℝ) :
    (s * q + t * p + t * q * Matrix.trace a) ^ 2 + (t * p - s * q) ^ 2 =
      2 * (t ^ 2 * (scalarAffine a p q).det + q ^ 2 * (scalarAffine a s t).det) +
        ((Matrix.trace a) ^ 2 - 4 * a.det) * t ^ 2 * q ^ 2 := by
  simp only [scalarAffine, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem scalarAffine_trace_separation (a g : RMat) (s t p q : ℝ) :
    Matrix.trace (scalarAffine a p q * (scalarAffine a s t).adjugate * g *
      scalarAffine a p q * scalarAffine a s t * g) =
      (scalarAffine a s t).det *
        Matrix.trace (scalarAffine a p q * g * scalarAffine a p q * g) +
      t ^ 2 * (scalarAffine a p q).det * (a * g - g * a).det := by
  rw [Matrix.adjugate_fin_two]
  simp only [scalarAffine, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem sl2_scalarAffine_inv (a : RMat) (u : G) {s t : ℝ}
    (hu : (u : RMat) = scalarAffine a s t) :
    ((u⁻¹ : G) : RMat) = scalarAffine a (s + t * Matrix.trace a) (-t) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, hu, scalarAffine_adjugate]

theorem sl2_scalarAffine_product_coordinates (a : RMat) (u v : G)
    {s t p q : ℝ} (hu : (u : RMat) = scalarAffine a s t)
    (hv : (v : RMat) = scalarAffine a p q) :
    ((u * v : G) : RMat) = scalarAffine a (s * p - t * q * a.det)
        (s * q + t * p + t * q * Matrix.trace a) ∧
    ((u * v⁻¹ : G) : RMat) = scalarAffine a
        (s * (p + q * Matrix.trace a) + t * q * a.det) (t * p - s * q) ∧
    (s * q + t * p + t * q * Matrix.trace a) ^ 2 + (t * p - s * q) ^ 2 =
      2 * (t ^ 2 + q ^ 2) + ((Matrix.trace a) ^ 2 - 4 * a.det) * t ^ 2 * q ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Matrix.SpecialLinearGroup.coe_mul, hu, hv] using scalarAffine_mul a s t p q
  · rw [Matrix.SpecialLinearGroup.coe_mul, hu, sl2_scalarAffine_inv a v hv, scalarAffine_mul]
    congr 1 <;> ring
  · have hdu : (scalarAffine a s t).det = 1 := hu ▸ u.property
    have hdv : (scalarAffine a p q).det = 1 := hv ▸ v.property
    simpa only [hdu, hdv, mul_one] using scalarAffine_coefficient_square_identity a s t p q

theorem sl2_scalarAffine_trace_separation (a : RMat) (u v g : G)
    {s t p q : ℝ} (hu : (u : RMat) = scalarAffine a s t)
    (hv : (v : RMat) = scalarAffine a p q) :
    Matrix.trace ((v * u⁻¹ * g * (v * u) * g : G) : RMat) =
      Matrix.trace ((v * g * v * g : G) : RMat) +
        t ^ 2 * (SL2Escape.pairSpanMatrix a (g : RMat)).det := by
  have hdu : (scalarAffine a s t).det = 1 := hu ▸ u.property
  have hdv : (scalarAffine a p q).det = 1 := hv ▸ v.property
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hu, hv, SL2Escape.pairSpanMatrix_det, mul_assoc, hdu, hdv, mul_one, one_mul] using
      scalarAffine_trace_separation a (g : RMat) s t p q

end TransposeFollowup.SL2Projection
