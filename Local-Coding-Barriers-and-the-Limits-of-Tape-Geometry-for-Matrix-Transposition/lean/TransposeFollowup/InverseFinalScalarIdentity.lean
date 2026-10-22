import TransposeFollowup.SL2CentralizerChart

/-! Replacing the final factor by its inverse removes the moving scalar
base set. The exact formula also exposes the nilpotent coefficient collapse. -/
namespace TransposeFollowup.SL2Projection
open Classical Matrix
set_option autoImplicit false
local notation "RMat" => Matrix (Fin 2) (Fin 2) ℝ
local notation "G" => Matrix.SpecialLinearGroup (Fin 2) ℝ

theorem scalarAffine_inverse_final_identity (b g : RMat) (s t p q : ℝ)
    (hb : Matrix.trace b = 0) :
    Matrix.trace (scalarAffine b p q * (scalarAffine b s t).adjugate * g *
        scalarAffine b p q * scalarAffine b s t * g.adjugate) =
      (scalarAffine b s t).det *
        (2 * (scalarAffine b p q).det * g.det +
          ((b * g - g * b).det - 4 * b.det * g.det) * q ^ 2) -
        t ^ 2 * (scalarAffine b p q).det * (b * g - g * b).det := by
  have hb' : b 1 1 = -b 0 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at hb
    linarith
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  simp only [scalarAffine, Matrix.det_fin_two, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hb']
  ring

theorem sl2_inverse_final_scalar_identity (b : RMat) (u v g : G) {s t p q : ℝ}
    (hb : Matrix.trace b = 0)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q) :
    Matrix.trace ((v * u⁻¹ * g * (v * u) * g⁻¹ : G) : RMat) =
      2 + ((b * (g : RMat) - (g : RMat) * b).det - 4 * b.det) * q ^ 2 -
        (b * (g : RMat) - (g : RMat) * b).det * t ^ 2 := by
  have hdu : (scalarAffine b s t).det = 1 := hu ▸ u.property
  have hdv : (scalarAffine b p q).det = 1 := hv ▸ v.property
  have hh := scalarAffine_inverse_final_identity b (g : RMat) s t p q hb
  simp only [hdu, hdv, Matrix.SpecialLinearGroup.det_coe, mul_one, one_mul] at hh
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hu, hv, mul_assoc, mul_comm] using hh

theorem sl2_inverse_final_scaled_projection (b : RMat) (u v g : G) {s t p q : ℝ}
    (hb : Matrix.trace b = 0)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q)
    (hD : (b * (g : RMat) - (g : RMat) * b).det ≠ 0) :
    let D := (b * (g : RMat) - (g : RMat) * b).det
    Matrix.trace ((v * u⁻¹ * g * (v * u) * g⁻¹ : G) : RMat) =
      2 - D * (t ^ 2 + (4 * b.det / D - 1) * q ^ 2) := by
  dsimp only
  rw [sl2_inverse_final_scalar_identity b u v g hb hu hv]
  field_simp
  ring

theorem sl2_inverse_final_nilpotent_identity (b : RMat) (u v g : G) {s t p q : ℝ}
    (hb : Matrix.trace b = 0) (hbd : b.det = 0)
    (hu : (u : RMat) = scalarAffine b s t) (hv : (v : RMat) = scalarAffine b p q) :
    Matrix.trace ((v * u⁻¹ * g * (v * u) * g⁻¹ : G) : RMat) =
      2 + (b * (g : RMat) - (g : RMat) * b).det * (q ^ 2 - t ^ 2) := by
  rw [sl2_inverse_final_scalar_identity b u v g hb hu hv, hbd]
  ring

end TransposeFollowup.SL2Projection
