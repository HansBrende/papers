import TransposeFollowup.MobiusUnipotentMatrices

/-! A local three-factor decomposition with parameters linear in entry
errors. The middle factor is a fixed conjugate of a lower unipotent. -/
namespace TransposeFollowup.RealMobius
open Classical
set_option autoImplicit false

def tiltedUnipotent (t : ℝ) : Group :=
  upperUnipotent 1 * lowerUnipotent t * (upperUnipotent 1)⁻¹

theorem tiltedUnipotent_coe (t : ℝ) :
    (tiltedUnipotent t : Matrix (Fin 2) (Fin 2) ℝ) = !![1 + t, -t; t, 1 - t] := by
  unfold tiltedUnipotent
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  change (!![1, 1; 0, 1] * !![1, 0; t, 1]) * !![1, -1; -(0), 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem upperUnipotent_one_mul_inversion_entries :
    (upperUnipotent 1 * inversionMatrix) 0 0 = 1 ∧
      (upperUnipotent 1 * inversionMatrix) 1 0 = 1 := by
  have heq : ((upperUnipotent 1 * inversionMatrix) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, -1; 1, 0] := by
    change !![1, 1; 0, 1] * !![0, -1; 1, 0] = _
    ext i k
    fin_cases i <;> fin_cases k <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  exact ⟨congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 0) heq,
    congrArg (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 1 0) heq⟩

theorem mobius_three_unipotent_factorization (g : Group) (ha : g 0 0 ≠ 0) :
    g = lowerUnipotent ((g 1 0 - (g 0 0 - 1)) / g 0 0) *
      tiltedUnipotent (g 0 0 - 1) * upperUnipotent ((g 0 1 + (g 0 0 - 1)) / g 0 0) := by
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℝ) =
    ((lowerUnipotent ((g 1 0 - (g 0 0 - 1)) / g 0 0) *
      tiltedUnipotent (g 0 0 - 1) * upperUnipotent ((g 0 1 + (g 0 0 - 1)) / g 0 0)) :
      Matrix (Fin 2) (Fin 2) ℝ)
  simp only [tiltedUnipotent_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> nlinarith [determinant g]

theorem mobius_local_factor_parameters (g : Group) {η : ℝ} (hη : η ≤ 1 / 2)
    (ha : |g 0 0 - 1| ≤ η) (hb : |g 0 1| ≤ η) (hc : |g 1 0| ≤ η) :
    0 < g 0 0 ∧ |(g 1 0 - (g 0 0 - 1)) / g 0 0| ≤ 4 * η ∧
      |(g 0 1 + (g 0 0 - 1)) / g 0 0| ≤ 4 * η := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans ha
  have ha' := abs_le.mp ha
  have hp : 0 < g 0 0 := by linarith
  have hn1 : |g 1 0 - (g 0 0 - 1)| ≤ 2 * η := by
    linarith [abs_sub (g 1 0) (g 0 0 - 1)]
  have hn2 : |g 0 1 + (g 0 0 - 1)| ≤ 2 * η := by
    linarith [abs_add_le (g 0 1) (g 0 0 - 1)]
  refine ⟨hp, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ g 0 0 by linarith)
      (show 0 ≤ 4 * η by positivity)
    nlinarith
  · rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ g 0 0 by linarith)
      (show 0 ≤ 4 * η by positivity)
    nlinarith

end TransposeFollowup.RealMobius
