import TransposeFollowup.SchwartzDyadicRegularity

/-! Normalization in the actual L2 norm preserves the Schwartz function,
its Fourier zero set and its relative dyadic regularity bound. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

noncomputable def schwartzNormalizeL2 (u : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ‖u.toLp 2 volume‖⁻¹ • u

theorem schwartzNormalizeL2_toLp (u : 𝓢(ℝ, ℂ)) :
    (schwartzNormalizeL2 u).toLp 2 volume = ‖u.toLp 2 volume‖⁻¹ • u.toLp 2 volume :=
  schwartz_toLp_real_smul _ u

theorem schwartzNormalizeL2_norm (u : 𝓢(ℝ, ℂ)) (hu : u.toLp 2 volume ≠ 0) :
    ‖(schwartzNormalizeL2 u).toLp 2 volume‖ = 1 := by
  rw [schwartzNormalizeL2_toLp, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

theorem schwartzNormalizeL2_regularity_le (j : ℕ) (u : 𝓢(ℝ, ℂ))
    (hu : u.toLp 2 volume ≠ 0) {R : ℝ}
    (hcost : schwartzDyadicRegularityCost j u ≤ R * ‖u.toLp 2 volume‖ ^ 2) :
    schwartzDyadicRegularityCost j (schwartzNormalizeL2 u) ≤ R := by
  rw [schwartzNormalizeL2, schwartzDyadicRegularityCost_real_smul]
  calc
    _ ≤ (‖u.toLp 2 volume‖⁻¹) ^ 2 * (R * ‖u.toLp 2 volume‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcost (sq_nonneg _)
    _ = R := by
      have hn := norm_ne_zero_iff.mpr hu
      field_simp

theorem schwartzNormalizeL2_operator_norm_gt (u : 𝓢(ℝ, ℂ)) (hu : u.toLp 2 volume ≠ 0)
    (T : ComplexL2 →L[ℝ] ComplexL2) {r : ℝ}
    (hr : r * ‖u.toLp 2 volume‖ < ‖T (u.toLp 2 volume)‖) :
    r < ‖T ((schwartzNormalizeL2 u).toLp 2 volume)‖ := by
  have hn : 0 < ‖u.toLp 2 volume‖ := norm_pos_iff.mpr hu
  rw [schwartzNormalizeL2_toLp, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn)]
  calc
    r = ‖u.toLp 2 volume‖⁻¹ * (r * ‖u.toLp 2 volume‖) := by
      field_simp
    _ < _ := mul_lt_mul_of_pos_left hr (inv_pos.mpr hn)

theorem schwartzNormalizeL2_fourier_zero (u : 𝓢(ℝ, ℂ)) {ξ : ℝ}
    (hξ : (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (𝓕 (schwartzNormalizeL2 u) : 𝓢(ℝ, ℂ)) ξ = 0 := by
  rw [schwartzNormalizeL2, FourierTransform.fourier_smul, smul_apply, hξ, smul_zero]

theorem schwartzNormalizeL2_energy_bounds (j : ℕ) (u : 𝓢(ℝ, ℂ))
    (hu : u.toLp 2 volume ≠ 0) {R : ℝ}
    (hcost : schwartzDyadicRegularityCost j u ≤ R * ‖u.toLp 2 volume‖ ^ 2) :
    let F := schwartzNormalizeL2 u
    (∫ x, x ^ 2 * ‖F x‖ ^ 2) ≤ R ∧
      ((∫ x, ‖deriv F x‖ ^ 2) + (∫ x, x ^ 4 * ‖deriv F x‖ ^ 2)) ≤ ((2 : ℝ) ^ j) ^ 2 * R ∧
      (∫ x, x ^ 2 * ‖deriv F x‖ ^ 2) ≤ ((2 : ℝ) ^ j) ^ 2 * R := by
  let F := schwartzNormalizeL2 u
  have hF : schwartzDyadicRegularityCost j F ≤ R := schwartzNormalizeL2_regularity_le j u hu hcost
  have hd := (schwartzDyadicRegularityCost_deriv_energy_le j F).trans
    (mul_le_mul_of_nonneg_left hF (sq_nonneg _))
  exact ⟨(schwartzDyadicRegularityCost_components_le j F).2.1.trans hF,
    hd, (schwartz_deriv_first_moment_energy_le F).trans hd⟩

end TransposeFollowup
