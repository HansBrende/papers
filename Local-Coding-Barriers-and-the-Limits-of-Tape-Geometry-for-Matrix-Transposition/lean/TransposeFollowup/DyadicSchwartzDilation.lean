import TransposeFollowup.SmoothBandSpatialMoments

/-! Dyadic dilation on Schwartz space, with exact derivative scaling. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped ContDiff
set_option autoImplicit false

theorem dyadic_dilation_growth_bound (j : ℕ) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖((2 : ℝ) ^ j)⁻¹ * x‖) ^ k := by
  refine ⟨1, (2 : ℝ) ^ j, ?_⟩
  intro x
  have hp : 0 < (2 : ℝ) ^ j := by positivity
  rw [pow_one, norm_mul, Real.norm_eq_abs ((2 : ℝ) ^ j)⁻¹,
    abs_of_pos (inv_pos.mpr hp), mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  linarith

noncomputable def schwartzDyadicDilate (u : 𝓢(ℝ, ℂ)) (j : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => ((2 : ℝ) ^ j)⁻¹ * x)
    (by fun_prop) (dyadic_dilation_growth_bound j) u

theorem schwartzDyadicDilate_apply (u : 𝓢(ℝ, ℂ)) (j : ℕ) (x : ℝ) :
    schwartzDyadicDilate u j x = u (((2 : ℝ) ^ j)⁻¹ * x) := rfl

theorem schwartzDyadicDilate_zero (u : 𝓢(ℝ, ℂ)) : schwartzDyadicDilate u 0 = u := by
  ext x
  simp only [schwartzDyadicDilate_apply, pow_zero, inv_one, one_mul]

theorem schwartzDyadicDilate_sub (u v : 𝓢(ℝ, ℂ)) (j : ℕ) :
    schwartzDyadicDilate (u - v) j = schwartzDyadicDilate u j - schwartzDyadicDilate v j := rfl

theorem schwartzDyadicDilate_add_index (u : 𝓢(ℝ, ℂ)) (j k : ℕ) :
    schwartzDyadicDilate (schwartzDyadicDilate u k) j = schwartzDyadicDilate u (j + k) := by
  ext x
  simp only [schwartzDyadicDilate_apply, pow_add, mul_inv_rev]
  congr 1
  ring

theorem schwartzDyadicDilate_hasCompactSupport (u : 𝓢(ℝ, ℂ))
    (hu : HasCompactSupport (⇑u)) (j : ℕ) :
    HasCompactSupport (⇑(schwartzDyadicDilate u j)) :=
  hu.comp_smul (c := ((2 : ℝ) ^ j)⁻¹) (by positivity)

theorem schwartzDyadicDilate_iteratedDeriv (u : 𝓢(ℝ, ℂ)) (j n : ℕ) (x : ℝ) :
    iteratedDeriv n (schwartzDyadicDilate u j) x =
      (((2 : ℝ) ^ j)⁻¹) ^ n • iteratedDeriv n u (((2 : ℝ) ^ j)⁻¹ * x) := by
  exact congrFun (iteratedDeriv_comp_const_smul (u.smooth n) (((2 : ℝ) ^ j)⁻¹)) x

theorem schwartzDyadicDilate_iteratedDeriv_norm (u : 𝓢(ℝ, ℂ)) (j n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (schwartzDyadicDilate u j) x‖ =
      (((2 : ℝ) ^ j)⁻¹) ^ n * ‖iteratedDeriv n u (((2 : ℝ) ^ j)⁻¹ * x)‖ := by
  rw [schwartzDyadicDilate_iteratedDeriv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem schwartzFrequencyDerivative_dyadicDilate (u : 𝓢(ℝ, ℂ)) (j : ℕ) :
    schwartzFrequencyDerivative (schwartzDyadicDilate u j) =
      ((2 : ℝ) ^ j) • schwartzDyadicDilate (schwartzFrequencyDerivative u) j := by
  ext x
  simp only [schwartzFrequencyDerivative_apply, schwartzDyadicDilate_apply,
    smul_apply, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  have hp : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

end TransposeFollowup
