import TransposeFollowup.L2FourierDerivative

/-! A weak L2 derivative controls the actual high-frequency component.
The estimate is stated first without division, so radius zero is allowed. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem highFrequency_scaled_norm_le_weak_derivative (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x)
    (R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi * R) * ‖highFrequency (Icc (-R) R) measurableSet_Icc f‖ ≤ ‖df‖ := by
  have hp : 0 ≤ 2 * Real.pi * R := by positivity
  have hnorm : ‖(2 * Real.pi * R : ℝ) •
      (𝓕 (highFrequency (Icc (-R) R) measurableSet_Icc f) : ComplexL2)‖ ≤
      ‖(𝓕 df : ComplexL2)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul (2 * Real.pi * R : ℝ)
      (𝓕 (highFrequency (Icc (-R) R) measurableSet_Icc f) : ComplexL2),
      highFrequency_fourier_coe (Icc (-R) R) measurableSet_Icc f,
      L2_fourier_weak_derivative_ae f df hweak] with ξ hsmul hhigh hdf
    rw [hsmul]
    change ‖(2 * Real.pi * R : ℝ) •
      (𝓕 (highFrequency (Icc (-R) R) measurableSet_Icc f) : ComplexL2) ξ‖ ≤ _
    rw [hhigh]
    by_cases hmem : ξ ∈ Icc (-R) R
    · simp [hmem]
    · rw [Set.indicator_of_mem (show ξ ∈ (Icc (-R) R)ᶜ from hmem), norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hp, hdf, norm_mul, frequency_derivative_symbol_norm]
      have hξ : R ≤ |ξ| := by
        by_contra hn
        exact hmem (abs_le.mp (le_of_lt (lt_of_not_ge hn)))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hξ (by positivity)) (norm_nonneg _)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, Lp.norm_fourier_eq] using hnorm

theorem highFrequency_norm_le_weak_derivative (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x)
    (R : ℝ) (hR : 0 < R) :
    ‖highFrequency (Icc (-R) R) measurableSet_Icc f‖ ≤ ‖df‖ / (2 * Real.pi * R) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi * R)).mpr
  simpa only [mul_comm] using highFrequency_scaled_norm_le_weak_derivative f df hweak R hR.le

theorem highFrequency_energy_le_weak_derivative (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x)
    (R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi * R) ^ 2 * ‖highFrequency (Icc (-R) R) measurableSet_Icc f‖ ^ 2 ≤ ‖df‖ ^ 2 := by
  have h := pow_le_pow_left₀ (by positivity)
    (highFrequency_scaled_norm_le_weak_derivative f df hweak R hR) 2
  simpa only [mul_pow] using h

theorem toLp_highFrequency_norm_le_derivative {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hu2 : MemLp u 2 volume) (hd2 : MemLp du 2 volume)
    (R : ℝ) (hR : 0 < R) :
    ‖highFrequency (Icc (-R) R) measurableSet_Icc (hu2.toLp u)‖ ≤
      ‖hd2.toLp du‖ / (2 * Real.pi * R) :=
  highFrequency_norm_le_weak_derivative (hu2.toLp u) (hd2.toLp du)
    (toLp_derivative_pairing hu hu2 hd2) R hR

end TransposeFollowup
