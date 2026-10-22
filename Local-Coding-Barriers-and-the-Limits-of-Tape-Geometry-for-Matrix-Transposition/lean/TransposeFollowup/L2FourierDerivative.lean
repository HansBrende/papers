import TransposeFollowup.SchwartzL2Derivative
import TransposeFollowup.SchwartzFourierDerivativeTest
import TransposeFollowup.FrequencyCutoff

/-! Fourier differentiation for actual L2 classes whose weak derivative is
represented by another L2 class. Classical differentiation supplies this
weak identity without any L1 hypothesis, by Schwartz integration by parts. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ContDiff
set_option autoImplicit false

theorem L2_fourier_weak_derivative_pairing (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ ξ, φ ξ * (𝓕 df) ξ) = ∫ ξ, φ ξ * ((2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ) := by
  calc
    _ = ∫ x, (𝓕 φ) x * df x := L2_fourier_pairing df φ
    _ = -∫ x, deriv (⇑(𝓕 φ : 𝓢(ℝ, ℂ))) x * f x := hweak (𝓕 φ)
    _ = ∫ x, (𝓕 (schwartzFrequencyDerivative φ)) x * f x := by
      rw [schwartz_fourier_deriv_test]
      simp only [neg_mul, integral_neg, neg_neg]
    _ = ∫ ξ, schwartzFrequencyDerivative φ ξ * (𝓕 f) ξ :=
      (L2_fourier_pairing f (schwartzFrequencyDerivative φ)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [schwartzFrequencyDerivative_apply]
      ring

theorem L2_fourier_weak_derivative_ae (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x) :
    ⇑(𝓕 df : ComplexL2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ) := by
  have hloc := (Lp.memLp (𝓕 f : ComplexL2)).locallyIntegrable (by norm_num)
  have hwloc : LocallyIntegrable
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ) volume :=
    hloc.continuous_mul (by fun_prop)
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 df : ComplexL2)).locallyIntegrable (by norm_num)) hwloc
  intro g hg hc
  have hcomp : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hdiff : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : 𝓢(ℝ, ℂ) := hcomp.toSchwartzMap hdiff
  have he := L2_fourier_weak_derivative_pairing f df hweak φ
  have hφ : ∀ x, φ x = (g x : ℂ) := fun _ => rfl
  simp_rw [hφ] at he
  simpa only [Complex.real_smul] using he

theorem toLp_fourier_derivative_ae {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hu2 : MemLp u 2 volume) (hd2 : MemLp du 2 volume) :
    ⇑(𝓕 (hd2.toLp du) : ComplexL2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I * ξ) * (𝓕 (hu2.toLp u)) ξ) :=
  L2_fourier_weak_derivative_ae (hu2.toLp u) (hd2.toLp du) (toLp_derivative_pairing hu hu2 hd2)

theorem frequency_derivative_symbol_norm_sq (ξ : ℝ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * ξ)‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 := by
  have he : (2 * (Real.pi : ℂ) * Complex.I * ξ) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, sq_abs]

theorem frequency_derivative_symbol_norm (ξ : ℝ) :
    ‖(2 * (Real.pi : ℂ) * Complex.I * ξ)‖ = 2 * Real.pi * |ξ| := by
  have he : (2 * (Real.pi : ℂ) * Complex.I * ξ) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)]

theorem L2_fourier_weak_derivative_energy (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x) :
    (∫ ξ, (2 * Real.pi * ξ) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) = ‖df‖ ^ 2 := by
  calc
    _ = ∫ ξ, ‖(𝓕 df : ComplexL2) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [L2_fourier_weak_derivative_ae f df hweak] with ξ hξ
      rw [hξ, norm_mul]
      conv_rhs => rw [mul_pow, frequency_derivative_symbol_norm_sq]
    _ = ‖(𝓕 df : ComplexL2)‖ ^ 2 := (complexL2_norm_sq _).symm
    _ = _ := by rw [Lp.norm_fourier_eq]

theorem L2_fourier_weak_derivative_integrable (f df : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x) :
    Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
  apply ((Lp.memLp (𝓕 df : ComplexL2)).integrable_norm_pow (by decide : 2 ≠ 0)).congr
  filter_upwards [L2_fourier_weak_derivative_ae f df hweak] with ξ hξ
  rw [hξ, norm_mul, mul_pow, frequency_derivative_symbol_norm_sq]

end TransposeFollowup
