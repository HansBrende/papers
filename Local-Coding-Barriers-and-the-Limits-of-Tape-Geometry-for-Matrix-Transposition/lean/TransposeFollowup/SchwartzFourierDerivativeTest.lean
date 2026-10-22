import TransposeFollowup.FourierL2Bridge

/-! The frequency multiplier 2*pi*i*xi on Schwartz tests, with the
derivative-of-Fourier identity needed for weak L2 differentiation. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

noncomputable def schwartzFrequencyDerivative (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (2 * (Real.pi : ℂ) * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) φ

theorem schwartzFrequencyDerivative_apply (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzFrequencyDerivative φ x = (2 * Real.pi * Complex.I * x) * φ x := by
  change (2 * (Real.pi : ℂ) * Complex.I) •
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) φ) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

theorem schwartz_fourier_deriv_test (φ : 𝓢(ℝ, ℂ)) :
    deriv (⇑(𝓕 φ : 𝓢(ℝ, ℂ))) = fun x => -(𝓕 (schwartzFrequencyDerivative φ)) x := by
  have hmoment : Integrable (fun x : ℝ => x • φ x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply (g := fun x : ℝ => x) (by fun_prop)]
      using (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) φ).integrable
  rw [SchwartzMap.fourier_coe, Real.deriv_fourier φ.integrable hmoment]
  have heq : (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • φ x) =
      (fun x => -(schwartzFrequencyDerivative φ x)) := by
    funext x
    rw [schwartzFrequencyDerivative_apply]
    simp only [smul_eq_mul]
    ring
  rw [heq]
  funext x
  change (𝓕 (-schwartzFrequencyDerivative φ) : 𝓢(ℝ, ℂ)) x = _
  rw [FourierTransform.fourier_neg]
  rfl

end TransposeFollowup
