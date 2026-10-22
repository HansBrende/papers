import TransposeFollowup.FourierL2Bridge
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Integration by parts against Schwartz tests for a function and its
classical derivative in L2. No L1 hypothesis on the function is required. -/
namespace TransposeFollowup
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

theorem schwartz_L2_integration_by_parts {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hu2 : MemLp u 2 volume) (hd2 : MemLp du 2 volume)
    (φ : 𝓢(ℝ, ℂ)) : (∫ x, φ x * du x) = -∫ x, deriv φ x * u x := by
  have hφ := φ.memLp 2 volume
  have hdφ : MemLp (deriv φ) 2 volume := (SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => φ.hasDerivAt x) (fun x _ => hu x)
    (hφ.integrable_mul hd2) (hdφ.integrable_mul hu2) (hφ.integrable_mul hu2)

theorem toLp_derivative_pairing {u du : ℝ → ℂ}
    (hu : ∀ x, HasDerivAt u (du x) x) (hu2 : MemLp u 2 volume) (hd2 : MemLp du 2 volume)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * hd2.toLp du x) = -∫ x, deriv φ x * hu2.toLp u x := by
  have hleft : (∫ x, φ x * hd2.toLp du x) = ∫ x, φ x * du x :=
    integral_congr_ae (hd2.coeFn_toLp.mono (fun x hx => congrArg (fun z => φ x * z) hx))
  have hright : (∫ x, deriv φ x * hu2.toLp u x) = ∫ x, deriv φ x * u x :=
    integral_congr_ae (hu2.coeFn_toLp.mono (fun x hx => congrArg (fun z => deriv φ x * z) hx))
  rw [hleft, hright]
  exact schwartz_L2_integration_by_parts hu hu2 hd2 φ

end TransposeFollowup
