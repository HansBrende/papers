import TransposeFollowup.MobiusTransportMoments
import TransposeFollowup.SchwartzSpatialMoments
import TransposeFollowup.ComplexifiedL2Operator

/-! The polynomial differential expression preserves Schwartz space, so
the weighted pullback has a square-integrable classical derivative almost
everywhere, with an explicit four-moment bound. A weak-derivative or Fourier
derivative theorem still requires justification across the possible pole. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory
open scoped SchwartzMap
set_option autoImplicit false

noncomputable def schwartzDifferentialTransport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) : 𝓢(ℝ, E) :=
  SchwartzMap.smulLeftCLM E (fun y : ℝ => (g 0 0 - g 1 0 * y) ^ 2)
    (SchwartzMap.derivCLM ℝ E u) -
  SchwartzMap.smulLeftCLM E (fun y : ℝ => g 1 0 * (g 0 0 - g 1 0 * y)) u

theorem schwartzDifferentialTransport_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) (y : ℝ) :
    schwartzDifferentialTransport g u y = differentialTransport g u (deriv u) y := by
  rw [differentialTransport_explicit]
  have h2 : (fun y : ℝ => (g 0 0 - g 1 0 * y) ^ 2).HasTemperateGrowth := by fun_prop
  have h1 : (fun y : ℝ => g 1 0 * (g 0 0 - g 1 0 * y)).HasTemperateGrowth := by fun_prop
  change (SchwartzMap.smulLeftCLM E _ (SchwartzMap.derivCLM ℝ E u)) y -
    (SchwartzMap.smulLeftCLM E _ u) y = _
  rw [SchwartzMap.smulLeftCLM_apply_apply h2, SchwartzMap.smulLeftCLM_apply_apply h1,
    SchwartzMap.derivCLM_apply]

theorem schwartz_differentialTransport_integrable_norm_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    Integrable (fun y => ‖differentialTransport g u (deriv u) y‖ ^ 2) := by
  simpa only [schwartzDifferentialTransport_apply] using
    schwartz_integrable_norm_sq (schwartzDifferentialTransport g u)

theorem schwartz_scaledPullback_deriv_integrable_norm_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    Integrable (fun x => ‖deriv (scaledPullback g u) x‖ ^ 2) :=
  (integrable_deriv_scaledPullback_norm_sq_iff g u.hasDerivAt).mpr
    (schwartz_differentialTransport_integrable_norm_sq g u)

theorem schwartz_scaledPullback_deriv_energy {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    (∫ x, ‖deriv (scaledPullback g u) x‖ ^ 2) =
      ∫ y, ‖(g 0 0 - g 1 0 * y) ^ 2 • deriv u y -
        (g 1 0 * (g 0 0 - g 1 0 * y)) • u y‖ ^ 2 := by
  rw [integral_deriv_scaledPullback_norm_sq g u.hasDerivAt]
  simp only [differentialTransport_explicit]

theorem schwartz_scaledPullback_deriv_energy_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Group) (u : 𝓢(ℝ, E)) :
    (∫ x, ‖deriv (scaledPullback g u) x‖ ^ 2) ≤
      (16 * (g 0 0) ^ 4) * (∫ y, ‖deriv u y‖ ^ 2) +
      (16 * (g 1 0) ^ 4) * (∫ y, y ^ 4 * ‖deriv u y‖ ^ 2) +
      (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∫ y, ‖u y‖ ^ 2) +
      (4 * (g 1 0) ^ 4) * (∫ y, y ^ 2 * ‖u y‖ ^ 2) := by
  rw [integral_deriv_scaledPullback_norm_sq g u.hasDerivAt]
  apply integral_differentialTransport_norm_sq_le g u (deriv u)
    (schwartz_differentialTransport_integrable_norm_sq g u)
  · simpa using schwartz_integrable_deriv_even_moment u 0
  · simpa using schwartz_integrable_deriv_even_moment u 2
  · exact schwartz_integrable_norm_sq u
  · simpa using schwartz_integrable_even_moment u 1

theorem complexify_inverse_action_coe (g : Group) (f : ComplexL2) :
    ⇑(complexifyL2 (actionCLM g⁻¹) f) =ᵐ[volume] scaledPullback g f := by
  filter_upwards [complexify_action_coe g⁻¹ f] with x hx
  change complexifyL2 (actionCLM g⁻¹) f x = (|denom g x|⁻¹ : ℝ) • f (eval g x)
  simpa only [inv_inv] using hx

end TransposeFollowup.RealMobius
