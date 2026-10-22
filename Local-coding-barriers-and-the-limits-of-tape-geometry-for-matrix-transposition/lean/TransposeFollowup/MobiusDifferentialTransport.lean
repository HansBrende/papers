import TransposeFollowup.MobiusWeightDerivative

/-! The derivative of a weighted Mobius pullback is another weighted
pullback, now applied to a polynomially weighted differential expression.
The identity exposes the spatial moments needed in band localization. -/
namespace TransposeFollowup.RealMobius
open Classical Set MeasureTheory
set_option autoImplicit false

noncomputable def scaledPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u : ℝ → E) (x : ℝ) : E := |denom g x|⁻¹ • u (eval g x)

theorem scaledPullback_real (g : Group) (u : ℝ → ℝ) : scaledPullback g u = weightedPullback g u := rfl

noncomputable def differentialTransport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u du : ℝ → E) (y : ℝ) : E :=
  (denom g⁻¹ y) ^ 2 • du y - (g 1 0 * denom g⁻¹ y) • u y

theorem differentialTransport_explicit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u du : ℝ → E) (y : ℝ) :
    differentialTransport g u du y = (g 0 0 - g 1 0 * y) ^ 2 • du y -
      (g 1 0 * (g 0 0 - g 1 0 * y)) • u y := by
  simp only [differentialTransport, denom_inverse, neg_mul, sub_eq_add_neg, add_comm]

theorem hasDerivAt_scaledPullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {u : ℝ → E} {u' : E} {x : ℝ} (hx : x ∈ domain g)
    (hu : HasDerivAt u u' (eval g x)) :
    HasDerivAt (scaledPullback g u)
      (|denom g x|⁻¹ • (jacobian g x • u' - (g 1 0 / denom g x) • u (eval g x))) x := by
  have h := (hasDerivAt_inverse_abs_denom g hx).smul (hu.scomp x (hasDerivAt_eval g hx))
  convert h using 1
  · rfl
  · simp only [sub_eq_add_neg, smul_add, smul_neg, smul_smul, neg_mul, neg_smul,
      Function.comp_apply]
    rw [mul_comm (|denom g x|⁻¹) (g 1 0 / denom g x)]

theorem hasDerivAt_scaledPullback_transport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {u du : ℝ → E} {x : ℝ} (hx : x ∈ domain g)
    (hu : HasDerivAt u (du (eval g x)) (eval g x)) :
    HasDerivAt (scaledPullback g u) (scaledPullback g (differentialTransport g u du) x) x := by
  convert hasDerivAt_scaledPullback g hx hu using 1
  simp only [scaledPullback, differentialTransport, denom_inverse_eval g hx, jacobian,
    div_pow, one_pow, mul_one_div]

theorem deriv_scaledPullback_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {u du : ℝ → E} (hu : ∀ y, HasDerivAt u (du y) y) :
    deriv (scaledPullback g u) =ᵐ[volume] scaledPullback g (differentialTransport g u du) := by
  filter_upwards [ae_domain g] with x hx
  exact (hasDerivAt_scaledPullback_transport g hx (hu _)).deriv

theorem scaledPullback_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u : ℝ → E) (x : ℝ) :
    ‖scaledPullback g u x‖ ^ 2 = jacobian g x * ‖u (eval g x)‖ ^ 2 := by
  simp only [scaledPullback, norm_smul, Real.norm_eq_abs, abs_inv, abs_abs, mul_pow,
    inv_pow, sq_abs, jacobian, one_div]

theorem scaledPullback_integral_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u : ℝ → E) : (∫ x, ‖scaledPullback g u x‖ ^ 2) = ∫ y, ‖u y‖ ^ 2 := by
  simp_rw [scaledPullback_norm_sq]
  exact integral_jacobian g (fun y => ‖u y‖ ^ 2)

theorem scaledPullback_integrable_norm_sq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) (u : ℝ → E) :
    Integrable (fun x => ‖scaledPullback g u x‖ ^ 2) ↔ Integrable (fun y => ‖u y‖ ^ 2) := by
  simp_rw [scaledPullback_norm_sq]
  exact integrable_jacobian_iff g (fun y => ‖u y‖ ^ 2)

theorem integral_deriv_scaledPullback_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {u du : ℝ → E} (hu : ∀ y, HasDerivAt u (du y) y) :
    (∫ x, ‖deriv (scaledPullback g u) x‖ ^ 2) = ∫ y, ‖differentialTransport g u du y‖ ^ 2 := by
  calc
    _ = ∫ x, ‖scaledPullback g (differentialTransport g u du) x‖ ^ 2 :=
      integral_congr_ae ((deriv_scaledPullback_ae g hu).mono (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))
    _ = _ := scaledPullback_integral_norm_sq g _

theorem integrable_deriv_scaledPullback_norm_sq_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {u du : ℝ → E} (hu : ∀ y, HasDerivAt u (du y) y) :
    Integrable (fun x => ‖deriv (scaledPullback g u) x‖ ^ 2) ↔
      Integrable (fun y => ‖differentialTransport g u du y‖ ^ 2) := by
  rw [integrable_congr ((deriv_scaledPullback_ae g hu).mono (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))]
  exact scaledPullback_integrable_norm_sq_iff g _

end TransposeFollowup.RealMobius
