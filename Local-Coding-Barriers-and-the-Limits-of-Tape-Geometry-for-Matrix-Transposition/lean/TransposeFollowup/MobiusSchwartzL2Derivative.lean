import TransposeFollowup.MobiusSchwartzRegularity
import TransposeFollowup.L2DerivativeFrequencyTail

/-! The global Schwartz-input calculus supplies a weak derivative for the
same actual complexified L2 action used in the spectral-gap reduction. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem scaledPullback_ae_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Group) {f h : ℝ → E} (heq : f =ᵐ[volume] h) :
    scaledPullback g f =ᵐ[volume] scaledPullback g h := by
  have hd : (fun x => ‖f x - h x‖ ^ 2) =ᵐ[volume] (fun _ => (0 : ℝ)) :=
    heq.mono (fun _ hx => by simp only [hx, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)])
  have hi : Integrable (fun x => ‖f x - h x‖ ^ 2) := (integrable_zero ℝ ℝ volume).congr hd.symm
  have hw := (scaledPullback_integrable_norm_sq_iff g (fun x => f x - h x)).mpr hi
  have hz : (∫ x, ‖scaledPullback g (fun y => f y - h y) x‖ ^ 2) = 0 := by
    rw [scaledPullback_integral_norm_sq]
    exact (integral_congr_ae hd).trans (by simp)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hw).mp hz
  filter_upwards [hae] with x hx
  have hx' := norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  change |denom g x|⁻¹ • (f (eval g x) - h (eval g x)) = 0 at hx'
  rw [smul_sub] at hx'
  exact sub_eq_zero.mp hx'

noncomputable def schwartzActionL2 (g : Group) (u : 𝓢(ℝ, ℂ)) : ComplexL2 :=
  complexifyL2 (actionCLM g⁻¹) (u.toLp 2 volume)

theorem schwartzActionL2_coe (g : Group) (u : 𝓢(ℝ, ℂ)) :
    ⇑(schwartzActionL2 g u) =ᵐ[volume] scaledPullback g u :=
  (complexify_inverse_action_coe g (u.toLp 2 volume)).trans
    (scaledPullback_ae_congr g (u.coeFn_toLp 2 volume))

theorem schwartzActionL2_norm_sq (g : Group) (u : 𝓢(ℝ, ℂ)) :
    ‖schwartzActionL2 g u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  rw [complexL2_norm_sq]
  calc
    _ = ∫ x, ‖scaledPullback g u x‖ ^ 2 :=
      integral_congr_ae ((schwartzActionL2_coe g u).mono (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))
    _ = _ := scaledPullback_integral_norm_sq g u

theorem schwartzActionL2_derivative_pairing (g : Group) (u φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * schwartzActionL2 g (schwartzDifferentialTransport g u) x) =
      -∫ x, deriv φ x * schwartzActionL2 g u x := by
  have hf := schwartzActionL2_coe g u
  have hd := schwartzActionL2_coe g (schwartzDifferentialTransport g u)
  have hf2 : MemLp (scaledPullback g u) 2 volume := (memLp_congr_ae hf).mp (Lp.memLp _)
  have hd2 : MemLp (scaledPullback g (schwartzDifferentialTransport g u)) 2 volume :=
    (memLp_congr_ae hd).mp (Lp.memLp _)
  have hderiv : ∀ x, HasDerivAt (scaledPullback g u)
      (scaledPullback g (schwartzDifferentialTransport g u) x) x := by
    intro x
    have h := (schwartz_scaledPullback_differentiable g u x).hasDerivAt
    rw [schwartz_scaledPullback_deriv] at h
    exact h
  calc
    _ = ∫ x, φ x * scaledPullback g (schwartzDifferentialTransport g u) x :=
      integral_congr_ae (hd.mono (fun x hx => congrArg (fun z => φ x * z) hx))
    _ = -∫ x, deriv φ x * scaledPullback g u x :=
      schwartz_L2_integration_by_parts hderiv hf2 hd2 φ
    _ = _ := congrArg Neg.neg (integral_congr_ae
      (hf.symm.mono (fun x hx => congrArg (fun z => deriv φ x * z) hx)))

theorem schwartzActionL2_fourier_derivative (g : Group) (u : 𝓢(ℝ, ℂ)) :
    ⇑(𝓕 (schwartzActionL2 g (schwartzDifferentialTransport g u)) : ComplexL2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I * ξ) * (𝓕 (schwartzActionL2 g u)) ξ) :=
  L2_fourier_weak_derivative_ae _ _ (schwartzActionL2_derivative_pairing g u)

theorem schwartzActionL2_fourier_derivative_energy (g : Group) (u : 𝓢(ℝ, ℂ)) :
    (∫ ξ, (2 * Real.pi * ξ) ^ 2 * ‖(𝓕 (schwartzActionL2 g u)) ξ‖ ^ 2) =
      ∫ y, ‖schwartzDifferentialTransport g u y‖ ^ 2 := by
  rw [L2_fourier_weak_derivative_energy _ _ (schwartzActionL2_derivative_pairing g u),
    schwartzActionL2_norm_sq]

end TransposeFollowup.RealMobius
