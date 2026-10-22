import TransposeFollowup.MobiusSchwartzL2Derivative

/-! High-frequency energy of the actual Mobius action is controlled by
the spatial moments exposed by the exact derivative formula. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem schwartzActionL2_fourier_iterated_derivative (g : Group) (u : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ⇑(𝓕 (schwartzActionL2 g ((schwartzDifferentialTransport g)^[n] u)) : ComplexL2) =ᵐ[volume]
      (fun ξ => (2 * Real.pi * Complex.I * ξ) ^ n * (𝓕 (schwartzActionL2 g u)) ξ) := by
  induction n with
  | zero => filter_upwards [] with ξ; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    filter_upwards [schwartzActionL2_fourier_derivative g ((schwartzDifferentialTransport g)^[n] u),
      ih] with ξ hd hi
    rw [hd, hi, pow_succ']
    ring

theorem schwartzActionL2_highFrequency_energy_le (g : Group) (u : 𝓢(ℝ, ℂ))
    (R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi * R) ^ 2 *
      ‖highFrequency (Icc (-R) R) measurableSet_Icc (schwartzActionL2 g u)‖ ^ 2 ≤
      ∫ y, ‖schwartzDifferentialTransport g u y‖ ^ 2 := by
  have h := highFrequency_energy_le_weak_derivative _ _ (schwartzActionL2_derivative_pairing g u) R hR
  rwa [schwartzActionL2_norm_sq] at h

theorem schwartzActionL2_highFrequency_four_moments (g : Group) (u : 𝓢(ℝ, ℂ))
    (R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi * R) ^ 2 *
      ‖highFrequency (Icc (-R) R) measurableSet_Icc (schwartzActionL2 g u)‖ ^ 2 ≤
      (16 * (g 0 0) ^ 4) * (∫ y, ‖deriv u y‖ ^ 2) +
      (16 * (g 1 0) ^ 4) * (∫ y, y ^ 4 * ‖deriv u y‖ ^ 2) +
      (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∫ y, ‖u y‖ ^ 2) +
      (4 * (g 1 0) ^ 4) * (∫ y, y ^ 2 * ‖u y‖ ^ 2) := by
  apply (schwartzActionL2_highFrequency_energy_le g u R hR).trans
  have h := schwartz_scaledPullback_deriv_energy_le g u
  rw [integral_deriv_scaledPullback_norm_sq g u.hasDerivAt] at h
  simpa only [schwartzDifferentialTransport_apply] using h

end TransposeFollowup.RealMobius
