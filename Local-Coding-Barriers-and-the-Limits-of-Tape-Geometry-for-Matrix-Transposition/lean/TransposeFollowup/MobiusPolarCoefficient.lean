import TransposeFollowup.MobiusComplexInner
import TransposeFollowup.MobiusPolarHaar
import TransposeFollowup.PositiveAffineMeasure

/-! Affine energy in the same dilation/shear parameters as the Haar
formula, with arbitrary complex L2 test vectors, including rotations. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform ENNReal
set_option autoImplicit false

theorem l2_wavelet_dilation_shear_lintegral_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    {M : ℝ} (hM : 0 < M) (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 / a) *
      ∫⁻ b : ℝ, ENNReal.ofReal (‖l2WaveletCoefficient u v (a ^ 2) (a ^ 2 * b)‖ ^ 2)) ≤
        ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) := by
  rw [lintegral_affine_parameter_change
    (fun s t => ENNReal.ofReal (‖l2WaveletCoefficient u v s t‖ ^ 2))]
  have hm : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)) :=
    ((l2WaveletCoefficient_measurable u v).norm.pow_const 2 |>.div
      (measurable_fst.pow_const 2)).ennreal_ofReal
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t : ℝ,
        ENNReal.ofReal (‖l2WaveletCoefficient u v s t‖ ^ 2 / s ^ 2) := by
      apply lintegral_congr
      intro s
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ = ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)
        ∂(volume.restrict (Ioi 0)).prod volume := (lintegral_prod _ hm.aemeasurable).symm
    _ ≤ _ := l2_wavelet_lintegral_le u v hM hzero

namespace RealMobius

theorem polar_group_coefficient (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    {a : ℝ} (ha : 0 < a) (θ b : ℝ) :
    inner ℂ v (complexPullbackL2 (columnChart (polarColumn a θ, b))⁻¹ (u.toLp 2 volume)) =
      l2WaveletCoefficient u (complexPullbackL2 (rotationMatrix θ) v) (a ^ 2) (a ^ 2 * b) := by
  rw [columnChart_polar_factor ha, complexPullbackL2_product_coefficient,
    l2WaveletCoefficient_eq_group_action u _ _ (sq_pos_of_pos ha)]

theorem polar_group_coefficient_energy_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) (θ : ℝ)
    {M : ℝ} (hM : 0 < M) (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (2 / a) *
      ∫⁻ b : ℝ, ENNReal.ofReal
        (‖inner ℂ v (complexPullbackL2 (columnChart (polarColumn a θ, b))⁻¹ (u.toLp 2 volume))‖ ^ 2)) ≤
      ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) := by
  have he := l2_wavelet_dilation_shear_lintegral_le u (complexPullbackL2 (rotationMatrix θ) v) hM hzero
  rw [complexPullbackL2_norm] at he
  convert he using 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  congr 1
  apply lintegral_congr
  intro b
  rw [polar_group_coefficient u v ha]

end RealMobius
end TransposeFollowup
