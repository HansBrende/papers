import TransposeFollowup.L2WaveletEstimate
import TransposeFollowup.ComplexMobiusComposition

/-! The affine wavelets are exactly the positive upper-triangular
restriction of the existing representation T_g = W_(g⁻¹). -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory SchwartzMap
set_option autoImplicit false

noncomputable def affineWaveletMatrix (s : ℝ) (hs : 0 < s) (t : ℝ) : Group :=
  ⟨!![Real.sqrt s, t / Real.sqrt s; 0, (Real.sqrt s)⁻¹], by
    simp [Matrix.det_fin_two, (Real.sqrt_pos.mpr hs).ne']⟩

theorem affineWaveletMatrix_inverse_denom (s : ℝ) (hs : 0 < s) (t x : ℝ) :
    denom (affineWaveletMatrix s hs t)⁻¹ x = Real.sqrt s := by
  rw [denom_inverse]
  simp [affineWaveletMatrix]

theorem affineWaveletMatrix_inverse_eval (s : ℝ) (hs : 0 < s) (t x : ℝ) :
    eval (affineWaveletMatrix s hs t)⁻¹ x = s⁻¹ * (x - t) := by
  rw [eval, affineWaveletMatrix_inverse_denom, num_inverse]
  change ((Real.sqrt s)⁻¹ * x - t / Real.sqrt s) / Real.sqrt s = _
  calc
    _ = (Real.sqrt s * Real.sqrt s)⁻¹ * (x - t) := by
      field_simp
    _ = _ := by rw [Real.mul_self_sqrt hs.le]

theorem scaledPullback_affineWavelet (u : ℝ → ℂ) (s : ℝ) (hs : 0 < s) (t x : ℝ) :
    scaledPullback (affineWaveletMatrix s hs t)⁻¹ u x =
      (Real.sqrt s)⁻¹ • u (s⁻¹ * (x - t)) := by
  rw [scaledPullback, affineWaveletMatrix_inverse_denom, affineWaveletMatrix_inverse_eval,
    abs_of_pos (Real.sqrt_pos.mpr hs)]

theorem complexPullbackL2_affineWavelet (u : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    complexPullbackL2 (affineWaveletMatrix s hs t)⁻¹ (u.toLp 2 volume) =
      ((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).toLp 2 volume := by
  rw [complexPullbackL2_schwartz]
  apply Lp.ext
  filter_upwards [schwartzActionL2_coe (affineWaveletMatrix s hs t)⁻¹ u,
    ((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).coeFn_toLp 2 volume] with x hx hy
  rw [hx, hy, scaledPullback_affineWavelet]
  rfl

theorem l2WaveletCoefficient_eq_group_action (u : 𝓢(ℝ, ℂ)) (v : ComplexL2)
    (s : ℝ) (hs : 0 < s) (t : ℝ) :
    l2WaveletCoefficient u v s t =
      inner ℂ v (complexPullbackL2 (affineWaveletMatrix s hs t)⁻¹ (u.toLp 2 volume)) := by
  rw [l2WaveletCoefficient_pos u v hs, complexPullbackL2_affineWavelet]

theorem schwartzUnitaryScale_translate_norm (u : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    ‖((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).toLp 2 volume‖ =
      ‖u.toLp 2 volume‖ := by
  rw [← complexPullbackL2_affineWavelet, complexPullbackL2_norm]

end TransposeFollowup.RealMobius
