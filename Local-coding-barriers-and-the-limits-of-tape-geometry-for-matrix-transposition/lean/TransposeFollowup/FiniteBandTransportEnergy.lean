import TransposeFollowup.SmoothBandSpatialMoments
import TransposeFollowup.MobiusSchwartzFrequencyTail

/-! The finite-family transported derivative bound. The hypotheses are
pointwise weighted square sums for chi, chi', q, q', q'', where q=2*pi*i*xi*chi.
No family-size factor and no bandwise relative moment bound are assumed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem schwartzDifferentialTransport_energy_le (g : Group) (u : 𝓢(ℝ, ℂ)) :
    ‖(schwartzDifferentialTransport g u).toLp 2 volume‖ ^ 2 ≤
      (16 * (g 0 0) ^ 4) * (∫ y, ‖deriv u y‖ ^ 2) +
      (16 * (g 1 0) ^ 4) * (∫ y, y ^ 4 * ‖deriv u y‖ ^ 2) +
      (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∫ y, ‖u y‖ ^ 2) +
      (4 * (g 1 0) ^ 4) * (∫ y, y ^ 2 * ‖u y‖ ^ 2) := by
  rw [schwartz_toLp_norm_sq]
  have h := schwartz_scaledPullback_deriv_energy_le g u
  rw [integral_deriv_scaledPullback_norm_sq g u.hasDerivAt] at h
  simpa only [schwartzDifferentialTransport_apply] using h

theorem finite_schwartzDifferentialTransport_energy_le {ι : Type*} (s : Finset ι)
    (u : ι → 𝓢(ℝ, ℂ)) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (g : Group) {A0 A4 U0 U2 : ℝ}
    (hA0 : (∑ i ∈ s, w i * ∫ x, ‖deriv (u i) x‖ ^ 2) ≤ A0)
    (hA4 : (∑ i ∈ s, w i * ∫ x, x ^ 4 * ‖deriv (u i) x‖ ^ 2) ≤ A4)
    (hU0 : (∑ i ∈ s, w i * ∫ x, ‖u i x‖ ^ 2) ≤ U0)
    (hU2 : (∑ i ∈ s, w i * ∫ x, x ^ 2 * ‖u i x‖ ^ 2) ≤ U2) :
    (∑ i ∈ s, w i * ‖(schwartzDifferentialTransport g (u i)).toLp 2 volume‖ ^ 2) ≤
      16 * (g 0 0) ^ 4 * A0 + 16 * (g 1 0) ^ 4 * A4 +
      4 * (g 1 0) ^ 2 * (g 0 0) ^ 2 * U0 + 4 * (g 1 0) ^ 4 * U2 := by
  calc
    _ ≤ ∑ i ∈ s, w i *
        ((16 * (g 0 0) ^ 4) * (∫ x, ‖deriv (u i) x‖ ^ 2) +
          (16 * (g 1 0) ^ 4) * (∫ x, x ^ 4 * ‖deriv (u i) x‖ ^ 2) +
          (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∫ x, ‖u i x‖ ^ 2) +
          (4 * (g 1 0) ^ 4) * (∫ x, x ^ 2 * ‖u i x‖ ^ 2)) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        (schwartzDifferentialTransport_energy_le g (u i)) (hw i hi))
    _ = (16 * (g 0 0) ^ 4) * (∑ i ∈ s, w i * ∫ x, ‖deriv (u i) x‖ ^ 2) +
        (16 * (g 1 0) ^ 4) * (∑ i ∈ s, w i * ∫ x, x ^ 4 * ‖deriv (u i) x‖ ^ 2) +
        (4 * (g 1 0) ^ 2 * (g 0 0) ^ 2) * (∑ i ∈ s, w i * ∫ x, ‖u i x‖ ^ 2) +
        (4 * (g 1 0) ^ 4) * (∑ i ∈ s, w i * ∫ x, x ^ 2 * ‖u i x‖ ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hA0 (by positivity))
        (mul_le_mul_of_nonneg_left hA4 (by positivity)))
      (mul_le_mul_of_nonneg_left hU0 (by positivity)))
      (mul_le_mul_of_nonneg_left hU2 (by positivity))

theorem finite_smoothBand_transport_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group)
    {B0 B1 Q0 Q1 Q2 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2)
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖χ i ξ‖ ^ 2 ≤ B0)
    (h1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (χ i) ξ‖ ^ 2 ≤ B1)
    (hq0 : ∀ ξ, ∑ i ∈ s, w i * ‖schwartzFrequencyDerivative (χ i) ξ‖ ^ 2 ≤ Q0)
    (hq1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (schwartzFrequencyDerivative (χ i)) ξ‖ ^ 2 ≤ Q1)
    (hq2 : ∀ ξ, ∑ i ∈ s, w i * ‖iteratedDeriv 2 (schwartzFrequencyDerivative (χ i)) ξ‖ ^ 2 ≤ Q2) :
    (∑ i ∈ s, w i *
      ‖(schwartzDifferentialTransport g (smoothBand hf hs (χ i) (hc i))).toLp 2 volume‖ ^ 2) ≤
      (16 * (g 0 0) ^ 4 * Q0 +
        16 * (g 1 0) ^ 4 * (((2 * Real.pi) ^ 4)⁻¹ *
          (3 * Q0 * (2 * Real.pi) ^ 4 + 12 * Q1 * (2 * Real.pi) ^ 2 + 3 * Q2)) +
        4 * (g 1 0) ^ 2 * (g 0 0) ^ 2 * B0 +
        4 * (g 1 0) ^ 4 * (((2 * Real.pi) ^ 2)⁻¹ *
          (2 * B0 * (2 * Real.pi) ^ 2 + 2 * B1))) * ‖hf.toLp f‖ ^ 2 := by
  have hU0 := finite_smoothBand_energy_le s χ hc w hf hs h0
  simp only [schwartz_toLp_norm_sq] at hU0
  have h := finite_schwartzDifferentialTransport_energy_le s
    (fun i => smoothBand hf hs (χ i) (hc i)) w hw g
    (finite_smoothBand_deriv_energy_le s χ hc w hf hs hq0)
    (finite_smoothBand_deriv_second_moment_energy_le s χ hc w hw hf hs hQ0 hQ1 hQ2 hq0 hq1 hq2)
    hU0 (finite_smoothBand_first_moment_energy_le s χ hc w hw hf hs hB0 hB1 h0 h1)
  convert h using 1
  ring

theorem finite_schwartzActionL2_highFrequency_energy_le {ι : Type*} (s : Finset ι)
    (u : ι → 𝓢(ℝ, ℂ)) (w R : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hR : ∀ i ∈ s, 0 ≤ R i) (g : Group) :
    (∑ i ∈ s, w i * ((2 * Real.pi * R i) ^ 2 *
      ‖highFrequency (Icc (-R i) (R i)) measurableSet_Icc (schwartzActionL2 g (u i))‖ ^ 2)) ≤
      ∑ i ∈ s, w i * ‖(schwartzDifferentialTransport g (u i)).toLp 2 volume‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i hi)
  rw [schwartz_toLp_norm_sq]
  exact schwartzActionL2_highFrequency_energy_le g (u i) (R i) (hR i hi)

end TransposeFollowup.RealMobius
