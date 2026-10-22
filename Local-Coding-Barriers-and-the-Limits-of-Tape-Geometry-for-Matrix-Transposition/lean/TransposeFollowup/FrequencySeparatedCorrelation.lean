import TransposeFollowup.MobiusSchwartzFrequencyTail

/-! Frequency separation removes the low component from a correlation.
Together with the weak-derivative tail bound this supplies a concrete
off-diagonal estimate, with the derivative norm kept explicit. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem complexL2_real_inner_fourier (f h : ComplexL2) :
    inner ℝ (𝓕 f : ComplexL2) (𝓕 h : ComplexL2) = inner ℝ f h := by
  have hsum := norm_add_sq_real (𝓕 f : ComplexL2) (𝓕 h : ComplexL2)
  rw [← FourierTransform.fourier_add] at hsum
  simp only [Lp.norm_fourier_eq] at hsum
  nlinarith [norm_add_sq_real f h]

theorem lowFrequency_real_inner_eq_zero (s : Set ℝ) (hs : MeasurableSet s) (f h : ComplexL2)
    (hh : ∀ᵐ ξ ∂volume, ξ ∈ s → (𝓕 h : ComplexL2) ξ = 0) :
    inner ℝ (lowFrequency s hs f) h = 0 := by
  rw [← complexL2_real_inner_fourier (lowFrequency s hs f) h, lowFrequency_fourier, L2.inner_def]
  calc
    _ = ∫ _ : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [frequencyCut_coe s hs f, hh] with ξ hc hz
      rw [hc]
      by_cases hmem : ξ ∈ s
      · simp [hmem, hz hmem]
      · simp [hmem]
    _ = _ := by simp

theorem real_inner_eq_highFrequency (s : Set ℝ) (hs : MeasurableSet s) (f h : ComplexL2)
    (hh : ∀ᵐ ξ ∂volume, ξ ∈ s → (𝓕 h : ComplexL2) ξ = 0) :
    inner ℝ f h = inner ℝ (highFrequency s hs f) h := by
  rw [highFrequency, inner_sub_left, lowFrequency_real_inner_eq_zero s hs f h hh, sub_zero]

theorem abs_real_inner_le_highFrequency (s : Set ℝ) (hs : MeasurableSet s) (f h : ComplexL2)
    (hh : ∀ᵐ ξ ∂volume, ξ ∈ s → (𝓕 h : ComplexL2) ξ = 0) :
    |inner ℝ f h| ≤ ‖highFrequency s hs f‖ * ‖h‖ := by
  rw [real_inner_eq_highFrequency s hs f h hh]
  exact abs_real_inner_le_norm _ _

theorem separated_correlation_le_weak_derivative (f df h : ComplexL2)
    (hweak : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * df x) = -∫ x, deriv φ x * f x)
    (R : ℝ) (hR : 0 < R)
    (hh : ∀ᵐ ξ ∂volume, ξ ∈ Icc (-R) R → (𝓕 h : ComplexL2) ξ = 0) :
    |inner ℝ f h| ≤ (‖df‖ / (2 * Real.pi * R)) * ‖h‖ :=
  (abs_real_inner_le_highFrequency (Icc (-R) R) measurableSet_Icc f h hh).trans
    (mul_le_mul_of_nonneg_right (highFrequency_norm_le_weak_derivative f df hweak R hR)
      (norm_nonneg h))

namespace RealMobius

theorem schwartzActionL2_norm (g : Group) (u : 𝓢(ℝ, ℂ)) :
    ‖schwartzActionL2 g u‖ = ‖u.toLp 2 volume‖ := by
  have hs : ‖schwartzActionL2 g u‖ ^ 2 = ‖u.toLp 2 volume‖ ^ 2 := by
    rw [schwartzActionL2_norm_sq, complexL2_norm_sq]
    exact integral_congr_ae ((u.coeFn_toLp 2 volume).symm.mono
      (fun _ hx => congrArg (fun z => ‖z‖ ^ 2) hx))
  nlinarith [norm_nonneg (schwartzActionL2 g u), norm_nonneg (u.toLp 2 volume)]

theorem schwartzActionL2_separated_correlation (g : Group) (u : 𝓢(ℝ, ℂ)) (h : ComplexL2)
    (R : ℝ) (hR : 0 < R)
    (hh : ∀ᵐ ξ ∂volume, ξ ∈ Icc (-R) R → (𝓕 h : ComplexL2) ξ = 0) :
    |inner ℝ (schwartzActionL2 g u) h| ≤
      (‖(schwartzDifferentialTransport g u).toLp 2 volume‖ / (2 * Real.pi * R)) * ‖h‖ := by
  have he := separated_correlation_le_weak_derivative _ _ h
    (schwartzActionL2_derivative_pairing g u) R hR hh
  rwa [schwartzActionL2_norm] at he

end RealMobius
end TransposeFollowup
