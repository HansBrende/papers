import TransposeFollowup.SmoothBandDerivativeEnergy

/-! Uniform finite-family derivative-energy bounds. The constants depend
on pointwise square sums of the cutoffs and their first two derivatives,
not on the number of bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem finite_smoothBandSpectrum_deriv_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {B0 B1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖χ i ξ‖ ^ 2 ≤ B0)
    (h1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (χ i) ξ‖ ^ 2 ≤ B1) :
    (∑ i ∈ s, w i * ∫ ξ, ‖deriv (smoothBandSpectrum hf hs (χ i) (hc i)) ξ‖ ^ 2) ≤
      (2 * B0 * (2 * Real.pi) ^ 2 + 2 * B1) * ‖hf.toLp f‖ ^ 2 := by
  have hA := finite_multiplier_fourier_derivative_energy_le s χ w hf hs 1 hB0 h0
  have hB := finite_multiplier_fourier_derivative_energy_le s
    (fun i => SchwartzMap.derivCLM ℂ ℂ (χ i)) w hf hs 0 hB1 h1
  simp only [iteratedDeriv_one] at hA
  simp only [SchwartzMap.derivCLM_apply, iteratedDeriv_zero, Nat.mul_zero, pow_zero, one_mul] at hB
  calc
    _ ≤ ∑ i ∈ s, w i * (2 * (∫ ξ, ‖χ i ξ * deriv (𝓕 f) ξ‖ ^ 2) +
        2 * (∫ ξ, ‖deriv (χ i) ξ * 𝓕 f ξ‖ ^ 2)) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        (smoothBandSpectrum_deriv_energy_le hf hs (χ i) (hc i)) (hw i hi))
    _ = 2 * (∑ i ∈ s, w i * ∫ ξ, ‖χ i ξ * deriv (𝓕 f) ξ‖ ^ 2) +
        2 * (∑ i ∈ s, w i * ∫ ξ, ‖deriv (χ i) ξ * 𝓕 f ξ‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      convert add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 2)) using 1
      ring

theorem finite_smoothBandSpectrum_secondDeriv_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {B0 B1 B2 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖χ i ξ‖ ^ 2 ≤ B0)
    (h1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (χ i) ξ‖ ^ 2 ≤ B1)
    (h2 : ∀ ξ, ∑ i ∈ s, w i * ‖iteratedDeriv 2 (χ i) ξ‖ ^ 2 ≤ B2) :
    (∑ i ∈ s, w i * ∫ ξ, ‖iteratedDeriv 2 (smoothBandSpectrum hf hs (χ i) (hc i)) ξ‖ ^ 2) ≤
      (3 * B0 * (2 * Real.pi) ^ 4 + 12 * B1 * (2 * Real.pi) ^ 2 + 3 * B2) * ‖hf.toLp f‖ ^ 2 := by
  have hA := finite_multiplier_fourier_derivative_energy_le s χ w hf hs 2 hB0 h0
  have hB := finite_multiplier_fourier_derivative_energy_le s
    (fun i => SchwartzMap.derivCLM ℂ ℂ (χ i)) w hf hs 1 hB1 h1
  have hc2 : ∀ ξ, ∑ i ∈ s, w i *
      ‖(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (χ i))) ξ‖ ^ 2 ≤ B2 := by
    simpa only [schwartz_derivCLM_coe, SchwartzMap.derivCLM_apply, iteratedDeriv_succ, iteratedDeriv_zero] using h2
  have hC := finite_multiplier_fourier_derivative_energy_le s
    (fun i => SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (χ i))) w hf hs 0 hB2 hc2
  simp only [SchwartzMap.derivCLM_apply, iteratedDeriv_one] at hB
  have hC' : (∑ i ∈ s, w i * ∫ ξ, ‖iteratedDeriv 2 (χ i) ξ * 𝓕 f ξ‖ ^ 2) ≤
      B2 * ‖hf.toLp f‖ ^ 2 := by
    simpa only [schwartz_derivCLM_coe, SchwartzMap.derivCLM_apply, iteratedDeriv_succ, iteratedDeriv_zero,
      Nat.mul_zero, pow_zero, one_mul] using hC
  calc
    _ ≤ ∑ i ∈ s, w i * (3 * (∫ ξ, ‖χ i ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2) +
        12 * (∫ ξ, ‖deriv (χ i) ξ * deriv (𝓕 f) ξ‖ ^ 2) +
        3 * (∫ ξ, ‖iteratedDeriv 2 (χ i) ξ * 𝓕 f ξ‖ ^ 2)) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        (smoothBandSpectrum_secondDeriv_energy_le hf hs (χ i) (hc i)) (hw i hi))
    _ = 3 * (∑ i ∈ s, w i * ∫ ξ, ‖χ i ξ * iteratedDeriv 2 (𝓕 f) ξ‖ ^ 2) +
        12 * (∑ i ∈ s, w i * ∫ ξ, ‖deriv (χ i) ξ * deriv (𝓕 f) ξ‖ ^ 2) +
        3 * (∑ i ∈ s, w i * ∫ ξ, ‖iteratedDeriv 2 (χ i) ξ * 𝓕 f ξ‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      convert add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 3))
          (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 12)))
        (mul_le_mul_of_nonneg_left hC' (by norm_num : (0 : ℝ) ≤ 3)) using 1
      ring

end TransposeFollowup
