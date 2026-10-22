import TransposeFollowup.SchwartzFourierMoments
import TransposeFollowup.FiniteBandDerivativeEnergy

/-! Spatial moments of actual smooth bands, including their derivatives.
All support-dependent input estimates still concern the original input. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap FourierTransform
open scoped FourierTransform
set_option autoImplicit false

theorem schwartzFrequencyDerivative_hasCompactSupport (χ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport (⇑χ)) :
    HasCompactSupport (⇑(schwartzFrequencyDerivative χ)) := by
  have he : ⇑(schwartzFrequencyDerivative χ) =
      (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ)) * ⇑χ :=
    funext (schwartzFrequencyDerivative_apply χ)
  rw [he]
  exact hc.mul_left

theorem schwartzFrequencyDerivative_smoothBandSpectrum {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    schwartzFrequencyDerivative (smoothBandSpectrum hf hs χ hc) =
      smoothBandSpectrum hf hs (schwartzFrequencyDerivative χ)
        (schwartzFrequencyDerivative_hasCompactSupport χ hc) := by
  ext ξ
  simp only [schwartzFrequencyDerivative_apply, smoothBandSpectrum_apply]
  ring

theorem smoothBand_deriv {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) :
    SchwartzMap.derivCLM ℂ ℂ (smoothBand hf hs χ hc) =
      smoothBand hf hs (schwartzFrequencyDerivative χ)
        (schwartzFrequencyDerivative_hasCompactSupport χ hc) := by
  calc
    _ = 𝓕⁻ (𝓕 (SchwartzMap.derivCLM ℂ ℂ (smoothBand hf hs χ hc))) :=
      (fourierInv_fourier_eq _).symm
    _ = _ := by
      rw [schwartz_fourier_deriv, smoothBand_fourier,
        schwartzFrequencyDerivative_smoothBandSpectrum]
      rfl

theorem smoothBand_spatial_moment_energy {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (n : ℕ) :
    (∫ x, x ^ (2 * n) * ‖smoothBand hf hs χ hc x‖ ^ 2) =
      ((2 * Real.pi) ^ (2 * n))⁻¹ *
        ∫ ξ, ‖iteratedDeriv n (smoothBandSpectrum hf hs χ hc) ξ‖ ^ 2 := by
  rw [schwartz_spatial_moment_energy, smoothBand_fourier]

theorem smoothBand_deriv_spatial_moment_energy {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (n : ℕ) :
    (∫ x, x ^ (2 * n) * ‖deriv (smoothBand hf hs χ hc) x‖ ^ 2) =
      ((2 * Real.pi) ^ (2 * n))⁻¹ *
        ∫ ξ, ‖iteratedDeriv n (smoothBandSpectrum hf hs (schwartzFrequencyDerivative χ)
          (schwartzFrequencyDerivative_hasCompactSupport χ hc)) ξ‖ ^ 2 := by
  change (∫ x, x ^ (2 * n) *
    ‖(SchwartzMap.derivCLM ℂ ℂ (smoothBand hf hs χ hc)) x‖ ^ 2) = _
  rw [smoothBand_deriv]
  exact smoothBand_spatial_moment_energy hf hs _ _ n

theorem finite_smoothBand_first_moment_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {B0 B1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖χ i ξ‖ ^ 2 ≤ B0)
    (h1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (χ i) ξ‖ ^ 2 ≤ B1) :
    (∑ i ∈ s, w i * ∫ x, x ^ 2 * ‖smoothBand hf hs (χ i) (hc i) x‖ ^ 2) ≤
      (((2 * Real.pi) ^ 2)⁻¹ * (2 * B0 * (2 * Real.pi) ^ 2 + 2 * B1)) *
        ‖hf.toLp f‖ ^ 2 := by
  have he (i : ι) := smoothBand_spatial_moment_energy hf hs (χ i) (hc i) 1
  simp only [Nat.mul_one, iteratedDeriv_one] at he
  simp_rw [he, mul_left_comm (w _) (((2 * Real.pi) ^ 2)⁻¹)]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left
    (finite_smoothBandSpectrum_deriv_energy_le s χ hc w hw hf hs hB0 hB1 h0 h1)
    (by positivity)).trans_eq (by ring)

theorem finite_smoothBand_deriv_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) {Q0 : ℝ}
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖schwartzFrequencyDerivative (χ i) ξ‖ ^ 2 ≤ Q0) :
    (∑ i ∈ s, w i * ∫ x, ‖deriv (smoothBand hf hs (χ i) (hc i)) x‖ ^ 2) ≤
      Q0 * ‖hf.toLp f‖ ^ 2 := by
  have he (i : ι) : (∫ x, ‖deriv (smoothBand hf hs (χ i) (hc i)) x‖ ^ 2) =
      ‖(smoothBand hf hs (schwartzFrequencyDerivative (χ i))
        (schwartzFrequencyDerivative_hasCompactSupport (χ i) (hc i))).toLp 2 volume‖ ^ 2 := by
    rw [schwartz_toLp_norm_sq, ← smoothBand_deriv]
    rfl
  simp_rw [he]
  exact finite_smoothBand_energy_le s (fun i => schwartzFrequencyDerivative (χ i))
    (fun i => schwartzFrequencyDerivative_hasCompactSupport (χ i) (hc i)) w hf hs h0

theorem finite_smoothBand_deriv_second_moment_energy_le {ι : Type*} (s : Finset ι)
    (χ : ι → 𝓢(ℝ, ℂ)) (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    {Q0 Q1 Q2 : ℝ} (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2)
    (h0 : ∀ ξ, ∑ i ∈ s, w i * ‖schwartzFrequencyDerivative (χ i) ξ‖ ^ 2 ≤ Q0)
    (h1 : ∀ ξ, ∑ i ∈ s, w i * ‖deriv (schwartzFrequencyDerivative (χ i)) ξ‖ ^ 2 ≤ Q1)
    (h2 : ∀ ξ, ∑ i ∈ s, w i * ‖iteratedDeriv 2 (schwartzFrequencyDerivative (χ i)) ξ‖ ^ 2 ≤ Q2) :
    (∑ i ∈ s, w i * ∫ x, x ^ 4 * ‖deriv (smoothBand hf hs (χ i) (hc i)) x‖ ^ 2) ≤
      (((2 * Real.pi) ^ 4)⁻¹ *
        (3 * Q0 * (2 * Real.pi) ^ 4 + 12 * Q1 * (2 * Real.pi) ^ 2 + 3 * Q2)) *
        ‖hf.toLp f‖ ^ 2 := by
  have he (i : ι) := smoothBand_deriv_spatial_moment_energy hf hs (χ i) (hc i) 2
  simp only [show 2 * 2 = 4 from rfl] at he
  simp_rw [he, mul_left_comm (w _) (((2 * Real.pi) ^ 4)⁻¹)]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left
    (finite_smoothBandSpectrum_secondDeriv_energy_le s (fun i => schwartzFrequencyDerivative (χ i))
      (fun i => schwartzFrequencyDerivative_hasCompactSupport (χ i) (hc i))
      w hw hf hs hQ0 hQ1 hQ2 h0 h1 h2) (by positivity)).trans_eq (by ring)

end TransposeFollowup
