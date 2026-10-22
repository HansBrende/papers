import TransposeFollowup.DyadicL2Reconstruction

/-! Norm, frequency support and low-frequency comparison for the smooth
high-frequency component reconstructed by the dyadic bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem lowFrequencyCutoff_complement_norm_le (ξ : ℝ) : ‖1 - lowFrequencyCutoff ξ‖ ≤ 1 := by
  have h0 : 0 ≤ unitFrequencyBump ξ := unitFrequencyBump.nonneg
  have h1 : unitFrequencyBump ξ ≤ 1 := unitFrequencyBump.le_one
  have he : (1 : ℂ) - lowFrequencyCutoff ξ = ((1 - unitFrequencyBump ξ : ℝ) : ℂ) := by
    simp only [lowFrequencyCutoff_apply, Complex.ofReal_sub, Complex.ofReal_one]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem smoothHighFrequency_norm_le {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ‖smoothHighFrequency hf hs‖ ≤ ‖hf.toLp f‖ := by
  rw [← Lp.norm_fourier_eq (smoothHighFrequency hf hs), ← Lp.norm_fourier_eq (hf.toLp f)]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothHighFrequency_fourier_coe hf hs] with ξ hξ
  rw [hξ, norm_mul]
  exact (mul_le_mul_of_nonneg_right (lowFrequencyCutoff_complement_norm_le ξ)
    (norm_nonneg _)).trans_eq (one_mul _)

theorem smoothHighFrequency_fourier_zero_on {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ∀ᵐ ξ ∂volume, ξ ∈ Icc (-1 : ℝ) 1 → (𝓕 (smoothHighFrequency hf hs) : ComplexL2) ξ = 0 := by
  filter_upwards [smoothHighFrequency_fourier_coe hf hs] with ξ hξ hmem
  rw [hξ, lowFrequencyCutoff_eq_one (abs_le.mpr hmem), sub_self, zero_mul]

theorem smoothBand_norm_le_lowFrequency {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0)
    (χ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport (⇑χ)) (s : Set ℝ) (hsm : MeasurableSet s)
    (hχ : ∀ ξ, ‖χ ξ‖ ≤ 1) (hz : ∀ ξ, ξ ∉ s → χ ξ = 0) :
    ‖(smoothBand hf hs χ hc).toLp 2 volume‖ ≤ ‖lowFrequency s hsm (hf.toLp f)‖ := by
  rw [← Lp.norm_fourier_eq ((smoothBand hf hs χ hc).toLp 2 volume), lowFrequency_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothBand_toLp_fourier_coe hf hs χ hc, frequencyCut_coe s hsm (hf.toLp f)]
    with ξ hb hcut
  rw [hb, hcut]
  by_cases hmem : ξ ∈ s
  · rw [Set.indicator_of_mem hmem, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hχ ξ) (norm_nonneg _)).trans_eq (one_mul _)
  · simp [hmem, hz ξ hmem]

theorem smoothHighFrequency_distance_le_lowFrequency {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) :
    ‖hf.toLp f - smoothHighFrequency hf hs‖ ≤
      ‖lowFrequency (Icc (-2 : ℝ) 2) measurableSet_Icc (hf.toLp f)‖ := by
  rw [norm_sub_smoothHighFrequency]
  apply smoothBand_norm_le_lowFrequency hf hs lowFrequencyCutoff lowFrequencyCutoff_hasCompactSupport
    (Icc (-2 : ℝ) 2) measurableSet_Icc lowFrequencyCutoff_norm_le
  intro ξ hξ
  apply lowFrequencyCutoff_eq_zero
  have h : ¬ |ξ| ≤ 2 := fun h => hξ (abs_le.mp h)
  exact (lt_of_not_ge h).le

end TransposeFollowup
