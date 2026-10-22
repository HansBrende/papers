import TransposeFollowup.SmoothFrequencyBand

/-! A pointwise square-sum bound on multipliers gives a uniform bound on
the sum of their L2 energies, independent of the number of bands. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem schwartz_multiplier_energy_integrable (ψ : 𝓢(ℝ, ℂ)) {F : ℝ → ℂ}
    (hF : MemLp F 2 volume) : Integrable (fun ξ => ‖ψ ξ * F ξ‖ ^ 2) := by
  have h : MemLp (fun ξ => ψ ξ * F ξ) 2 volume := (ψ.memLp ⊤ volume).mul hF
  exact h.integrable_norm_pow (by decide : 2 ≠ 0)

theorem finite_multiplier_energy_le {ι : Type*} (s : Finset ι) (ψ : ι → 𝓢(ℝ, ℂ))
    (w : ι → ℝ) {F : ℝ → ℂ} (hF : MemLp F 2 volume) {B : ℝ}
    (hB : ∀ ξ, ∑ i ∈ s, w i * ‖ψ i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ s, w i * ∫ ξ, ‖ψ i ξ * F ξ‖ ^ 2) ≤ B * ∫ ξ, ‖F ξ‖ ^ 2 := by
  have hi (i : ι) : Integrable (fun ξ => w i * ‖ψ i ξ * F ξ‖ ^ 2) :=
    (schwartz_multiplier_energy_integrable (ψ i) hF).const_mul (w i)
  calc
    _ = ∫ ξ, ∑ i ∈ s, w i * ‖ψ i ξ * F ξ‖ ^ 2 := by
      rw [integral_finsetSum s (fun i _ => hi i)]
      simp only [integral_const_mul]
    _ ≤ ∫ ξ, B * ‖F ξ‖ ^ 2 := by
      apply integral_mono (integrable_finsetSum s (fun i _ => hi i))
        ((hF.integrable_norm_pow (by decide : 2 ≠ 0)).const_mul B)
      intro ξ
      calc
        _ = (∑ i ∈ s, w i * ‖ψ i ξ‖ ^ 2) * ‖F ξ‖ ^ 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, mul_pow]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hB ξ) (sq_nonneg _)
    _ = _ := integral_const_mul B _

theorem finite_multiplier_fourier_derivative_energy_le {ι : Type*} (s : Finset ι)
    (ψ : ι → 𝓢(ℝ, ℂ)) (w : ι → ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (n : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hψ : ∀ ξ, ∑ i ∈ s, w i * ‖ψ i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ s, w i * ∫ ξ, ‖ψ i ξ * iteratedDeriv n (𝓕 f) ξ‖ ^ 2) ≤
      B * ((2 * Real.pi) ^ (2 * n) * ‖hf.toLp f‖ ^ 2) :=
  (finite_multiplier_energy_le s ψ w (unit_supported_fourier_derivative_memLp hf hs n) hψ).trans
    (mul_le_mul_of_nonneg_left (unit_supported_fourier_derivative_energy_le hf hs n) hB)

theorem finite_smoothBand_energy_le {ι : Type*} (s : Finset ι) (χ : ι → 𝓢(ℝ, ℂ))
    (hc : ∀ i, HasCompactSupport (⇑(χ i))) (w : ι → ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) {B : ℝ}
    (hB : ∀ ξ, ∑ i ∈ s, w i * ‖χ i ξ‖ ^ 2 ≤ B) :
    (∑ i ∈ s, w i * ‖(smoothBand hf hs (χ i) (hc i)).toLp 2 volume‖ ^ 2) ≤
      B * ‖hf.toLp f‖ ^ 2 := by
  have h := finite_multiplier_energy_le s χ w (Lp.memLp (𝓕 (hf.toLp f) : ComplexL2)) hB
  have he : (∑ i ∈ s, w i * ‖(smoothBand hf hs (χ i) (hc i)).toLp 2 volume‖ ^ 2) =
      ∑ i ∈ s, w i * ∫ ξ, ‖χ i ξ * (𝓕 (hf.toLp f) : ComplexL2) ξ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [smoothBand_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [norm_mul, mul_pow]
  rw [he]
  simpa only [← complexL2_norm_sq, Lp.norm_fourier_eq] using h

end TransposeFollowup
