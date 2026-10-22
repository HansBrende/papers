import TransposeFollowup.SchwartzAffineFourier
import Mathlib.MeasureTheory.Integral.Prod

/-! The singular scale integral used in wavelet Plancherel. Integrability
is derived before applying Fubini; the zero-frequency fiber is null. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

theorem schwartz_wavelet_density_le (u : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) (ξ : ℝ) :
    ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 / |ξ| ≤ M⁻¹ * ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 := by
  by_cases hlo : |ξ| < M
  · simp [hzero ξ hlo]
  · have hm : M ≤ |ξ| := le_of_not_gt hlo
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hM hm) (sq_nonneg _)

theorem schwartz_wavelet_density_integrable (u : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    Integrable (fun ξ : ℝ => ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 / |ξ|) := by
  have hm : Measurable (fun ξ : ℝ => ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 / |ξ|) := by fun_prop
  apply ((schwartz_integrable_norm_sq (𝓕 u)).const_mul M⁻¹).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact schwartz_wavelet_density_le u hM hzero ξ

theorem schwartz_wavelet_admissibility_le (u : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 / |ξ|) ≤ M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 := by
  calc
    _ ≤ ∫ ξ : ℝ, M⁻¹ * ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 :=
      integral_mono (schwartz_wavelet_density_integrable u hM hzero)
        ((schwartz_integrable_norm_sq (𝓕 u)).const_mul M⁻¹) (schwartz_wavelet_density_le u hM hzero)
    _ = _ := by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier, ← schwartz_toLp_norm_sq]

theorem weighted_mul_scale_identity (q : ℝ → ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) (s : ℝ) :
    q (s * ξ) / |s| = |ξ| * (q (s * ξ) / |s * ξ|) := by
  by_cases hs : s = 0
  · simp [hs]
  · rw [abs_mul]
    field_simp [abs_ne_zero.mpr hs, abs_ne_zero.mpr hξ]

theorem weighted_mul_scale_integrable {q : ℝ → ℝ}
    (hq : Integrable (fun s : ℝ => q s / |s|)) {ξ : ℝ} (hξ : ξ ≠ 0) :
    Integrable (fun s : ℝ => q (s * ξ) / |s|) := by
  have h := (hq.comp_mul_right' hξ).const_mul |ξ|
  exact h.congr (Filter.Eventually.of_forall fun s => (weighted_mul_scale_identity q hξ s).symm)

theorem integral_weighted_mul_scale (q : ℝ → ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ s : ℝ, q (s * ξ) / |s|) = ∫ x : ℝ, q x / |x| := by
  simp_rw [weighted_mul_scale_identity q hξ]
  rw [integral_const_mul, Measure.integral_comp_mul_right (fun x : ℝ => q x / |x|) ξ,
    smul_eq_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hξ), one_mul]

theorem integrable_wavelet_scale_kernel {q ψ : ℝ → ℝ} (hq : Measurable q) (hψ : Measurable ψ)
    (hqpos : ∀ x, 0 ≤ q x) (hψpos : ∀ x, 0 ≤ ψ x)
    (hqint : Integrable (fun x : ℝ => q x / |x|)) (hψint : Integrable ψ) :
    Integrable (fun z : ℝ × ℝ => q (z.1 * z.2) / |z.1| * ψ z.2) (volume.prod volume) := by
  have hm : Measurable (fun z : ℝ × ℝ => q (z.1 * z.2) / |z.1| * ψ z.2) :=
    ((hq.comp (measurable_fst.mul measurable_snd)).div
      (continuous_abs.measurable.comp measurable_fst)).mul (hψ.comp measurable_snd)
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [volume.ae_ne (0 : ℝ)] with ξ hξ
    exact (weighted_mul_scale_integrable hqint hξ).mul_const (ψ ξ)
  · apply (hψint.const_mul (∫ x : ℝ, q x / |x|)).congr
    filter_upwards [volume.ae_ne (0 : ℝ)] with ξ hξ
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hqpos _) (abs_nonneg _)) (hψpos _))]
    rw [integral_mul_const, integral_weighted_mul_scale q hξ]

theorem integral_wavelet_scale_kernel {q ψ : ℝ → ℝ} (hq : Measurable q) (hψ : Measurable ψ)
    (hqpos : ∀ x, 0 ≤ q x) (hψpos : ∀ x, 0 ≤ ψ x)
    (hqint : Integrable (fun x : ℝ => q x / |x|)) (hψint : Integrable ψ) :
    (∫ s : ℝ, ∫ ξ : ℝ, q (s * ξ) / |s| * ψ ξ) =
      (∫ x : ℝ, q x / |x|) * ∫ ξ : ℝ, ψ ξ := by
  rw [integral_integral_swap (integrable_wavelet_scale_kernel hq hψ hqpos hψpos hqint hψint),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ)] with ξ hξ
  rw [integral_mul_const, integral_weighted_mul_scale q hξ]

theorem integral_positive_wavelet_scale_kernel_le {q ψ : ℝ → ℝ} (hq : Measurable q) (hψ : Measurable ψ)
    (hqpos : ∀ x, 0 ≤ q x) (hψpos : ∀ x, 0 ≤ ψ x)
    (hqint : Integrable (fun x : ℝ => q x / |x|)) (hψint : Integrable ψ) :
    (∫ s in Ioi (0 : ℝ), ∫ ξ : ℝ, q (s * ξ) / |s| * ψ ξ) ≤
      (∫ x : ℝ, q x / |x|) * ∫ ξ : ℝ, ψ ξ := by
  rw [← integral_wavelet_scale_kernel hq hψ hqpos hψpos hqint hψint]
  apply setIntegral_le_integral
    (integrable_wavelet_scale_kernel hq hψ hqpos hψpos hqint hψint).integral_prod_left
  exact Filter.Eventually.of_forall fun s => integral_nonneg fun ξ =>
    mul_nonneg (div_nonneg (hqpos _) (abs_nonneg _)) (hψpos _)

end TransposeFollowup
