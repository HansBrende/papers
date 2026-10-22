import TransposeFollowup.WaveletScaleKernel

/-! A positive-scale affine wavelet estimate for actual Schwartz vectors.
The singular scale integral and all translation energies are integrable. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap
open scoped FourierTransform
set_option autoImplicit false

noncomputable def schwartzUnitaryScale (u : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 < s) : 𝓢(ℝ, ℂ) :=
  (Real.sqrt s)⁻¹ • schwartzRescale u s⁻¹ (inv_pos.mpr hs)

theorem schwartzUnitaryScale_apply (u : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 < s) (x : ℝ) :
    schwartzUnitaryScale u s hs x = (Real.sqrt s)⁻¹ • u (s⁻¹ * x) := rfl

theorem fourier_schwartzUnitaryScale (u : 𝓢(ℝ, ℂ)) (s : ℝ) (hs : 0 < s) (ξ : ℝ) :
    (𝓕 (schwartzUnitaryScale u s hs) : 𝓢(ℝ, ℂ)) ξ =
      Real.sqrt s • (𝓕 u : 𝓢(ℝ, ℂ)) (s * ξ) := by
  have hsq : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have he : (Real.sqrt s)⁻¹ * s = Real.sqrt s := by
    calc
      _ = (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt s) :=
        congrArg (fun z : ℝ => (Real.sqrt s)⁻¹ * z) (Real.mul_self_sqrt hs.le).symm
      _ = _ := inv_mul_cancel_left₀ hsq _
  simp only [schwartzUnitaryScale, FourierTransform.fourier_smul, smul_apply, fourier_schwartzRescale,
    inv_inv, smul_smul, he]

noncomputable def waveletCoefficient (u v : 𝓢(ℝ, ℂ)) (s t : ℝ) : ℂ :=
  ∫ x : ℝ, inner ℂ (v x) ((Real.sqrt s)⁻¹ • u (s⁻¹ * (x - t)))

theorem waveletCoefficient_eq_inner (u v : 𝓢(ℝ, ℂ)) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    waveletCoefficient u v s t =
      inner ℂ (v.toLp 2 volume) (((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t).toLp 2 volume) := by
  rw [SchwartzMap.inner_toL2_toL2_eq v ((schwartzUnitaryScale u s hs).compSubConstCLM ℂ t) volume]
  rfl

theorem waveletCoefficient_measurable (u v : 𝓢(ℝ, ℂ)) :
    Measurable (fun z : ℝ × ℝ => waveletCoefficient u v z.1 z.2) := by
  have hm : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      inner ℂ (v z.2) ((Real.sqrt z.1.1)⁻¹ • u (z.1.1⁻¹ * (z.2 - z.1.2)))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem wavelet_translation_energy (u v : 𝓢(ℝ, ℂ)) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) =
      s * ∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) (s * ξ)‖ ^ 2 * ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 := by
  simp_rw [waveletCoefficient_eq_inner u v hs]
  rw [schwartz_translation_correlation_energy]
  simp_rw [fourier_schwartzUnitaryScale, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg s), mul_pow, Real.sq_sqrt hs.le, mul_assoc]
  exact integral_const_mul _ _

theorem wavelet_translation_energy_integrable (u v : 𝓢(ℝ, ℂ)) {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => ‖waveletCoefficient u v s t‖ ^ 2) := by
  simp_rw [waveletCoefficient_eq_inner u v hs]
  exact schwartz_translation_correlation_integrable _ _

theorem wavelet_weighted_energy_eq_kernel (u v : 𝓢(ℝ, ℂ)) {s : ℝ} (hs : 0 < s) :
    (∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) / s ^ 2 =
      ∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) (s * ξ)‖ ^ 2 / |s| * ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 := by
  rw [wavelet_translation_energy u v hs, abs_of_pos hs]
  calc
    _ = (∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) (s * ξ)‖ ^ 2 * ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2) / s := by
      field_simp
    _ = _ := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring

theorem wavelet_scale_energy_integrable (u v : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    IntegrableOn (fun s : ℝ => (∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) / s ^ 2) (Ioi 0) := by
  have hi := integrable_wavelet_scale_kernel (by fun_prop : Measurable (fun ξ : ℝ => ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2))
    (by fun_prop : Measurable (fun ξ : ℝ => ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2))
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (schwartz_wavelet_density_integrable u hM hzero) (schwartz_integrable_norm_sq (𝓕 v))
  apply hi.integral_prod_left.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (wavelet_weighted_energy_eq_kernel u v hs).symm

theorem schwartz_wavelet_energy_le (u v : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ s in Ioi (0 : ℝ), (∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) / s ^ 2) ≤
      M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v.toLp 2 volume‖ ^ 2 := by
  calc
    _ = ∫ s in Ioi (0 : ℝ), ∫ ξ : ℝ,
        ‖(𝓕 u : 𝓢(ℝ, ℂ)) (s * ξ)‖ ^ 2 / |s| * ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioi (fun s hs => wavelet_weighted_energy_eq_kernel u v hs)
    _ ≤ (∫ ξ : ℝ, ‖(𝓕 u : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 / |ξ|) *
        ∫ ξ : ℝ, ‖(𝓕 v : 𝓢(ℝ, ℂ)) ξ‖ ^ 2 :=
      integral_positive_wavelet_scale_kernel_le (by fun_prop) (by fun_prop)
        (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
        (schwartz_wavelet_density_integrable u hM hzero) (schwartz_integrable_norm_sq (𝓕 v))
    _ ≤ _ := by
      rw [SchwartzMap.integral_norm_sq_fourier, ← schwartz_toLp_norm_sq]
      exact mul_le_mul_of_nonneg_right (schwartz_wavelet_admissibility_le u hM hzero) (sq_nonneg _)

end TransposeFollowup
