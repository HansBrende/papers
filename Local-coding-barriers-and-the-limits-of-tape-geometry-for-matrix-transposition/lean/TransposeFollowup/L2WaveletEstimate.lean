import TransposeFollowup.L2WaveletCoefficient

/-! The positive affine wavelet bound for arbitrary complex L2 test vectors.
Fatou's lemma transfers the proved Schwartz bound; finiteness then yields
genuine Bochner integrability, so the real integral is not vacuous. -/
namespace TransposeFollowup
open Classical MeasureTheory Set SchwartzMap Filter
open scoped FourierTransform Topology ENNReal
set_option autoImplicit false

theorem schwartz_wavelet_lintegral_le (u v : 𝓢(ℝ, ℂ)) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖waveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)
      ∂(volume.restrict (Ioi 0)).prod volume) ≤
        ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v.toLp 2 volume‖ ^ 2) := by
  have hm : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (‖waveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)) :=
    ((waveletCoefficient_measurable u v).norm.pow_const 2 |>.div
      (measurable_fst.pow_const 2)).ennreal_ofReal
  rw [lintegral_prod _ hm.aemeasurable]
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal
        ((∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) / s ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      rw [← integral_div]
      exact (ofReal_integral_eq_lintegral_ofReal
        ((wavelet_translation_energy_integrable u v hs).div_const _)
        (ae_of_all _ (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))).symm
    _ = ENNReal.ofReal (∫ s in Ioi (0 : ℝ),
        (∫ t : ℝ, ‖waveletCoefficient u v s t‖ ^ 2) / s ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal (wavelet_scale_energy_integrable u v hM hzero)
        (ae_of_all _ (fun _ => div_nonneg (integral_nonneg (fun _ => sq_nonneg _))
          (sq_nonneg _)))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (schwartz_wavelet_energy_le u v hM hzero)

theorem l2_wavelet_lintegral_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)
      ∂(volume.restrict (Ioi 0)).prod volume) ≤
        ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2) := by
  obtain ⟨w, hw⟩ := schwartz_toL2_sequence v
  let f (n : ℕ) (z : ℝ × ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (‖l2WaveletCoefficient u ((w n).toLp 2 volume) z.1 z.2‖ ^ 2 / z.1 ^ 2)
  have hm (n : ℕ) : Measurable (f n) :=
    ((l2WaveletCoefficient_measurable u _).norm.pow_const 2 |>.div
      (measurable_fst.pow_const 2)).ennreal_ofReal
  have ht (z : ℝ × ℝ) : Tendsto (fun n => f n z) atTop
      (𝓝 (ENNReal.ofReal (‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2))) :=
    ENNReal.tendsto_ofReal (((l2WaveletCoefficient_tendsto u hw z.1 z.2).norm.pow 2).div_const _)
  have hb (n : ℕ) : (∫⁻ z, f n z ∂(volume.restrict (Ioi 0)).prod volume) ≤
      ENNReal.ofReal (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖(w n).toLp 2 volume‖ ^ 2) := by
    simpa only [f, l2WaveletCoefficient_schwartz] using
      schwartz_wavelet_lintegral_le u (w n) hM hzero
  calc
    _ = ∫⁻ z, liminf (fun n => f n z) atTop ∂(volume.restrict (Ioi 0)).prod volume :=
      lintegral_congr (fun z => (ht z).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ z, f n z ∂(volume.restrict (Ioi 0)).prod volume) atTop :=
      lintegral_liminf_le hm
    _ ≤ liminf (fun n => ENNReal.ofReal
        (M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖(w n).toLp 2 volume‖ ^ 2)) atTop :=
      liminf_le_liminf (Eventually.of_forall hb)
    _ = _ := (ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hw.norm.pow 2))).liminf_eq

theorem l2_wavelet_energy_integrable (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    Integrable (fun z : ℝ × ℝ => ‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : Measurable (fun z : ℝ × ℝ =>
      ‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2) :=
    (l2WaveletCoefficient_measurable u v).norm.pow_const 2 |>.div (measurable_fst.pow_const 2)
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))).mp
    (ne_of_lt ((l2_wavelet_lintegral_le u v hM hzero).trans_lt ENNReal.ofReal_lt_top))

theorem l2_wavelet_energy_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ z : ℝ × ℝ, ‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2
      ∂(volume.restrict (Ioi 0)).prod volume) ≤
        M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2 := by
  have hb := l2_wavelet_lintegral_le u v hM hzero
  rw [← ofReal_integral_eq_lintegral_ofReal (l2_wavelet_energy_integrable u v hM hzero)
    (ae_of_all _ (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

theorem l2_wavelet_iterated_energy_le (u : 𝓢(ℝ, ℂ)) (v : ComplexL2) {M : ℝ} (hM : 0 < M)
    (hzero : ∀ ξ : ℝ, |ξ| < M → (𝓕 u : 𝓢(ℝ, ℂ)) ξ = 0) :
    (∫ s in Ioi (0 : ℝ), (∫ t : ℝ, ‖l2WaveletCoefficient u v s t‖ ^ 2) / s ^ 2) ≤
      M⁻¹ * ‖u.toLp 2 volume‖ ^ 2 * ‖v‖ ^ 2 := by
  have he := integral_prod (fun z : ℝ × ℝ =>
    ‖l2WaveletCoefficient u v z.1 z.2‖ ^ 2 / z.1 ^ 2)
    (l2_wavelet_energy_integrable u v hM hzero)
  simp_rw [integral_div] at he
  rw [← he]
  exact l2_wavelet_energy_le u v hM hzero

end TransposeFollowup
