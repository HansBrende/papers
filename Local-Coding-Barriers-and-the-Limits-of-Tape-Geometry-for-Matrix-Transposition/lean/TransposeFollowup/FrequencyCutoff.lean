import TransposeFollowup.FourierL2Bridge

/-! Actual L2 frequency truncation and its complementary component.
All norm and support statements concern the L2 quotient, with explicit
almost-everywhere representative equalities. -/
namespace TransposeFollowup
open Classical MeasureTheory Set FourierTransform
open scoped FourierTransform
set_option autoImplicit false

theorem complexL2_norm_sq (f : ComplexL2) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

noncomputable def frequencyCut (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) : ComplexL2 :=
  ((Lp.memLp (𝓕 f : ComplexL2)).indicator hs).toLp (s.indicator (𝓕 f : ComplexL2))

noncomputable def lowFrequency (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) : ComplexL2 :=
  𝓕⁻ (frequencyCut s hs f)

noncomputable def highFrequency (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) : ComplexL2 :=
  f - lowFrequency s hs f

theorem frequencyCut_coe (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ⇑(frequencyCut s hs f) =ᵐ[volume] s.indicator (𝓕 f : ComplexL2) := MemLp.coeFn_toLp _

theorem lowFrequency_fourier (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    𝓕 (lowFrequency s hs f) = frequencyCut s hs f := fourier_fourierInv_eq _

theorem lowFrequency_norm (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ‖lowFrequency s hs f‖ = ‖frequencyCut s hs f‖ := by
  rw [← Lp.norm_fourier_eq (lowFrequency s hs f), lowFrequency_fourier]

theorem lowFrequency_norm_sq (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ‖lowFrequency s hs f‖ ^ 2 = ∫ ξ in s, ‖(𝓕 f : ComplexL2) ξ‖ ^ 2 := by
  rw [lowFrequency_norm, complexL2_norm_sq]
  calc
    _ = ∫ ξ, s.indicator (fun ξ => ‖(𝓕 f : ComplexL2) ξ‖ ^ 2) ξ := by
      apply integral_congr_ae
      filter_upwards [frequencyCut_coe s hs f] with ξ hξ
      rw [hξ]
      by_cases h : ξ ∈ s <;> simp [h]
    _ = _ := integral_indicator hs

theorem lowFrequency_norm_le (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ‖lowFrequency s hs f‖ ≤ ‖f‖ := by
  rw [lowFrequency_norm, ← Lp.norm_fourier_eq f]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencyCut_coe s hs f] with ξ hξ
  rw [hξ]
  by_cases h : ξ ∈ s <;> simp [h]

theorem highFrequency_fourier_coe (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ⇑(𝓕 (highFrequency s hs f) : ComplexL2) =ᵐ[volume] sᶜ.indicator (𝓕 f : ComplexL2) := by
  have he : (𝓕 (highFrequency s hs f) : ComplexL2) = 𝓕 f - frequencyCut s hs f := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (f - lowFrequency s hs f) = _
    rw [map_sub]
    change 𝓕 f - 𝓕 (lowFrequency s hs f) = _
    rw [lowFrequency_fourier]
  rw [he]
  filter_upwards [Lp.coeFn_sub (𝓕 f : ComplexL2) (frequencyCut s hs f),
    frequencyCut_coe s hs f] with ξ hξ hc
  rw [hξ]
  change (𝓕 f : ComplexL2) ξ - frequencyCut s hs f ξ = _
  rw [hc]
  by_cases h : ξ ∈ s <;> simp [h]

theorem highFrequency_fourier_zero_on (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ∀ᵐ ξ ∂volume, ξ ∈ s → (𝓕 (highFrequency s hs f) : ComplexL2) ξ = 0 := by
  filter_upwards [highFrequency_fourier_coe s hs f] with ξ hξ hmem
  simpa [hmem] using hξ

theorem highFrequency_norm_le (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ‖highFrequency s hs f‖ ≤ ‖f‖ := by
  rw [← Lp.norm_fourier_eq (highFrequency s hs f), ← Lp.norm_fourier_eq f]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [highFrequency_fourier_coe s hs f] with ξ hξ
  rw [hξ]
  by_cases h : ξ ∈ s <;> simp [h]

theorem low_add_highFrequency (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    lowFrequency s hs f + highFrequency s hs f = f := by
  unfold highFrequency
  abel

theorem norm_sub_highFrequency (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2) :
    ‖f - highFrequency s hs f‖ = ‖lowFrequency s hs f‖ := by
  simp only [highFrequency, sub_sub_cancel]

theorem lowFrequency_norm_sq_classical (s : Set ℝ) (hs : MeasurableSet s) (f : ComplexL2)
    (hf : Integrable (f : ℝ → ℂ)) :
    ‖lowFrequency s hs f‖ ^ 2 = ∫ ξ in s, ‖𝓕 (f : ℝ → ℂ) ξ‖ ^ 2 := by
  rw [lowFrequency_norm_sq]
  apply setIntegral_congr_ae hs
  filter_upwards [L2_fourier_coe_ae f hf] with ξ hξ _
  rw [hξ]

end TransposeFollowup
