import TransposeFollowup.SmoothedWalkAutocorrelation
import TransposeFollowup.MobiusWalkEntrySupport

/-! Derived matrix-entry support for autocorrelations and their canonical
densities. This accounts for both inversion and multiplication. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem inv_ae_matrixEntryBox (μ : Measure Group) {B : ℝ}
    (hμ : ∀ᵐ g ∂μ, g ∈ matrixEntryBox B) :
    ∀ᵐ g ∂μ.inv, g ∈ matrixEntryBox B := by
  rw [Measure.inv_def]
  apply (ae_map_iff (p := fun g => g ∈ matrixEntryBox B) measurable_inv.aemeasurable
    (matrixEntryBox_isCompact B).isClosed.measurableSet).mpr
  exact hμ.mono (fun _ hg => matrixEntryBox_inv hg)

theorem autocorrelation_ae_matrixEntryBox (μ : Measure Group) [SFinite μ] {B : ℝ}
    (hμ : ∀ᵐ g ∂μ, g ∈ matrixEntryBox B) :
    ∀ᵐ g ∂μ.inv ∗ₘ μ, g ∈ matrixEntryBox (2 * B ^ 2) := by
  simpa only [pow_two, mul_assoc] using mconv_ae_matrixEntryBox μ.inv μ (inv_ae_matrixEntryBox μ hμ) hμ

theorem smoothedAutocorrelation_ae_zero_outside (μ : Measure Group) [SFinite μ] (η : ℝ) {B : ℝ}
    (hμ : ∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B) :
    ∀ᵐ g ∂(Measure.haar : Measure Group),
      g ∉ matrixEntryBox (2 * B ^ 2) → mobiusSmoothedAutocorrelation μ η g = 0 := by
  have : SFinite (mobiusHaarKernel η) := by unfold mobiusHaarKernel; infer_instance
  have hs := autocorrelation_ae_matrixEntryBox (μ ∗ₘ mobiusHaarKernel η) hμ
  rw [mobiusSmoothedAutocorrelation_withDensity,
    ae_withDensity_iff (mobiusSmoothedAutocorrelation_measurable μ η)] at hs
  exact hs.mono (fun _ hg hnot => by
    by_contra hn
    exact hnot (hg hn))

theorem generatorWalkAutocorrelation_ae_zero_outside {c : ℕ} (G : Fin c → Group) (hc : 0 < c)
    {A η : ℝ} (hG : ∀ i, G i ∈ matrixEntryBox A) (hη : 0 < η) (hηone : η ≤ 1) (n : ℕ) :
    ∀ᵐ g ∂(Measure.haar : Measure Group),
      g ∉ matrixEntryBox (32 * (2 * A) ^ (2 * n)) →
        mobiusSmoothedAutocorrelation (generatorWalkMeasure G n) η g = 0 := by
  have : IsProbabilityMeasure (generatorWalkMeasure G n) := generatorWalkMeasure_probability G hc n
  have hs := smoothedAutocorrelation_ae_zero_outside (generatorWalkMeasure G n) η
    (generatorWalk_smoothed_ae_entryBox G hc hG hη hηone n)
  convert hs using 1
  rw [show 2 * n = n * 2 by omega, pow_mul]
  ring

end TransposeFollowup.RealMobius
