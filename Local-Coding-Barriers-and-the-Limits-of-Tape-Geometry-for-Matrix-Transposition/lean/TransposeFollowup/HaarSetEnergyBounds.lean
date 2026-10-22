import TransposeFollowup.DensityLevelEnergy

/-! Upper bounds, finiteness and nondegeneracy of continuous set energy.
The group need not be commutative. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem haarMultiplicativeEnergy_le_left (σ : Measure H) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    haarMultiplicativeEnergy σ A B ≤ σ A ^ 2 * σ B := by
  have hf : Measurable (A.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hA
  have hg : Measurable (B.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hB
  have hpoint (x : H) : densityConvolution σ (A.indicator 1) (B.indicator 1) x ≤ σ A := by
    have h := densityConvolution_le_of_right_le σ hf
      (show ∀ x, B.indicator (1 : H → ℝ≥0∞) x ≤ 1 from fun x => Set.indicator_le_self' (fun _ _ => zero_le) x) x
    simpa only [lintegral_indicator hA, Pi.one_apply, lintegral_one, Measure.restrict_apply_univ, mul_one] using h
  calc
    _ ≤ σ A * ∫⁻ x, densityConvolution σ (A.indicator 1) (B.indicator 1) x ∂σ :=
      lintegral_sq_le_bound_mul_lintegral σ (densityConvolution_measurable σ hf hg) hpoint
    _ = _ := by
      rw [densityConvolution_lintegral σ hf hg, lintegral_indicator hA, lintegral_indicator hB]
      simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply_univ]
      ring

theorem haarMultiplicativeEnergy_le_right (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    haarMultiplicativeEnergy σ A B ≤ σ A * σ B ^ 2 := by
  have hf : Measurable (A.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hA
  have hg : Measurable (B.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hB
  have hpoint (x : H) : densityConvolution σ (A.indicator 1) (B.indicator 1) x ≤ σ B := by
    have h := densityConvolution_le_of_left_le σ hg
      (show ∀ x, A.indicator (1 : H → ℝ≥0∞) x ≤ 1 from fun x => Set.indicator_le_self' (fun _ _ => zero_le) x) x
    simpa only [lintegral_indicator hB, Pi.one_apply, lintegral_one, Measure.restrict_apply_univ, one_mul] using h
  calc
    _ ≤ σ B * ∫⁻ x, densityConvolution σ (A.indicator 1) (B.indicator 1) x ∂σ :=
      lintegral_sq_le_bound_mul_lintegral σ (densityConvolution_measurable σ hf hg) hpoint
    _ = _ := by
      rw [densityConvolution_lintegral σ hf hg, lintegral_indicator hA, lintegral_indicator hB]
      simp only [Pi.one_apply, lintegral_one, Measure.restrict_apply_univ]
      ring

theorem haarMultiplicativeEnergy_lt_top (σ : Measure H) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAt : σ A < ⊤) (hBt : σ B < ⊤) :
    haarMultiplicativeEnergy σ A B < ⊤ :=
  (haarMultiplicativeEnergy_le_left σ hA hB).trans_lt (by finiteness)

theorem haarMultiplicativeEnergy_pos_measures (σ : Measure H) [SFinite σ] [Measure.IsMulLeftInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hE : 0 < haarMultiplicativeEnergy σ A B) : 0 < σ A ∧ 0 < σ B := by
  have h := hE.trans_le (haarMultiplicativeEnergy_le_left σ hA hB)
  constructor
  · by_contra hn
    have hz : σ A = 0 := le_antisymm (le_of_not_gt hn) zero_le
    simp [hz] at h
  · by_contra hn
    have hz : σ B = 0 := le_antisymm (le_of_not_gt hn) zero_le
    simp [hz] at h

theorem haarMultiplicativeEnergy_volume_comparable (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : σ A ≠ 0) (hB0 : σ B ≠ 0) (hAt : σ A ≠ ⊤) (hBt : σ B ≠ ⊤)
    {θ K : ℝ≥0∞}
    (hleft : θ * σ A ^ 2 * σ B ≤ K * haarMultiplicativeEnergy σ A B)
    (hright : θ * σ A * σ B ^ 2 ≤ K * haarMultiplicativeEnergy σ A B) :
    θ * σ A ≤ K * σ B ∧ θ * σ B ≤ K * σ A := by
  have hc0 := mul_ne_zero hA0 hB0
  have hct := ENNReal.mul_ne_top hAt hBt
  constructor
  · apply (ENNReal.mul_le_mul_iff_left hc0 hct).mp
    calc
      _ = θ * σ A ^ 2 * σ B := by ring
      _ ≤ K * haarMultiplicativeEnergy σ A B := hleft
      _ ≤ K * (σ A * σ B ^ 2) := mul_le_mul' le_rfl (haarMultiplicativeEnergy_le_right σ hA hB)
      _ = _ := by ring
  · apply (ENNReal.mul_le_mul_iff_left hc0 hct).mp
    calc
      _ = θ * σ A * σ B ^ 2 := by ring
      _ ≤ K * haarMultiplicativeEnergy σ A B := hright
      _ ≤ K * (σ A ^ 2 * σ B) := mul_le_mul' le_rfl (haarMultiplicativeEnergy_le_left σ hA hB)
      _ = _ := by ring

end TransposeFollowup
