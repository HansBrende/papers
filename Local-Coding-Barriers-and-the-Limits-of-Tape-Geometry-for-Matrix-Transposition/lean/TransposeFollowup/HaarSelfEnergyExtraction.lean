import TransposeFollowup.RelativeNonflatteningEnergy
import TransposeFollowup.DensityConvolutionTrace

/-! Symmetric level pairs yield high self-energy. This completes the
continuous energy reduction needed before approximate-group extraction. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem haarMultiplicativeEnergy_sq_le_self_mul_self (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A) (hBs : ∀ x, x⁻¹ ∈ B ↔ x ∈ B) :
    haarMultiplicativeEnergy σ A B ^ 2 ≤
      haarMultiplicativeEnergy σ A A * haarMultiplicativeEnergy σ B B := by
  apply densityConvolution_energy_sq_le σ (measurable_const.indicator hA) (measurable_const.indicator hB)
  · intro x
    change A.indicator (1 : H → ℝ≥0∞) x⁻¹ = A.indicator (1 : H → ℝ≥0∞) x
    simp only [Set.indicator_apply, hAs x, Pi.one_apply]
  · intro x
    change B.indicator (1 : H → ℝ≥0∞) x⁻¹ = B.indicator (1 : H → ℝ≥0∞) x
    simp only [Set.indicator_apply, hBs x, Pi.one_apply]

theorem haarMultiplicativeEnergy_self_lower (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsInvInvariant σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAs : ∀ x, x⁻¹ ∈ A ↔ x ∈ A) (hBs : ∀ x, x⁻¹ ∈ B ↔ x ∈ B)
    (hA0 : σ A ≠ 0) (hB0 : σ B ≠ 0) (hAt : σ A ≠ ⊤) (hBt : σ B ≠ ⊤)
    {θ K : ℝ≥0∞}
    (hleft : θ * σ A ^ 2 * σ B ≤ K * haarMultiplicativeEnergy σ A B)
    (hright : θ * σ A * σ B ^ 2 ≤ K * haarMultiplicativeEnergy σ A B) :
    θ ^ 2 * σ A ^ 3 ≤ K ^ 2 * haarMultiplicativeEnergy σ A A ∧
      θ ^ 2 * σ B ^ 3 ≤ K ^ 2 * haarMultiplicativeEnergy σ B B := by
  have hprod : θ ^ 2 * σ A ^ 3 * σ B ^ 3 ≤ K ^ 2 *
      (haarMultiplicativeEnergy σ A A * haarMultiplicativeEnergy σ B B) := by
    calc
      _ = (θ * σ A ^ 2 * σ B) * (θ * σ A * σ B ^ 2) := by ring
      _ ≤ (K * haarMultiplicativeEnergy σ A B) * (K * haarMultiplicativeEnergy σ A B) :=
        mul_le_mul' hleft hright
      _ = K ^ 2 * haarMultiplicativeEnergy σ A B ^ 2 := by ring
      _ ≤ _ := mul_le_mul' le_rfl (haarMultiplicativeEnergy_sq_le_self_mul_self σ hA hB hAs hBs)
  have hAA : haarMultiplicativeEnergy σ A A ≤ σ A ^ 3 := by
    simpa only [pow_succ, pow_one, mul_assoc] using haarMultiplicativeEnergy_le_left σ hA hA
  have hBB : haarMultiplicativeEnergy σ B B ≤ σ B ^ 3 := by
    simpa only [pow_succ, pow_one, mul_assoc] using haarMultiplicativeEnergy_le_left σ hB hB
  constructor
  · apply (ENNReal.mul_le_mul_iff_left (pow_ne_zero 3 hB0) (by finiteness)).mp
    calc
      _ ≤ K ^ 2 * (haarMultiplicativeEnergy σ A A * haarMultiplicativeEnergy σ B B) := hprod
      _ ≤ K ^ 2 * (haarMultiplicativeEnergy σ A A * σ B ^ 3) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hBB)
      _ = _ := by ring
  · apply (ENNReal.mul_le_mul_iff_left (pow_ne_zero 3 hA0) (by finiteness)).mp
    calc
      _ = θ ^ 2 * σ A ^ 3 * σ B ^ 3 := by ring
      _ ≤ K ^ 2 * (haarMultiplicativeEnergy σ A A * haarMultiplicativeEnergy σ B B) := hprod
      _ ≤ K ^ 2 * (σ A ^ 3 * haarMultiplicativeEnergy σ B B) :=
        mul_le_mul' le_rfl (mul_le_mul' hAA le_rfl)
      _ = _ := by ring

theorem exists_symmetric_nonflattening_self_energy (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) = 1)
    (hs : ∀ x, f x⁻¹ = f x) {C θ : ℝ} (hθ : 0 < θ) (hC : ∀ x, f x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal θ * (∫⁻ x, f x ^ 2 ∂σ) ≤
      ∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) :
    let τ := θ * (∫⁻ x, f x ^ 2 ∂σ).toReal
    let a := ENNReal.ofReal (τ / 16)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / τ)) ∧
      ∃ i < N, let A := dyadicDensityLevel f a i
        MeasurableSet A ∧ (∀ x, x⁻¹ ∈ A ↔ x ∈ A) ∧ 0 < σ A ∧ σ A < ⊤ ∧
          ENNReal.ofReal θ ≤ 64 * (N : ℝ≥0∞) ^ 4 * (∫⁻ x, f x ^ 2 ∂σ) * σ A ∧
          ENNReal.ofReal θ * (∫⁻ x, f x ^ 2 ∂σ) * σ A ≤ 64 * (N : ℝ≥0∞) ^ 4 ∧
          ENNReal.ofReal θ ^ 2 * σ A ^ 3 ≤ (64 * (N : ℝ≥0∞) ^ 4) ^ 2 * haarMultiplicativeEnergy σ A A := by
  obtain ⟨N, hN, hlog, i, hi, j, _, hA0, hAt, hB0, hBt, hleft, hright, _, _, hVAlo, hVAhi, _⟩ :=
    exists_relative_nonflattening_level_pair σ hf hm hθ hC hnonflat
  have hA := dyadicDensityLevel_measurableSet hf (ENNReal.ofReal (θ * (∫⁻ x, f x ^ 2 ∂σ).toReal / 16)) i
  have hB := dyadicDensityLevel_measurableSet hf (ENNReal.ofReal (θ * (∫⁻ x, f x ^ 2 ∂σ).toReal / 16)) j
  have hself := haarMultiplicativeEnergy_self_lower σ hA hB (dyadicDensityLevel_inv hs _ i)
    (dyadicDensityLevel_inv hs _ j) hA0.ne' hB0.ne' hAt.ne hBt.ne hleft hright
  exact ⟨N, hN, hlog, i, hi, hA, dyadicDensityLevel_inv hs _ i, hA0, hAt, hVAlo, hVAhi, hself.1⟩

end TransposeFollowup
