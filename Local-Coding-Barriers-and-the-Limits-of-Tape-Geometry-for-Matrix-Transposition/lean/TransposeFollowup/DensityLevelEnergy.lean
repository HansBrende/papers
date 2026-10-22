import TransposeFollowup.DensityTailEnergy

/-! A quantitative level-pair extraction for continuous convolution energy.
All losses are explicit: a low-tail error and the fourth power of the
number of dyadic levels. This is not a finite-group energy statement. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

noncomputable def haarMultiplicativeEnergy (σ : Measure H) (A B : Set H) : ℝ≥0∞ :=
  ∫⁻ x, densityConvolution σ (A.indicator 1) (B.indicator 1) x ^ 2 ∂σ

theorem densityConvolution_sum_sum (σ : Measure H) {ι : Type*} (s : Finset ι)
    {f : ι → H → ℝ≥0∞} (hf : ∀ i ∈ s, Measurable (f i)) (x : H) :
    densityConvolution σ (fun y => ∑ i ∈ s, f i y) (fun y => ∑ i ∈ s, f i y) x =
      ∑ p ∈ s ×ˢ s, densityConvolution σ (f p.1) (f p.2) x := by
  rw [densityConvolution_sum_left σ s hf (Finset.measurable_sum _ hf), Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  exact densityConvolution_sum_right σ s (hf i hi) hf x

theorem exists_densityConvolution_sum_energy (σ : Measure H) [SFinite σ]
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) {f : ι → H → ℝ≥0∞}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    ∃ i ∈ s, ∃ j ∈ s,
      (∫⁻ x, densityConvolution σ (fun y => ∑ t ∈ s, f t y) (fun y => ∑ t ∈ s, f t y) x ^ 2 ∂σ) ≤
        (s.card : ℝ≥0∞) ^ 4 * ∫⁻ x, densityConvolution σ (f i) (f j) x ^ 2 ∂σ := by
  let z := fun (p : ι × ι) => densityConvolution σ (f p.1) (f p.2)
  have hz : ∀ p ∈ s ×ˢ s, Measurable (z p) := by
    intro p hp
    exact densityConvolution_measurable σ (hf p.1 (Finset.mem_product.mp hp).1)
      (hf p.2 (Finset.mem_product.mp hp).2)
  obtain ⟨p, hp, hmax⟩ := (s ×ˢ s).exists_max_image (fun p => ∫⁻ x, z p x ^ 2 ∂σ) (hs.product hs)
  refine ⟨p.1, (Finset.mem_product.mp hp).1, p.2, (Finset.mem_product.mp hp).2, ?_⟩
  calc
    _ = ∫⁻ x, (∑ q ∈ s ×ˢ s, z q x) ^ 2 ∂σ := by
      apply lintegral_congr
      intro x
      rw [densityConvolution_sum_sum σ s hf]
    _ ≤ ((s ×ˢ s).card : ℝ≥0∞) * ∑ q ∈ s ×ˢ s, ∫⁻ x, z q x ^ 2 ∂σ :=
      lintegral_sum_sq_le σ _ hz
    _ ≤ ((s ×ˢ s).card : ℝ≥0∞) * ∑ _q ∈ s ×ˢ s, ∫⁻ x, z p x ^ 2 ∂σ :=
      mul_le_mul' le_rfl (Finset.sum_le_sum hmax)
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
      dsimp only [z]
      ring

theorem weighted_indicator_convolution_energy (σ : Measure H) [SFinite σ]
    {A B : Set H} (hA : MeasurableSet A) (hB : MeasurableSet B) (a b : ℝ≥0∞) :
    (∫⁻ x, densityConvolution σ (fun y => a * A.indicator 1 y) (fun y => b * B.indicator 1 y) x ^ 2 ∂σ) =
      (a * b) ^ 2 * haarMultiplicativeEnergy σ A B := by
  have hAi : Measurable (A.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hA
  have hBi : Measurable (B.indicator (1 : H → ℝ≥0∞)) := measurable_const.indicator hB
  simp_rw [densityConvolution_const_mul σ hAi hBi a b, mul_pow]
  exact lintegral_const_mul _ ((densityConvolution_measurable σ hAi hBi).pow_const 2)

theorem exists_dyadicDensityLevel_energy (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) ≤ 1)
    {a : ℝ≥0∞} {N : ℕ} (hN : 0 < N) (hcap : ∀ x, f x < a * 2 ^ N) :
    ∃ i < N, ∃ j < N,
      (∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) ≤
        8 * a + 2 * (N : ℝ≥0∞) ^ 4 * ((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
          haarMultiplicativeEnergy σ (dyadicDensityLevel f a i) (dyadicDensityLevel f a j) := by
  let F := fun j x => (a * 2 ^ (j + 1)) * (dyadicDensityLevel f a j).indicator 1 x
  have hF (j : ℕ) : Measurable (F j) :=
    measurable_const.mul (measurable_const.indicator (dyadicDensityLevel_measurableSet hf a j))
  obtain ⟨i, hi, j, hj, hE⟩ := exists_densityConvolution_sum_energy σ (Finset.range N)
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (fun j _ => hF j)
  rw [weighted_indicator_convolution_energy σ (dyadicDensityLevel_measurableSet hf a i)
    (dyadicDensityLevel_measurableSet hf a j), Finset.card_range] at hE
  refine ⟨i, Finset.mem_range.mp hi, j, Finset.mem_range.mp hj, ?_⟩
  calc
    _ ≤ 8 * a + 2 * ∫⁻ x, densityConvolution σ (densityHigh f a) (densityHigh f a) x ^ 2 ∂σ :=
      densityConvolution_tail_energy σ hf hm a
    _ ≤ 8 * a + 2 * ∫⁻ x, densityConvolution σ (dyadicDensityMajorant f a N) (dyadicDensityMajorant f a N) x ^ 2 ∂σ := by
      apply add_le_add le_rfl
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro x
      exact pow_le_pow_left' (densityConvolution_mono σ (densityHigh_le_dyadicDensityMajorant hcap)
        (densityHigh_le_dyadicDensityMajorant hcap) x) 2
    _ ≤ 8 * a + 2 * ((N : ℝ≥0∞) ^ 4 *
        (((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
          haarMultiplicativeEnergy σ (dyadicDensityLevel f a i) (dyadicDensityLevel f a j))) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hE)
    _ = _ := by ring

theorem exists_dyadicDensityLevel_large_energy (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) ≤ 1)
    {a τ : ℝ≥0∞} {N : ℕ} (hN : 0 < N) (hcap : ∀ x, f x < a * 2 ^ N)
    (hτ : τ ≠ ⊤) (htail : 16 * a ≤ τ)
    (hnonflat : τ ≤ ∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) :
    ∃ i < N, ∃ j < N,
      τ ≤ 4 * (N : ℝ≥0∞) ^ 4 * ((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
        haarMultiplicativeEnergy σ (dyadicDensityLevel f a i) (dyadicDensityLevel f a j) := by
  obtain ⟨i, hi, j, hj, hE⟩ := exists_dyadicDensityLevel_energy σ hf hm hN hcap
  refine ⟨i, hi, j, hj, ?_⟩
  have ht : 2 * (8 * a) ≤ τ := by simpa only [← mul_assoc, show (2 : ℝ≥0∞) * 8 = 16 by norm_num] using htail
  have h := ennreal_le_two_mul_of_small_add hτ ht (hnonflat.trans hE)
  convert h using 1
  ring

end TransposeFollowup
