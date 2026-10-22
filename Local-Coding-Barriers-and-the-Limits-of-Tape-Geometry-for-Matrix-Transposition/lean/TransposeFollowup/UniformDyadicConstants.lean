import TransposeFollowup.DyadicFarCorrelation

/-! Fixed transport and distant-band constants for matrices whose
relevant entries have absolute value at most two. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set SchwartzMap
set_option autoImplicit false

noncomputable def universalDyadicTransportConstant : ℝ :=
  256 * dyadicFrequencyDerivativeBound 0 +
  256 * (((2 * Real.pi) ^ 4)⁻¹ *
    (3 * dyadicFrequencyDerivativeBound 0 * (2 * Real.pi) ^ 4 +
      12 * dyadicFrequencyDerivativeBound 1 * (2 * Real.pi) ^ 2 +
      3 * dyadicFrequencyDerivativeBound 2)) +
  64 * dyadicCutoffDerivativeBound 0 +
  64 * (((2 * Real.pi) ^ 2)⁻¹ *
    (2 * dyadicCutoffDerivativeBound 0 * (2 * Real.pi) ^ 2 + 2 * dyadicCutoffDerivativeBound 1))

theorem universalDyadicTransportConstant_nonneg : 0 ≤ universalDyadicTransportConstant := by
  unfold universalDyadicTransportConstant dyadicFrequencyDerivativeBound dyadicCutoffDerivativeBound
  positivity

theorem dyadicTransportConstant_le_universal (g : Group)
    (ha : |g 0 0| ≤ 2) (hc : |g 1 0| ≤ 2) :
    dyadicTransportConstant g ≤ universalDyadicTransportConstant := by
  have ha2 : (g 0 0) ^ 2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hc2 : (g 1 0) ^ 2 ≤ 4 := by
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using pow_le_pow_left₀ (abs_nonneg _) hc 2
  have ha4 : (g 0 0) ^ 4 ≤ 16 := by
    simpa only [← pow_mul, show 2 * 2 = 4 from rfl, show (4 : ℝ) ^ 2 = 16 by norm_num]
      using pow_le_pow_left₀ (sq_nonneg _) ha2 2
  have hc4 : (g 1 0) ^ 4 ≤ 16 := by
    simpa only [← pow_mul, show 2 * 2 = 4 from rfl, show (4 : ℝ) ^ 2 = 16 by norm_num]
      using pow_le_pow_left₀ (sq_nonneg _) hc2 2
  have hac : 4 * (g 1 0) ^ 2 * (g 0 0) ^ 2 ≤ 64 := by
    have h := mul_le_mul hc2 ha2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  unfold dyadicTransportConstant universalDyadicTransportConstant
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by nlinarith [ha4]) (dyadicFrequencyDerivativeBound_nonneg 0)
      · apply mul_le_mul_of_nonneg_right (by nlinarith [hc4])
        unfold dyadicFrequencyDerivativeBound
        positivity
    · exact mul_le_mul_of_nonneg_right hac (dyadicCutoffDerivativeBound_nonneg 0)
  · apply mul_le_mul_of_nonneg_right (by nlinarith [hc4])
    unfold dyadicCutoffDerivativeBound
    positivity

theorem inverse_entry_zero_zero (g : Group) : (g⁻¹) 0 0 = g 1 1 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

theorem inverse_entry_one_zero (g : Group) : (g⁻¹) 1 0 = -(g 1 0) := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  rfl

noncomputable def universalDyadicFarConstant : ℝ :=
  (2 / (2 * Real.pi)) * Real.sqrt universalDyadicTransportConstant *
    Real.sqrt (dyadicCutoffDerivativeBound 0)

theorem universalDyadicFarConstant_nonneg : 0 ≤ universalDyadicFarConstant := by
  unfold universalDyadicFarConstant
  positivity

theorem dyadicBand_upper_far_sum_le_universal (D M : ℕ) (indices : ℕ → Finset ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hs : ∀ᵐ x ∂volume, x ∉ Icc (0 : ℝ) 1 → f x = 0) (g : Group)
    (ha : |g 0 0| ≤ 2) (hc : |g 1 0| ≤ 2) :
    let u := fun k => smoothBand hf hs (dyadicAnnularCutoff k) (dyadicAnnularCutoff_hasCompactSupport k)
    (∑ r ∈ Finset.range M, ∑ j ∈ indices r,
      |inner ℝ (schwartzActionL2 g (u j)) ((u (j + (D + r))).toLp 2 volume)|) ≤
      ((2 : ℝ) ^ D)⁻¹ * universalDyadicFarConstant * ‖hf.toLp f‖ ^ 2 := by
  apply (dyadicBand_upper_far_sum_le D M indices hf hs g).trans
  have hC := Real.sqrt_le_sqrt (dyadicTransportConstant_le_universal g ha hc)
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC
      (Real.sqrt_nonneg (dyadicCutoffDerivativeBound 0)))
      (sq_nonneg ‖hf.toLp f‖))
    (by positivity : 0 ≤ 2 * ((2 : ℝ) ^ D)⁻¹ / (2 * Real.pi))
  convert h using 1
  unfold universalDyadicFarConstant
  ring

end TransposeFollowup.RealMobius
