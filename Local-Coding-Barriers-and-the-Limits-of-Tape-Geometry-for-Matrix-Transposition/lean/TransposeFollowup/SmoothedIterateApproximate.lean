import TransposeFollowup.SmoothedIterateSelfEnergy
import TransposeFollowup.AutocorrelationIterateCoefficient
import TransposeFollowup.MobiusMeasurableApproximate

/-! Failure to flatten the actual smoothed autocorrelation density
produces an approximate group carrying quantitatively positive probability.
All regularization and covering witnesses are constructed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_approximate_group
    (μ : Measure Group) [IsProbabilityMeasure μ] {η B : ℝ} (hη : 0 < η) (k : ℕ)
    (hs : ∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B)
    {C θ : ℝ} (hθ : 0 < θ) (hC : ∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal θ *
        (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group)) ≤
      ∫⁻ x, smoothedAutocorrelationIterate μ η (k + 1) x ^ 2 ∂(Measure.haar : Measure Group)) :
    let H : Measure Group := Measure.haar
    let f := smoothedAutocorrelationIterate μ η k
    let V := ∫⁻ x, f x ^ 2 ∂H
    let q := ENNReal.ofReal θ
    let R := (4 * B ^ 2) ^ (2 ^ k)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      ∃ (U : Set Group) (Y : Finset Group) (x : Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox (32 * (R + 1) ^ 6) ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) := by
  dsimp only
  let H : Measure Group := Measure.haar
  let f := smoothedAutocorrelationIterate μ η k
  let V := ∫⁻ x, f x ^ 2 ∂H
  let q := ENNReal.ofReal θ
  let a := ENNReal.ofReal (θ * V.toReal / 16)
  let R := (4 * B ^ 2) ^ (2 ^ k)
  have hf : Measurable f := smoothedAutocorrelationIterate_measurable μ η k
  have hV0 : V ≠ 0 := lintegral_sq_ne_zero_of_mass_ne_zero H hf
    (by rw [smoothedAutocorrelationIterate_lintegral μ hη k]; simp)
  have hVt : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (smoothedAutocorrelationIterate_lintegral_sq_le μ hη hC k)
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.mpr hθ).ne'
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha : 0 < a := ENNReal.ofReal_pos.mpr
    (div_pos (mul_pos hθ (ENNReal.toReal_pos hV0 hVt)) (by norm_num))
  obtain ⟨N, hN, hlog, i, _, hD, hDs, hD0, hDt, hlo, hhi, he⟩ :=
    exists_smoothedIterate_nonflattening_self_energy μ hη k hθ hC hnonflat
  let D := dyadicDensityLevel f a i
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L₀ := K₀ ^ 2 / q ^ 2
  let L := 8 * L₀
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  have hL₀t : L₀ ≠ ⊤ := by dsimp only [L₀, K₀]; finiteness
  have hcancel : q ^ 2 * L₀ = K₀ ^ 2 :=
    ENNReal.mul_div_cancel (pow_ne_zero 2 hq0) (by finiteness)
  have hratio : H D ^ 3 ≤ L₀ * haarMultiplicativeEnergy H D D := by
    apply (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hq0) (by finiteness)).mp
    calc
      q ^ 2 * H D ^ 3 ≤ K₀ ^ 2 * haarMultiplicativeEnergy H D D := he
      _ = q ^ 2 * (L₀ * haarMultiplicativeEnergy H D D) := by rw [← mul_assoc, hcancel]
  have hL₀one : 1 ≤ L₀ := by
    apply (ENNReal.mul_le_mul_iff_left (pow_ne_zero 3 hD0.ne') (by finiteness)).mp
    calc
      1 * H D ^ 3 = H D ^ 3 := one_mul _
      _ ≤ L₀ * haarMultiplicativeEnergy H D D := hratio
      _ ≤ L₀ * H D ^ 3 := mul_le_mul' le_rfl (by
        calc
          haarMultiplicativeEnergy H D D ≤ H D ^ 2 * H D := haarMultiplicativeEnergy_le_left H hD hD
          _ = H D ^ 3 := by ring)
  have hae : (D ∩ matrixEntryBox R) =ᵐ[H] D := dyadicDensityLevel_inter_support_ae H
    (smoothedAutocorrelationIterate_ae_zero_outside μ hη hs k) ha i
  obtain ⟨U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt, hUlo, hUhi,
      hYs, hYi, hYcard, hYcov, happrox, hx, hover⟩ :=
    exists_approximate_group_from_measurable_self_energy hD hDs hae hD0 hDt hL₀one hL₀t hratio
  have haeq : a = q * V / 16 := by
    dsimp only [a, q]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16),
      ENNReal.ofReal_mul hθ.le, ENNReal.ofReal_toReal hVt, ENNReal.ofReal_ofNat]
  have h16a : 16 * a = q * V := by
    rw [haeq]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hmass : a * H (D ∩ x • U) ≤ (H.withDensity f) (x • U) := by
    rw [withDensity_apply _ (hUo.measurableSet.const_smul x)]
    have hd := dyadicDensityLevel_mass_le (H.restrict (x • U)) hf a i
    rw [Measure.restrict_apply hD] at hd
    apply le_trans _ hd
    apply mul_le_mul' _ le_rfl
    calc
      a = a * 1 := (mul_one _).symm
      _ ≤ a * 2 ^ i := mul_le_mul' le_rfl (one_le_pow₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  refine ⟨N, hN, hlog, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, ?_, ?_, ?_⟩
  · calc
      q ≤ K₀ * V * H D := hlo
      _ ≤ K₀ * V * (128 * K * L ^ 2 * H U) := mul_le_mul' le_rfl hUlo
      _ = _ := by ring
  · calc
      q * V * H U ≤ q * V * (16 * K ^ 7 * H D) := mul_le_mul' le_rfl hUhi
      _ = 16 * K ^ 7 * (q * V * H D) := by ring
      _ ≤ 16 * K ^ 7 * K₀ := mul_le_mul' le_rfl hhi
  · calc
      q ^ 2 = q * q := pow_two _
      _ ≤ q * (K₀ * V * H D) := mul_le_mul' le_rfl hlo
      _ = K₀ * (q * V) * H D := by ring
      _ = 16 * K₀ * a * H D := by rw [← h16a]; ring
      _ ≤ 16 * K₀ * a * (512 * L ^ 2 * K ^ 4 * H (D ∩ x • U)) := mul_le_mul' le_rfl hover
      _ = (8192 * K₀ * L ^ 2 * K ^ 4) * (a * H (D ∩ x • U)) := by ring
      _ ≤ (8192 * K₀ * L ^ 2 * K ^ 4) * (H.withDensity f) (x • U) := mul_le_mul' le_rfl hmass

end TransposeFollowup.RealMobius
