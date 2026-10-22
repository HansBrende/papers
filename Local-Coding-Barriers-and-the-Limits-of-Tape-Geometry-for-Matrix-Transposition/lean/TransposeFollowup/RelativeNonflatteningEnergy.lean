import TransposeFollowup.LevelEnergyNormalization
import TransposeFollowup.HaarSetEnergyBounds

/-! Nonflattening yields positive finite level sets with large energy
relative to both volume products, and quantitatively comparable volumes. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
open scoped ENNReal
set_option autoImplicit false

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]

theorem exists_relative_nonflattening_level_pair (σ : Measure H) [SFinite σ]
    [Measure.IsMulLeftInvariant σ] [Measure.IsMulRightInvariant σ] [Measure.IsInvInvariant σ]
    {f : H → ℝ≥0∞} (hf : Measurable f) (hm : (∫⁻ x, f x ∂σ) = 1)
    {C θ : ℝ} (hθ : 0 < θ) (hC : ∀ x, f x ≤ ENNReal.ofReal C)
    (hnonflat : ENNReal.ofReal θ * (∫⁻ x, f x ^ 2 ∂σ) ≤
      ∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ) :
    let U := ∫⁻ x, f x ^ 2 ∂σ
    let τ := θ * U.toReal
    let a := ENNReal.ofReal (τ / 16)
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / τ)) ∧
      ∃ i < N, ∃ j < N,
        let A := dyadicDensityLevel f a i
        let B := dyadicDensityLevel f a j
        0 < σ A ∧ σ A < ⊤ ∧ 0 < σ B ∧ σ B < ⊤ ∧
        ENNReal.ofReal θ * σ A ^ 2 * σ B ≤ 64 * (N : ℝ≥0∞) ^ 4 * haarMultiplicativeEnergy σ A B ∧
        ENNReal.ofReal θ * σ A * σ B ^ 2 ≤ 64 * (N : ℝ≥0∞) ^ 4 * haarMultiplicativeEnergy σ A B ∧
        ENNReal.ofReal θ * σ A ≤ 64 * (N : ℝ≥0∞) ^ 4 * σ B ∧
        ENNReal.ofReal θ * σ B ≤ 64 * (N : ℝ≥0∞) ^ 4 * σ A ∧
        ENNReal.ofReal θ ≤ 64 * (N : ℝ≥0∞) ^ 4 * U * σ A ∧
        ENNReal.ofReal θ * U * σ A ≤ 64 * (N : ℝ≥0∞) ^ 4 ∧
        ENNReal.ofReal θ ≤ 64 * (N : ℝ≥0∞) ^ 4 * U * σ B ∧
        ENNReal.ofReal θ * U * σ B ≤ 64 * (N : ℝ≥0∞) ^ 4 := by
  let U := ∫⁻ x, f x ^ 2 ∂σ
  have hU0 : U ≠ 0 := lintegral_sq_ne_zero_of_mass_ne_zero σ hf (by rw [hm]; exact one_ne_zero)
  have hUb : U ≤ ENNReal.ofReal C := by
    simpa only [hm, mul_one] using lintegral_sq_le_bound_mul_lintegral σ hf hC
  have hUt : U ≠ ⊤ := (hUb.trans_lt ENNReal.ofReal_lt_top).ne
  let τ := θ * U.toReal
  have hτ : 0 < τ := mul_pos hθ (ENNReal.toReal_pos hU0 hUt)
  have hτeq : ENNReal.ofReal τ = ENNReal.ofReal θ * U := by
    rw [ENNReal.ofReal_mul hθ.le, ENNReal.ofReal_toReal hUt]
  let a := ENNReal.ofReal (τ / 16)
  have ha : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by dsimp [τ]; positivity)).ne'
  have hnonflat' : ENNReal.ofReal τ ≤ ∫⁻ x, densityConvolution σ f f x ^ 2 ∂σ := by
    rw [hτeq]
    exact hnonflat
  obtain ⟨N, hN, hlog, i, hi, j, hj, hE⟩ := exists_nonflattening_level_pair σ hf hm.le hτ hC hnonflat'
  let A := dyadicDensityLevel f a i
  let B := dyadicDensityLevel f a j
  have hA : MeasurableSet A := dyadicDensityLevel_measurableSet hf a i
  have hB : MeasurableSet B := dyadicDensityLevel_measurableSet hf a j
  have hAt : σ A < ⊤ := dyadicDensityLevel_measure_lt_top σ hf (by rw [hm]; simp) ha i
  have hBt : σ B < ⊤ := dyadicDensityLevel_measure_lt_top σ hf (by rw [hm]; simp) ha j
  have hEp : 0 < haarMultiplicativeEnergy σ A B := by
    by_contra hn
    have hz : haarMultiplicativeEnergy σ A B = 0 := le_antisymm (le_of_not_gt hn) zero_le
    change ENNReal.ofReal τ ≤ _ * haarMultiplicativeEnergy σ A B at hE
    rw [hz, mul_zero] at hE
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hτ)) hE
  obtain ⟨hA0, hB0⟩ := haarMultiplicativeEnergy_pos_measures σ hA hB hEp
  have hw : ENNReal.ofReal θ * U ≤ (64 * (N : ℝ≥0∞) ^ 4) *
      (a * 2 ^ i) ^ 2 * (a * 2 ^ j) ^ 2 * haarMultiplicativeEnergy σ A B := by
    calc
      _ = ENNReal.ofReal τ := hτeq.symm
      _ ≤ 4 * (N : ℝ≥0∞) ^ 4 * ((a * 2 ^ (i + 1)) * (a * 2 ^ (j + 1))) ^ 2 *
          haarMultiplicativeEnergy σ A B := hE
      _ = _ := by rw [pow_succ (2 : ℝ≥0∞) i, pow_succ (2 : ℝ≥0∞) j]; ring
  have hrel := normalize_weighted_pair_energy hU0 hUt
    ((dyadicDensityLevel_mass_le σ hf a i).trans hm.le)
    ((dyadicDensityLevel_mass_le σ hf a j).trans hm.le)
    (dyadicDensityLevel_second_moment_le σ hf a i)
    (dyadicDensityLevel_second_moment_le σ hf a j) hw
  have hcomp := haarMultiplicativeEnergy_volume_comparable σ hA hB hA0.ne' hB0.ne' hAt.ne hBt.ne hrel.1 hrel.2
  have hwinA := weighted_pair_volume_window_left hU0 hUt
    ((dyadicDensityLevel_mass_le σ hf a i).trans hm.le)
    ((dyadicDensityLevel_mass_le σ hf a j).trans hm.le)
    (dyadicDensityLevel_second_moment_le σ hf a i)
    (dyadicDensityLevel_second_moment_le σ hf a j) hw
    (haarMultiplicativeEnergy_le_left σ hA hB) (haarMultiplicativeEnergy_le_right σ hA hB)
  have hw' : ENNReal.ofReal θ * U ≤ (64 * (N : ℝ≥0∞) ^ 4) *
      (a * 2 ^ j) ^ 2 * (a * 2 ^ i) ^ 2 * haarMultiplicativeEnergy σ A B := by
    convert hw using 1
    ring
  have hwinB := weighted_pair_volume_window_left hU0 hUt
    ((dyadicDensityLevel_mass_le σ hf a j).trans hm.le)
    ((dyadicDensityLevel_mass_le σ hf a i).trans hm.le)
    (dyadicDensityLevel_second_moment_le σ hf a j)
    (dyadicDensityLevel_second_moment_le σ hf a i) hw'
    (show haarMultiplicativeEnergy σ A B ≤ σ B ^ 2 * σ A by
      simpa only [mul_comm] using haarMultiplicativeEnergy_le_right σ hA hB)
    (show haarMultiplicativeEnergy σ A B ≤ σ B * σ A ^ 2 by
      simpa only [mul_comm] using haarMultiplicativeEnergy_le_left σ hA hB)
  exact ⟨N, hN, hlog, i, hi, j, hj, hA0, hAt, hB0, hBt, hrel.1, hrel.2, hcomp.1, hcomp.2,
    hwinA.1, hwinA.2, hwinB.1, hwinB.2⟩

end TransposeFollowup
