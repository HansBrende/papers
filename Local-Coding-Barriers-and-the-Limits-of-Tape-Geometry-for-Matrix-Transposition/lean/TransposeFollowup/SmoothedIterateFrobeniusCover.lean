import TransposeFollowup.SmoothedIterateScaleCover
import TransposeFollowup.MobiusApproximateRefinement

/-! Actual ordinary-radius covers of the nonflattening approximate group
and its sixth power, retaining the cubic Haar-ball scale factor. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_frobenius_covers
    (μ : Measure Group) [IsProbabilityMeasure μ] {η B : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (k : ℕ)
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
    let Q := 32 * (R + 1) ^ 6
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      ∃ (U : Set Group) (Y E E₆ : Finset Group) (x : Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        (E : Set Group) ⊆ U ∧
        (∀ g ∈ U, ∃ e ∈ E, (∀ i j, |g i j - e i j| < η / 4) ∧
          (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) ∧
        (E.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          ENNReal.ofReal (1025 ^ 4 * Q ^ 12) * (2 ^ 23 * K₀ * L ^ 2 * K ^ 20 * H U) ∧
        (E₆ : Set Group) ⊆ U ^ 6 ∧
        (∀ g ∈ U ^ 6, ∃ e ∈ E₆, (∀ i j, |g i j - e i j| < η / 4) ∧
          (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) ∧
        (E₆.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52) * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100 * H U) := by
  dsimp only
  let H : Measure Group := Measure.haar
  let q := ENNReal.ofReal θ
  let R := (4 * B ^ 2) ^ (2 ^ k)
  let Q := 32 * (R + 1) ^ 6
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 1 ≤ Q := by
    have hh : 1 ≤ (R + 1) ^ 6 := one_le_pow₀ (by linarith)
    calc
      (1 : ℝ) ≤ 32 * 1 := by norm_num
      _ ≤ 32 * (R + 1) ^ 6 := mul_le_mul_of_nonneg_left hh (by norm_num)
  obtain ⟨N, hN, hlog, U, Y, F, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass, hF, hcover, hFcard⟩ :=
    exists_smoothedIterate_approximate_group_scale_cover μ hη hηone k hs hθ hC hnonflat
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let A₁ := ENNReal.ofReal (1025 ^ 4 * Q ^ 12)
  let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
  obtain ⟨E, E₆, hE, hEcard, hEclose, hE₆, hE₆card, hE₆close⟩ :=
    exists_frobenius_covers_of_approximate_cover Y F hQ hη
      (fun _ hg => hUb (subset_closure hg)) hYs hF hYcov hcover
  refine ⟨N, hN, hlog, U, Y, E, E₆, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass, hE, hEclose, ?_, hE₆, hE₆close, ?_⟩
  · calc
      (E.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          ((F.card : ℝ≥0∞) * A₁) * q ^ 2 * H (mobiusIdentityBall η) :=
        mul_le_mul' (mul_le_mul' hEcard le_rfl) le_rfl
      _ = A₁ * ((F.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η)) := by ring
      _ ≤ A₁ * (2 ^ 23 * K₀ * L ^ 2 * K ^ 20 * H U) := mul_le_mul' le_rfl hFcard
  · calc
      (E₆.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          ((Y.card : ℝ≥0∞) ^ 5 * (F.card : ℝ≥0∞) * A₆) * q ^ 2 * H (mobiusIdentityBall η) :=
        mul_le_mul' (mul_le_mul' hE₆card le_rfl) le_rfl
      _ = A₆ * (Y.card : ℝ≥0∞) ^ 5 * ((F.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η)) := by ring
      _ ≤ A₆ * (512 * K ^ 16) ^ 5 * (2 ^ 23 * K₀ * L ^ 2 * K ^ 20 * H U) :=
        mul_le_mul' (mul_le_mul' le_rfl (pow_le_pow_left' hYcard 5)) hFcard
      _ = A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100 * H U) := by ring

end TransposeFollowup.RealMobius
