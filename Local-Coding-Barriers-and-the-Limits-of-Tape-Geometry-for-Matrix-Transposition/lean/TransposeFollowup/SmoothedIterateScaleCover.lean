import TransposeFollowup.SmoothedIterateApproximate
import TransposeFollowup.SmoothedIterateEndpoint
import TransposeFollowup.MobiusSmoothingScaleCover

/-! An actual smoothing-scale finite cover of the approximate group
extracted from a nonflattening autocorrelation step. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_approximate_group_scale_cover
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
      ∃ (U : Set Group) (Y F : Finset Group) (x : Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        (F : Set Group) ⊆ U ∧ U ⊆ (F : Set Group) * mobiusIdentityBall (64 * Q ^ 2 * η) ∧
        (F.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          2 ^ 23 * K₀ * L ^ 2 * K ^ 20 * H U := by
  dsimp only
  let H : Measure Group := Measure.haar
  let f := smoothedAutocorrelationIterate μ η k
  let q := ENNReal.ofReal θ
  let R := (4 * B ^ 2) ^ (2 ^ k)
  let Q := 32 * (R + 1) ^ 6
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.mpr hθ).ne'
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ : 0 < Q := by dsimp only [Q, R]; positivity
  obtain ⟨N, hN, hlog, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass⟩ :=
    exists_smoothedIterate_approximate_group μ hη k hs hθ hC hnonflat
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let c := 512 * K ^ 16
  let Bc := 8192 * K₀ * L ^ 2 * K ^ 4
  let p := (H.withDensity f) (x • U)
  have hKt : K ≠ ⊤ := by dsimp only [K, L, K₀]; finiteness
  have hct : c ≠ ⊤ := by finiteness
  have hp0 : 0 < p := by
    by_contra hn
    have hz : p = 0 := le_antisymm (not_lt.mp hn) bot_le
    change q ^ 2 ≤ Bc * p at hmass
    rw [hz, mul_zero] at hmass
    exact (not_le_of_gt (by positivity : 0 < q ^ 2)) hmass
  have : IsProbabilityMeasure (H.withDensity f) := smoothedAutocorrelationIterate_probability μ hη k
  have hpone : p ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hpone
  obtain ⟨ν, hν, hend⟩ := smoothedAutocorrelationIterate_right_kernel μ hη k
  let : IsProbabilityMeasure ν := hν
  obtain ⟨F, hF, hcard, hcover⟩ := exists_finite_cover_of_smoothed_concentration ν hη hηone hQ
    hUo.measurableSet (fun _ hg => hUb (subset_closure hg)) hUt Y hct hYcard hYcov x hp0 hpt
    (by change (H.withDensity f) (x • U) ≤ _; rw [hend])
  refine ⟨N, hN, hlog, U, Y, F, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass, hF, hcover, ?_⟩
  calc
    (F.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
        (F.card : ℝ≥0∞) * (Bc * p) * H (mobiusIdentityBall η) :=
      mul_le_mul' (mul_le_mul' le_rfl hmass) le_rfl
    _ = Bc * ((F.card : ℝ≥0∞) * p * H (mobiusIdentityBall η)) := by ring
    _ ≤ Bc * (2 * c * H U) := mul_le_mul' le_rfl hcard
    _ = 2 ^ 23 * K₀ * L ^ 2 * K ^ 20 * H U := by dsimp only [Bc, c]; ring

end TransposeFollowup.RealMobius
