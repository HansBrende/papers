import TransposeFollowup.SmoothedIterateLocalizedCover
import TransposeFollowup.MobiusCoveringNumbers

/-! Native Frobenius covering numbers of the actual localized set and
its cube: finite positive size, small tripling, and two-sided quantitative
size control in terms of the actual squared-L2 mass. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_covering_profile
    (μ : Measure Group) [IsProbabilityMeasure μ] {η B α : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 32) (hα : 0 < α) (hαone : α ≤ 1) (k : ℕ)
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
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    let ι := fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
    0 < V ∧ V < ⊤ ∧
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
      let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
      ∃ (U : Set Group) (Y : Finset Group) (x : Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        let A := U ^ 2 ∩ mobiusIdentityBall α
        let nA : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, hη.le⟩ (ι '' A)
        let n₃ : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, hη.le⟩ (ι '' (A ^ 3))
        1 ∈ A ∧ IsOpen A ∧ A⁻¹ = A ∧ IsCompact (closure A) ∧
        closure A ⊆ matrixEntryBox 2 ∧ 0 < H A ∧ H A < ⊤ ∧ A ^ 3 ⊆ U ^ 6 ∧
        H U ≤ M * H A ∧ H A ≤ 512 * K ^ 16 * H U ∧
        q ≤ 128 * K₀ * K * L ^ 2 * M * V * H A ∧ q * V * H A ≤ 8192 * K₀ * K ^ 23 ∧
        0 < nA ∧ nA ≤ n₃ ∧ n₃ < ⊤ ∧
        n₃ * q ^ 2 ≤ 6561 * D * nA ∧
        q ≤ 128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M * V * nA * H (mobiusIdentityBall η) ∧
        nA * q ^ 3 * V * H (mobiusIdentityBall η) ≤ A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 := by
  dsimp only
  let H : Measure Group := Measure.haar
  let f := smoothedAutocorrelationIterate μ η k
  let V := ∫⁻ x, f x ^ 2 ∂H
  let q := ENNReal.ofReal θ
  let R := (4 * B ^ 2) ^ (2 ^ k)
  let Q := 32 * (R + 1) ^ 6
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  let ι := fun g : Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
  let r : ℝ≥0 := ⟨η, hη.le⟩
  have hr : 0 < r := hη
  have hV0 : V ≠ 0 := lintegral_sq_ne_zero_of_mass_ne_zero H
    (smoothedAutocorrelationIterate_measurable μ η k)
    (by rw [smoothedAutocorrelationIterate_lintegral μ hη k]; simp)
  have hVt : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (smoothedAutocorrelationIterate_lintegral_sq_le μ hη hC k)
  obtain ⟨N, hN, hlog, U, Y, E₆, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
      hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
      _, hcard₆, hclose₆, hcompare⟩ :=
    exists_smoothedIterate_localized_cube_cover μ hη hηsmall hα hαone k hs hθ hC hnonflat
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let A := U ^ 2 ∩ mobiusIdentityBall α
  let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
  let C₆ := (2 : ℝ≥0∞) ^ 68 * K₀ * L ^ 2 * K ^ 100
  let D := 393216 ^ 4 * A₆ * C₆ * M
  let nA : ℝ≥0∞ := Metric.externalCoveringNumber r (ι '' A)
  let n₃ : ℝ≥0∞ := Metric.externalCoveringNumber r (ι '' (A ^ 3))
  have hn₃ : n₃ ≤ (E₆.card : ℝ≥0∞) := externalCoveringNumber_le_finite_frobenius (η := r) E₆ hclose₆
  have hnA₃ : nA ≤ n₃ := ENat.toENNReal_mono
    (Metric.externalCoveringNumber_mono_set (Set.image_mono (Set.subset_pow hA1 (by decide : (3 : ℕ) ≠ 0))))
  have hn₃t : n₃ < ⊤ := hn₃.trans_lt (by finiteness)
  have hnAt : Metric.externalCoveringNumber r (ι '' A) ≠ ⊤ :=
    ENat.toENNReal_ne_top.mp (hnA₃.trans_lt hn₃t).ne
  have hnA0 : 0 < nA := by
    have hpos : 0 < Metric.externalCoveringNumber r (ι '' A) :=
      Metric.externalCoveringNumber_pos_iff.mpr ⟨ι 1, Set.mem_image_of_mem ι hA1⟩
    simpa only [ENat.toENNReal_zero, nA] using ENat.toENNReal_strictMono hpos
  have hcost : (E₆.card : ℝ≥0∞) * q ^ 2 ≤ 6561 * D * nA :=
    strict_cover_cost_le_externalCoveringNumber hr hnAt (fun F hF => hcompare F
      (fun g hg => hF (ι g) (Set.mem_image_of_mem ι hg)))
  have hvolume : H A ≤ 6561 * 393216 ^ 4 * nA * H (mobiusIdentityBall η) :=
    haar_le_externalCoveringNumber hr hηsmall (fun _ hg => hAb (subset_closure hg)) hnAt
  refine ⟨pos_iff_ne_zero.mpr hV0, lt_top_iff_ne_top.mpr hVt, N, hN, hlog,
    U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt, hYs, hYi, hYcard, hYcov, happrox,
    hx, hVlo, hVhi, hmass, hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3,
    hHlo, hHhi, hVAlo, hVAhi, hnA0, hnA₃, hn₃t, (mul_le_mul' hn₃ le_rfl).trans hcost, ?_, ?_⟩
  · calc
      q ≤ 128 * K₀ * K * L ^ 2 * M * V * H A := hVAlo
      _ ≤ 128 * K₀ * K * L ^ 2 * M * V *
          (6561 * 393216 ^ 4 * nA * H (mobiusIdentityBall η)) := mul_le_mul' le_rfl hvolume
      _ = _ := by ring
  · calc
      nA * q ^ 3 * V * H (mobiusIdentityBall η) ≤
          (E₆.card : ℝ≥0∞) * q ^ 3 * V * H (mobiusIdentityBall η) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' (hnA₃.trans hn₃) le_rfl) le_rfl) le_rfl
      _ = (q * V) * ((E₆.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η)) := by ring
      _ ≤ (q * V) * (A₆ * (C₆ * H U)) := mul_le_mul' le_rfl hcard₆
      _ = A₆ * C₆ * (q * V * H U) := by ring
      _ ≤ A₆ * C₆ * (16 * K ^ 7 * K₀) := mul_le_mul' le_rfl hVhi
      _ = _ := by dsimp only [C₆]; ring

end TransposeFollowup.RealMobius
