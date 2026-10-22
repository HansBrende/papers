import TransposeFollowup.SmoothedIterateCoveringProfile
import TransposeFollowup.MobiusCoveringPowerBounds
import TransposeFollowup.CoveringLevelScale
import TransposeFollowup.CoveringSizeInterval

/-! A single scale threshold gives intermediate size and small tripling
for the actual nonflattening witness. Support growth is an explicit
hypothesis; no distribution, escape, or product theorem is assumed. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_uniform_smoothedIterate_covering_interval {α s κ γ β : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hs : 0 < s) (hsone : s ≤ 1)
    (hsk : 30000 * s ≤ κ / 2) (hsg : 30000 * s ≤ γ / 2) (hsb : 30000 * s ≤ β) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 32 ∧
    ∀ (μ : Measure Group) [IsProbabilityMeasure μ] {η B C : ℝ}
      (hη : 0 < η), η ≤ η₀ → ∀ k : ℕ,
      (∀ᵐ g ∂μ ∗ₘ mobiusHaarKernel η, g ∈ matrixEntryBox B) →
      (∀ x, mobiusSmoothedDensity μ η x ≤ ENNReal.ofReal C) →
      C ≤ η ^ (-3 + κ) →
      ENNReal.ofReal (η ^ (-γ)) ≤
        (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group)) →
      32 * ((4 * B ^ 2) ^ (2 ^ k) + 1) ^ 6 ≤ η ^ (-s) →
      ENNReal.ofReal (η ^ s) *
        (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂(Measure.haar : Measure Group)) ≤
        (∫⁻ x, smoothedAutocorrelationIterate μ η (k + 1) x ^ 2 ∂(Measure.haar : Measure Group)) →
    let θ := η ^ s
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
        nA * q ^ 3 * V * H (mobiusIdentityBall η) ≤ A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 ∧
        η ^ (-κ / 2) ≤ nA.toReal ∧ nA.toReal ≤ η ^ (-3 + γ / 2) ∧
        n₃.toReal ≤ η ^ (-β) * nA.toReal := by
  let c : ℝ := Measure.haarScalarFactor Measure.haar columnChartMeasure
  obtain ⟨η₁, hη₁, _, hscale⟩ := exists_uniform_covering_loss_threshold hs
    (max ((2 : ℝ) ^ 100) (max (α⁻¹ ^ 4) (max c c⁻¹)))
  refine ⟨min η₁ (1 / 32), lt_min hη₁ (by norm_num), min_le_right _ _, ?_⟩
  intro μ hμ η B C hη hsmall k hsupport hC hCpower henergy hQ hnonflat
  dsimp only
  let θ := η ^ s
  let h := η ^ (-s)
  let H : Measure Group := Measure.haar
  let f := smoothedAutocorrelationIterate μ η k
  let V := ∫⁻ x, f x ^ 2 ∂H
  let R := (4 * B ^ 2) ^ (2 ^ k)
  let Q := 32 * (R + 1) ^ 6
  have hηsmall : η ≤ 1 / 32 := hsmall.trans (min_le_right _ _)
  have hηhalf : η ≤ 1 / 2 := by linarith
  have hηone : η ≤ 1 := by linarith
  have hθ : 0 < θ := Real.rpow_pos_of_pos hη _
  have hθinv : θ⁻¹ ≤ h := le_of_eq (Real.rpow_neg hη.le s).symm
  obtain ⟨hconst, hlogscale⟩ := hscale η hη (hsmall.trans (min_le_left _ _))
  have hlarge : (2 : ℝ) ^ 100 ≤ h := (le_max_left _ _).trans hconst
  have hαinv : α⁻¹ ^ 4 ≤ h := (le_max_left _ _).trans ((le_max_right _ _).trans hconst)
  have hc : c ≤ h := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hconst))
  have hci : c⁻¹ ≤ h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hconst))
  obtain ⟨hV0, hVt, N, hN, hlog, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
      hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
      hnA0, hnA3, hn3t, htrip, hlo, hhi⟩ :=
    exists_smoothedIterate_covering_profile μ hη hηsmall hα hαone k hsupport hθ hC hnonflat
  have hVpower : V.toReal ≤ η ^ (-3 + κ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((smoothedAutocorrelationIterate_lintegral_sq_le μ hη hC k).trans
        (ENNReal.ofReal_le_ofReal hCpower))
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hη.le _)] using hh
  have hVpowerlo : η ^ (-γ) ≤ V.toReal := by
    have hh := ENNReal.toReal_mono hVt.ne henergy
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hη.le _)] using hh
  have hNscale : (N : ℝ) ≤ h :=
    (covering_level_log_bound_of_powers hη hηhalf hsone (by linarith : 0 ≤ κ)
      (by linarith : 0 ≤ γ) hCpower hVpowerlo hlog).trans hlogscale
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  obtain ⟨ht, hl, hu⟩ := covering_profile_power_bounds hη hηhalf hlarge hNscale hQ0 hQ
    hα hαinv hθ hθinv hc hci (hnA3.trans_lt hn3t).ne hVt.ne htrip hlo hhi
  have he : h ^ 30000 = η ^ (-(30000 * s)) := by
    dsimp only [h]
    rw [← Real.rpow_mul_natCast hη.le]
    congr 1
    norm_num
    ring
  rw [he] at ht hl hu
  obtain ⟨hsizeLo, hsizeHi, hsmalltrip⟩ := covering_envelope_size_interval hη hηone
    ENNReal.toReal_nonneg hsk hsg hsb hVpowerlo hVpower ht hl hu
  exact ⟨hV0, hVt, N, hN, hlog, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
    hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
    hnA0, hnA3, hn3t, htrip, hlo, hhi, hsizeLo, hsizeHi, hsmalltrip⟩

end TransposeFollowup.RealMobius
