import TransposeFollowup.SmoothedIterateFrobeniusCover
import TransposeFollowup.MobiusNearIdentityLocalization
import TransposeFollowup.MobiusFrobeniusCoverVolume

/-! Actual nonflattening produces a symmetric near-identity set whose
cube has a finite ordinary Frobenius cover quantitatively comparable to
every such cover of the set itself. All witnesses and losses are explicit. -/
namespace TransposeFollowup.RealMobius
open Classical MeasureTheory Set
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace Group] [BorelSpace Group]

theorem exists_smoothedIterate_localized_cube_cover
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
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      let D := 393216 ^ 4 * ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52) *
        (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
      ∃ (U : Set Group) (Y E₆ : Finset Group) (x : Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set Group) ⊆ U ^ 2 ∧ (Y : Set Group)⁻¹ = (Y : Set Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        let A := U ^ 2 ∩ mobiusIdentityBall α
        1 ∈ A ∧ IsOpen A ∧ A⁻¹ = A ∧ IsCompact (closure A) ∧
        closure A ⊆ matrixEntryBox 2 ∧ 0 < H A ∧ H A < ⊤ ∧ A ^ 3 ⊆ U ^ 6 ∧
        H U ≤ M * H A ∧ H A ≤ 512 * K ^ 16 * H U ∧
        q ≤ 128 * K₀ * K * L ^ 2 * M * V * H A ∧ q * V * H A ≤ 8192 * K₀ * K ^ 23 ∧
        (E₆ : Set Group) ⊆ U ^ 6 ∧
        (E₆.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤
          ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52) * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100 * H U) ∧
        (∀ g ∈ A ^ 3, ∃ e ∈ E₆, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) ∧
        ∀ F : Finset (Matrix (Fin 2) (Fin 2) ℝ),
          (∀ g ∈ A, ∃ e ∈ F, (∑ i : Fin 2, ∑ j : Fin 2, (g i j - e i j) ^ 2) < η ^ 2) →
          (E₆.card : ℝ≥0∞) * q ^ 2 ≤ D * (F.card : ℝ≥0∞) := by
  dsimp only
  let H : Measure Group := Measure.haar
  let q := ENNReal.ofReal θ
  let R := (4 * B ^ 2) ^ (2 ^ k)
  let Q := 32 * (R + 1) ^ 6
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 1 ≤ Q := by
    have hh : 1 ≤ (R + 1) ^ 6 := one_le_pow₀ (by linarith)
    calc
      (1 : ℝ) ≤ 32 * 1 := by norm_num
      _ ≤ 32 * (R + 1) ^ 6 := mul_le_mul_of_nonneg_left hh (by norm_num)
  obtain ⟨N, hN, hlog, U, Y, E, E₆, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
      _, _, _, hE₆, hclose₆, hcard₆⟩ :=
    exists_smoothedIterate_frobenius_covers μ hη (by linarith) k hs hθ hC hnonflat
  let K₀ := 64 * (N : ℝ≥0∞) ^ 4
  let L := 8 * (K₀ ^ 2 / q ^ 2)
  let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
  let A := U ^ 2 ∩ mobiusIdentityBall α
  let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
  let C₆ := (2 : ℝ≥0∞) ^ 68 * K₀ * L ^ 2 * K ^ 100
  let D := 393216 ^ 4 * A₆ * C₆ * M
  obtain ⟨hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3⟩ :=
    near_identity_square_geometry hU1 hUo hUi hα hαone
  obtain ⟨hHlo, hHhi⟩ := near_identity_square_volume_bounds Y hQ hα hαone
    (fun _ hg => hUb (subset_closure hg)) hUi hYcov
  have hHhi' : H A ≤ 512 * K ^ 16 * H U := hHhi.trans (mul_le_mul' hYcard le_rfl)
  refine ⟨N, hN, hlog, U, Y, E₆, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
    hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi', ?_, ?_, hE₆, hcard₆, ?_, ?_⟩
  · calc
      q ≤ 128 * K₀ * K * L ^ 2 * (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂H) * H U := hVlo
      _ ≤ 128 * K₀ * K * L ^ 2 * (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂H) * (M * H A) :=
        mul_le_mul' le_rfl hHlo
      _ = _ := by ring
  · calc
      q * (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂H) * H A ≤
          q * (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂H) * (512 * K ^ 16 * H U) :=
        mul_le_mul' le_rfl hHhi'
      _ = 512 * K ^ 16 * (q * (∫⁻ x, smoothedAutocorrelationIterate μ η k x ^ 2 ∂H) * H U) := by ring
      _ ≤ 512 * K ^ 16 * (16 * K ^ 7 * K₀) := mul_le_mul' le_rfl hVhi
      _ = _ := by ring
  · intro g hg
    obtain ⟨e, he, _, heclose⟩ := hclose₆ g (hA3 hg)
    exact ⟨e, he, heclose⟩
  · intro F hF
    have hvol := haar_le_frobenius_cover_card_at_scale F hη hηsmall
      (fun _ hg => hAb (subset_closure hg)) hF
    apply (ENNReal.mul_le_mul_iff_left (mobiusIdentityBall_haar_pos hη).ne'
      (mobiusIdentityBall_haar_lt_top hη).ne).mp
    calc
      (E₆.card : ℝ≥0∞) * q ^ 2 * H (mobiusIdentityBall η) ≤ A₆ * (C₆ * H U) := hcard₆
      _ ≤ A₆ * (C₆ * (M * H A)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hHlo)
      _ ≤ A₆ * (C₆ * (M * (393216 ^ 4 * (F.card : ℝ≥0∞) * H (mobiusIdentityBall η)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hvol))
      _ = (D * (F.card : ℝ≥0∞)) * H (mobiusIdentityBall η) := by dsimp only [D]; ring

end TransposeFollowup.RealMobius
