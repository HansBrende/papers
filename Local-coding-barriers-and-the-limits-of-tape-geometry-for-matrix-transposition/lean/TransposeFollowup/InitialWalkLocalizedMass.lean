import TransposeFollowup.InitialWalkCoveringInterval
import TransposeFollowup.SmoothedIterateLocalizedMass

/-! A single actual localized witness has the covering-number profile
and quantitative short-walk concentration at every smaller walk length.
The exponent, iteration, and scale quantifiers keep their proved order. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise Matrix.Norms.Frobenius
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_initial_walk_localized_mass {α γ β : ℝ}
    (hα : 0 < α) (hαone : α ≤ 1) (hγ : 0 < γ) (hβ : 0 < β) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ 30000 * s ≤ (1 / 61440 : ℝ) / 2 ∧
      30000 * s ≤ γ / 2 ∧ 30000 * s ≤ β ∧
    ∀ k : ℕ, ∃ N₀ J₀ : ℕ, 0 < N₀ ∧
    ∀ r : ℕ, 5 ≤ r → ∃ g : Fin (2 ^ (3 * r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2 ^ (3 * r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2 ^ (3 * r) ∧
      (∀ t, HasDenominator (dyadicDenominator r) (g t) ∧
        realEmbedding (g t) ∈ mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g t))⁻¹ ∈ mobiusIdentityBall (dyadicRadius r)) ∧
    ∀ N j ell i : ℕ, N₀ ≤ N → max J₀ (7680 * r) ≤ j → 2 * N * ell ≤ j →
      Real.log (1 / (1 / 4 : ℝ) ^ j) / Real.log (1 / dyadicRadius r) < (ell : ℝ) → i ≤ k →
    let η := (1 / 4 : ℝ) ^ j
    let μ := generatorWalkMeasure (realEmbedding ∘ g) ell
    let B := 4 * (4 : ℝ) ^ ell
    let C := η ^ (-3 + 1 / 61440 : ℝ)
    ENNReal.ofReal (η ^ (-γ)) ≤
      (∫⁻ x, smoothedAutocorrelationIterate μ η i x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) →
    ENNReal.ofReal (η ^ s) *
      (∫⁻ x, smoothedAutocorrelationIterate μ η i x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) ≤
      (∫⁻ x, smoothedAutocorrelationIterate μ η (i + 1) x ^ 2 ∂(Measure.haar : Measure RealMobius.Group)) →
    let θ := η ^ s
    let H : Measure RealMobius.Group := Measure.haar
    let f := smoothedAutocorrelationIterate μ η i
    let V := ∫⁻ x, f x ^ 2 ∂H
    let q := ENNReal.ofReal θ
    let R := (4 * B ^ 2) ^ (2 ^ i)
    let Q := 32 * (R + 1) ^ 6
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    let ι := fun g : RealMobius.Group => (g : Matrix (Fin 2) (Fin 2) ℝ)
    0 < V ∧ V < ⊤ ∧
    ∃ N_level : ℕ, 0 < N_level ∧ (N_level : ℝ) ≤ 1 + Real.logb 2 (max 1 (16 * C / (θ * V.toReal))) ∧
      let K₀ := 64 * (N_level : ℝ≥0∞) ^ 4
      let L := 8 * (K₀ ^ 2 / q ^ 2)
      let K := (2 : ℝ≥0∞) ^ 55 * L ^ 21
      let A₆ := ENNReal.ofReal ((2 ^ 21 + 1) ^ 4 * Q ^ 52)
      let D := 393216 ^ 4 * A₆ * (2 ^ 68 * K₀ * L ^ 2 * K ^ 100) * M
      ∃ (U : Set RealMobius.Group) (Y : Finset RealMobius.Group) (x : RealMobius.Group),
        1 ∈ U ∧ IsOpen U ∧ U⁻¹ = U ∧ IsCompact (closure U) ∧
        closure U ⊆ matrixEntryBox Q ∧ 0 < H U ∧ H U < ⊤ ∧
        (Y : Set RealMobius.Group) ⊆ U ^ 2 ∧ (Y : Set RealMobius.Group)⁻¹ = (Y : Set RealMobius.Group) ∧
        (Y.card : ℝ≥0∞) ≤ 512 * K ^ 16 ∧ U ^ 2 ⊆ (Y : Set RealMobius.Group) * U ∧
        IsApproximateSubgroup (512 * K ^ 16).toReal U ∧ x ∈ matrixEntryBox (R + 1) ∧
        q ≤ 128 * K₀ * K * L ^ 2 * V * H U ∧ q * V * H U ≤ 16 * K ^ 7 * K₀ ∧
        q ^ 2 ≤ 8192 * K₀ * L ^ 2 * K ^ 4 * (H.withDensity f) (x • U) ∧
        let A := U ^ 2 ∩ mobiusIdentityBall α
        let nA : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, (by positivity : 0 ≤ η)⟩ (ι '' A)
        let n₃ : ℝ≥0∞ := Metric.externalCoveringNumber ⟨η, (by positivity : 0 ≤ η)⟩ (ι '' (A ^ 3))
        1 ∈ A ∧ IsOpen A ∧ A⁻¹ = A ∧ IsCompact (closure A) ∧
        closure A ⊆ matrixEntryBox 2 ∧ 0 < H A ∧ H A < ⊤ ∧ A ^ 3 ⊆ U ^ 6 ∧
        H U ≤ M * H A ∧ H A ≤ 512 * K ^ 16 * H U ∧
        q ≤ 128 * K₀ * K * L ^ 2 * M * V * H A ∧ q * V * H A ≤ 8192 * K₀ * K ^ 23 ∧
        0 < nA ∧ nA ≤ n₃ ∧ n₃ < ⊤ ∧
        n₃ * q ^ 2 ≤ 6561 * D * nA ∧
        q ≤ 128 * 6561 * 393216 ^ 4 * K₀ * K * L ^ 2 * M * V * nA * H (mobiusIdentityBall η) ∧
        nA * q ^ 3 * V * H (mobiusIdentityBall η) ≤ A₆ * 2 ^ 72 * K₀ ^ 2 * L ^ 2 * K ^ 107 ∧
        η ^ (-(1 / 61440 : ℝ) / 2) ≤ nA.toReal ∧ nA.toReal ≤ η ^ (-3 + γ / 2) ∧
        n₃.toReal ≤ η ^ (-β) * nA.toReal ∧
        ∀ t : ℕ, t ≤ ell → ∃ w ∈ matrixEntryBox (4 * R * (R + 1) * Q),
          q ^ 2 ≤ 16384 * K₀ * L ^ 2 * K ^ 4 * M *
            (generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η) (w • A) := by
  obtain ⟨s, hs, hsone, hsk, hsg, hsb, hall⟩ := exists_initial_walk_covering_interval hα hαone hγ hβ
  refine ⟨s, hs, hsone, hsk, hsg, hsb, ?_⟩
  intro k
  obtain ⟨N₀, J₀, hN₀, hfamily⟩ := hall k
  refine ⟨N₀, J₀, hN₀, ?_⟩
  intro r hr
  obtain ⟨g, hg, hgr, hcard, hcardr, hnear, hcover⟩ := hfamily r hr
  refine ⟨g, hg, hgr, hcard, hcardr, hnear, ?_⟩
  intro N j ell i hN hj hell hlog hi
  dsimp only
  intro henergy hnonflat
  obtain ⟨hV0, hVt, N_level, hNl, hlevel, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
      hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
      hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
      hnA0, hnA3, hn3t, htrip, hlo, hhi, hsizeLo, hsizeHi, hsmalltrip⟩ :=
    hcover N j ell i hN hj hell hlog hi henergy hnonflat
  refine ⟨hV0, hVt, N_level, hNl, hlevel, U, Y, x, hU1, hUo, hUi, hUc, hUb, hU0, hUt,
    hYs, hYi, hYcard, hYcov, happrox, hx, hVlo, hVhi, hmass,
    hA1, hAo, hAi, hAc, hAb, hA0, hAt, hA3, hHlo, hHhi, hVAlo, hVAhi,
    hnA0, hnA3, hn3t, htrip, hlo, hhi, hsizeLo, hsizeHi, hsmalltrip, ?_⟩
  intro t ht
  have hη : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
  have hηone : (1 / 4 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hG : ∀ a, (realEmbedding ∘ g) a ∈ matrixEntryBox 2 :=
    fun a => mobiusIdentityBall_subset_entryBox_two (dyadicRadius_pos r)
      (dyadicRadius_le_one r) (hnear a).2.1
  let R := (4 * (4 * (4 : ℝ) ^ ell) ^ 2) ^ (2 ^ i)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hQ : 1 ≤ 32 * (R + 1) ^ 6 := by
    have hh : (1 : ℝ) ≤ (R + 1) ^ 6 := one_le_pow₀ (by linarith)
    linarith only [hh]
  obtain ⟨w, hw, hwMass⟩ := exists_shortWalk_localized_mass (realEmbedding ∘ g)
    (by positivity) hG hη hηone ell i ht hU1 hUo hUi
    (fun _ hu => hUb (subset_closure hu)) hQ hα hαone x hx
    (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hη s)) 2) hmass
  refine ⟨w, hw, ?_⟩
  simpa only [← mul_assoc, show (2 : ℝ≥0∞) * 8192 = 16384 by norm_num] using hwMass

end TransposeFollowup.RationalFreePair
