import TransposeFollowup.NormalizedShortWords
import TransposeFollowup.SmoothedIterateLocalizedMass

/-! Every shorter walk in the actual iterate yields a large bounded-word
set whose common conjugate is contained in the square of the SAME localized
witness. Translation is eliminated without an additional cardinality loss. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_iterate_normalized_short_words {m D : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hg : ∀ a, HasDenominator D (g a))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    (hG : ∀ a, realEmbedding (g a) ∈ matrixEntryBox 2)
    {κ : ℝ} (hκ : 1 ≤ κ) (hcard : κ ^ 2 ≤ 2 * m)
    {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1) (ell i : ℕ) {t : ℕ} (ht : t ≤ ell)
    {U : Set RealMobius.Group} {Q α X : ℝ}
    (hU1 : 1 ∈ U) (hUo : IsOpen U) (hUi : U⁻¹ = U) (hUb : U ⊆ matrixEntryBox Q)
    (hQ : 1 ≤ Q) (hα : 0 < α) (hαone : α ≤ 1)
    (x : RealMobius.Group) (hx : x ∈ matrixEntryBox X)
    {c C : ℝ≥0∞} (hc : 0 < c)
    (hmass : c ≤ C * (Measure.haar : Measure RealMobius.Group).withDensity
      (smoothedAutocorrelationIterate (generatorWalkMeasure (realEmbedding ∘ g) ell) η i) (x • U)) :
    let A := U ^ 2 ∩ mobiusIdentityBall α
    let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
    ∃ u ∈ mobiusIdentityBall η, ∃ F : Finset (FreeGroup (Fin m)), 1 ∈ F ∧
      (∀ v ∈ F, FreeGroup.norm v ≤ 2 * t ∧
        FreeGroup.lift (realEmbedding ∘ g) v ∈ denominatorCarrier (D ^ (2 * t)) ∧
        u⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v * u ∈ A ^ 2) ∧
      c ≤ 4 * C * M * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / κ) ^ t) := by
  dsimp only
  let A := U ^ 2 ∩ mobiusIdentityBall α
  let M := ENNReal.ofReal (33 ^ 4 * Q ^ 8 / α ^ 4)
  obtain ⟨w, _, hw⟩ := exists_shortWalk_localized_mass (realEmbedding ∘ g) hm hG
    hη hηone ell i ht hU1 hUo hUi hUb hQ hα hαone x hx hc hmass
  let μ := generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η
  have : IsProbabilityMeasure (generatorWalkMeasure (realEmbedding ∘ g) t) :=
    generatorWalkMeasure_probability _ hm t
  have : IsProbabilityMeasure (mobiusHaarKernel η) := mobiusHaarKernel_probability hη
  have hp : 0 < μ (w • A) := by
    by_contra hn
    have hz : μ (w • A) = 0 := le_antisymm (not_lt.mp hn) bot_le
    change c ≤ 2 * C * M * μ (w • A) at hw
    rw [hz, mul_zero] at hw
    exact (not_le_of_gt hc) hw
  have hgeo := near_identity_square_geometry hU1 hUo hUi hα hαone
  obtain ⟨u, hu, F, hF1, hF, hcount⟩ := exists_normalized_short_words_of_smoothed_walk_mass
    g hm hg hfree hκ hcard t hη hgeo.2.1.measurableSet w hp (measure_ne_top μ _) le_rfl
  refine ⟨u, hu, F, hF1, ?_, ?_⟩
  · intro v hv
    refine ⟨(hF v hv).1, (hF v hv).2.1, ?_⟩
    simpa only [hgeo.2.2.1, ← pow_two] using (hF v hv).2.2
  · calc
      c ≤ 2 * C * M * μ (w • A) := hw
      _ ≤ 2 * C * M * (2 * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / κ) ^ t)) :=
        mul_le_mul' le_rfl hcount
      _ = _ := by ring

end TransposeFollowup.RationalFreePair
