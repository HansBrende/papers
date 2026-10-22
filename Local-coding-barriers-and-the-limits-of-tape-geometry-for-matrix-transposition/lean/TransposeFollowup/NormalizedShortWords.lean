import TransposeFollowup.SmoothedWalkShortWords

/-! Normalize the extracted endpoint words at one endpoint. The translating
matrix disappears; cardinality is unchanged and word length only doubles. -/
namespace TransposeFollowup.RationalFreePair
open Classical MeasureTheory Set RealMobius
open scoped ENNReal NNReal Pointwise
set_option autoImplicit false

variable [MeasurableSpace RealMobius.Group] [BorelSpace RealMobius.Group]

theorem exists_normalized_short_words_of_smoothed_walk_mass {m D : ℕ} (g : Fin m → Group)
    (hm : 0 < m) (hg : ∀ i, HasDenominator D (g i))
    (hfree : Function.Injective (FreeGroup.lift (realEmbedding ∘ g)))
    {k : ℝ} (hk : 1 ≤ k) (hcard : k ^ 2 ≤ 2 * m) (t : ℕ)
    {η : ℝ} (hη : 0 < η) {A : Set RealMobius.Group} (hA : MeasurableSet A)
    (w : RealMobius.Group) {p : ℝ≥0∞} (hp : 0 < p) (hpt : p ≠ ⊤)
    (hmass : p ≤ (generatorWalkMeasure (realEmbedding ∘ g) t ∗ₘ mobiusHaarKernel η) (w • A)) :
    ∃ u ∈ mobiusIdentityBall η, ∃ F : Finset (FreeGroup (Fin m)), 1 ∈ F ∧
      (∀ v ∈ F, FreeGroup.norm v ≤ 2 * t ∧
        FreeGroup.lift (realEmbedding ∘ g) v ∈ denominatorCarrier (D ^ (2 * t)) ∧
        u⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v * u ∈ A⁻¹ * A) ∧
      p ≤ 2 * (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 / k) ^ t) := by
  obtain ⟨u, hu, E, hEn, hE, hmassE⟩ :=
    exists_short_words_of_smoothed_walk_mass g hm hg hfree hk hcard t hη hA w hp hpt hmass
  obtain ⟨v₀, hv₀⟩ := hEn
  let f := fun v : FreeGroup (Fin m) => v₀⁻¹ * v
  have hinj : Function.Injective f := by
    intro a b he
    exact mul_left_cancel he
  refine ⟨u, hu, E.image f, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨v₀, hv₀, inv_mul_cancel v₀⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [f]
      have h := FreeGroup.norm_mul_le v₀⁻¹ z
      rw [FreeGroup.norm_inv_eq] at h
      have h₀ := (hE v₀ hv₀).1
      have hz' := (hE z hz).1
      omega
    · have h := denominatorCarrier_mul (denominatorCarrier_inv (hE v₀ hv₀).2.1)
        (hE z hz).2.1
      simpa only [f, map_mul, map_inv, two_mul, pow_add] using h
    · have he : u⁻¹ * FreeGroup.lift (realEmbedding ∘ g) (f z) * u =
          (w⁻¹ * FreeGroup.lift (realEmbedding ∘ g) v₀ * u)⁻¹ *
            (w⁻¹ * FreeGroup.lift (realEmbedding ∘ g) z * u) := by
        simp only [f, map_mul, map_inv, mul_inv_rev]
        group
      rw [he]
      exact Set.mul_mem_mul (Set.inv_mem_inv.mpr (hE v₀ hv₀).2.2) (hE z hz).2.2
  · simpa only [Finset.card_image_of_injective E hinj] using hmassE

end TransposeFollowup.RationalFreePair
