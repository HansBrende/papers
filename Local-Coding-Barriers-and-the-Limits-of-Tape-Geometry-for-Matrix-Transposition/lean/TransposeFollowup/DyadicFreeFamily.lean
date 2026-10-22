import TransposeFollowup.DyadicFreeFamilyScales

/-! An unconditional dyadic near-identity rational free family with exact
cardinality and polynomial denominator bounds. -/
namespace TransposeFollowup.RationalFreePair
open Classical
set_option autoImplicit false

theorem dyadicDenominator_radius_lower (r : ℕ) :
    1 / dyadicRadius r ≤ (dyadicDenominator r : ℝ) := by
  simpa only [dyadicRadius, one_div_one_div, Nat.cast_pow, Nat.cast_ofNat] using
    (Nat.cast_le (α := ℝ)).mpr (dyadicDenominator_lower r)

theorem dyadicDenominator_radius_upper (r : ℕ) :
    (dyadicDenominator r : ℝ) ≤ (1 / dyadicRadius r) ^ 1920 := by
  have h : (dyadicDenominator r : ℝ) ≤ (2 : ℝ) ^ (1920 * r) := by
    exact_mod_cast dyadicDenominator_upper r
  simpa only [dyadicRadius, one_div_one_div, ← pow_mul, mul_comm r 1920] using h

theorem exists_dyadic_free_family {r : ℕ} (hr : 5 ≤ r) :
    ∃ g : Fin (2 ^ (3 * r)) → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2 ^ (3 * r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2 ^ (3 * r) ∧
      ∀ k, HasDenominator (dyadicDenominator r) (g k) ∧
        realEmbedding (g k) ∈ RealMobius.mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g k))⁻¹ ∈ RealMobius.mobiusIdentityBall (dyadicRadius r) := by
  have hcard := dyadic_packing_budget hr
  have hex := exists_packed_free_family 9999 (L := 16 * r) (m := 2 ^ (3 * r))
    (by omega) (dyadicRadius_pos r)
    (by simpa only [dyadicEntryBound, show 2 * (16 * r) = 32 * r by omega] using hcard)
  obtain ⟨g, hg, hgr, hd, hn⟩ := hex
  refine ⟨g, hg, hgr, free_family_card g hg, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (free_family_injective _ hgr)]
    simp
  · intro k
    refine ⟨?_, hn k, ?_⟩
    · simpa only [dyadicDenominator, show 4 * (16 * r) = 64 * r by omega] using hd k
    · change RealMobius.mobiusIdentityDistanceSq (realEmbedding (g k))⁻¹ < _
      rw [real_identityDistanceSq_inv]
      exact hn k

theorem exists_dyadic_free_family_with_bounds {r : ℕ} (hr : 5 ≤ r) :
    ∃ (Q : ℕ) (g : Fin (2 ^ (3 * r)) → Group),
      0 < Q ∧
      1 / dyadicRadius r ≤ (Q : ℝ) ∧
      (Q : ℝ) ≤ (1 / dyadicRadius r) ^ 1920 ∧
      Q ≤ (Finset.univ.image g).card ^ 640 ∧
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (Finset.univ.image g).card = 2 ^ (3 * r) ∧
      (Finset.univ.image (realEmbedding ∘ g)).card = 2 ^ (3 * r) ∧
      ∀ k, HasDenominator Q (g k) ∧
        realEmbedding (g k) ∈ RealMobius.mobiusIdentityBall (dyadicRadius r) ∧
        (realEmbedding (g k))⁻¹ ∈ RealMobius.mobiusIdentityBall (dyadicRadius r) := by
  obtain ⟨g, hg, hgr, hc, hcr, hn⟩ := exists_dyadic_free_family hr
  refine ⟨dyadicDenominator r, g, dyadicDenominator_pos r,
    dyadicDenominator_radius_lower r, dyadicDenominator_radius_upper r,
    ?_, hg, hgr, hc, hcr, hn⟩
  rw [hc]
  exact dyadicDenominator_card_bound r

end TransposeFollowup.RationalFreePair
