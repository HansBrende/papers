import TransposeFollowup.BoundedCoordinatePacking
import TransposeFollowup.RationalRecenteredFamily
import Mathlib.Data.Fintype.EquivFin

/-! Select a finite near-identity free family, including its actual rational
matrices and denominator, from an explicit packing inequality. -/
namespace TransposeFollowup.RationalFreePair
open Classical BoundedCoordinatePacking
set_option autoImplicit false

theorem exists_packed_free_family (n : ℕ) {L m : ℕ} (hL : 0 < L)
    {η : ℝ} (hη : 0 < η)
    (hcard : binCount ((1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L))
      (η / (8 * (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L))) ^ 4 * (m + 1) ≤ 2 ^ L) :
    ∃ g : Fin m → Group,
      Function.Injective (FreeGroup.lift g) ∧
      Function.Injective (FreeGroup.lift (realEmbedding ∘ g)) ∧
      (∀ k, HasDenominator (seedDenominator n ^ (4 * L)) (g k)) ∧
      ∀ k, realEmbedding (g k) ∈ RealMobius.mobiusIdentityBall η := by
  let N := (1 + 8 / (baseDenominator n : ℝ)) ^ (2 * L)
  have hδ : 0 < η / (8 * N) := by dsimp [N]; positivity
  obtain ⟨S, hS, hclose⟩ := exists_cluster
    (fun (f : Fin L → Bool) i j => realSquareFamily n f i j) (N := N)
    hδ (realSquareFamily_entry_bound n) (m := m + 1) (by simpa using hcard)
  obtain ⟨o, ho⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have herase : m ≤ (S.erase o).card := by rw [Finset.card_erase_of_mem ho]; omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq herase
  let e : T ≃ Fin m := Fintype.equivFinOfCardEq (by simpa using hT)
  let j : Fin m → (Fin L → Bool) := fun k => (e.symm k).val
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  have hjT : ∀ k, j k ∈ T := fun k => (e.symm k).property
  have hjS : ∀ k, j k ∈ S := fun k => (Finset.mem_erase.mp (hTS (hjT k))).2
  have hjo : ∀ k, j k ≠ o := fun k => (Finset.mem_erase.mp (hTS (hjT k))).1
  refine ⟨fun k => (squareFamily n o)⁻¹ * squareFamily n (j k),
    squareFamily_translated_subfamily_free n hL o j hj hjo, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, translated_squareFamily_realEmbedding] using
      realSquareFamily_translated_subfamily_free n hL o j hj hjo
  · intro k
    exact translated_squareFamily_hasDenominator n o (j k)
  · intro k
    rw [translated_squareFamily_realEmbedding]
    exact realSquareFamily_near_pair_translate n o (j k) hη
      (fun i t => (hclose (j k) (hjS k) o ho i t).le)

theorem free_family_injective {ι : Type*} {G : Type*} [_root_.Group G] (g : ι → G)
    (hg : Function.Injective (FreeGroup.lift g)) : Function.Injective g := by
  intro i j h
  apply FreeGroup.of_injective
  apply hg
  simpa only [FreeGroup.lift_apply_of] using h

theorem free_family_card {m : ℕ} (g : Fin m → Group)
    (hg : Function.Injective (FreeGroup.lift g)) : (Finset.univ.image g).card = m := by
  rw [Finset.card_image_of_injective _ (free_family_injective g hg)]
  simp

end TransposeFollowup.RationalFreePair
