import LeanMachine.DisjointSumsPinned

/-! # Deleting parity blocks that meet a recorded set

Keep all blocks disjoint from a specified finite coordinate set. Pin that
set, the old pins, and every coordinate of the deleted blocks. The remaining
kernel grants only shifts already allowed before deletion. Disjointness
bounds the number of deleted blocks by the number of recorded coordinates.
-/

namespace LeanMachine.DisjointSums

open Finset
open scoped BigOperators Classical
noncomputable section

variable {ι κ A : Type*} (D : DisjointSums ι κ)

/-- Select any subfamily of a disjoint bank. -/
def restrictBlocks (K : Set κ) : DisjointSums ι K where
  support k := D.support k.val
  nonempty k := D.nonempty k.val
  disjoint := fun _ _ h => D.disjoint (fun he => h (Subtype.ext he))

variable [Fintype κ] (F : Finset ι)

/-- Blocks that meet the additional recorded coordinates. -/
def touchingBlocks : Finset κ := univ.filter (fun k => ¬Disjoint (D.support k) F)

/-- Retain exactly the blocks disjoint from the additional record. -/
def deleteTouching : DisjointSums ι ↥(D.touchingBlocks F)ᶜ :=
  D.restrictBlocks (↑(D.touchingBlocks F)ᶜ)

/-- The old pins, the new recorded coordinates, and all deleted supports. -/
def deletionPins (E : Set ι) : Set ι :=
  E ∪ (↑F) ∪ (↑((D.touchingBlocks F).biUnion D.support))

/-- Each deleted block can be charged to a different newly recorded coordinate. -/
theorem touchingBlocks_card_le : (D.touchingBlocks F).card ≤ F.card := by
  classical
  have hne (k : κ) (hk : k ∈ D.touchingBlocks F) :
      1 ≤ ((D.support k) ∩ F).card :=
    card_pos.mpr (not_disjoint_iff_nonempty_inter.mp (mem_filter.mp hk).2)
  calc
    (D.touchingBlocks F).card = ∑ _k ∈ D.touchingBlocks F, 1 := by simp
    _ ≤ ∑ k ∈ D.touchingBlocks F, ((D.support k) ∩ F).card := sum_le_sum hne
    _ = ((D.touchingBlocks F).biUnion (fun k => D.support k ∩ F)).card :=
      (card_biUnion (fun k _ l _ hkl => (D.disjoint hkl).mono
        inter_subset_left inter_subset_left)).symm
    _ ≤ F.card := card_le_card (biUnion_subset.mpr (fun _ _ => inter_subset_right))

/-- Exact number of blocks surviving deletion. -/
theorem card_deleteTouching :
    Fintype.card ↥(D.touchingBlocks F)ᶜ = Fintype.card κ - (D.touchingBlocks F).card := by
  simp

variable (E : Set ι) (hfree : ∀ k, ∀ i ∈ E, i ∉ D.support k)

include hfree in
/-- The enlarged pin set is disjoint from every retained support. -/
theorem deletionPins_free (k : ↥(D.touchingBlocks F)ᶜ) (i : ι)
    (hi : i ∈ D.deletionPins F E) : i ∉ (D.deleteTouching F).support k := by
  intro hik
  change i ∈ D.support k.val at hik
  have hk : k.val ∉ D.touchingBlocks F := mem_compl.mp k.property
  rcases hi with (hiE | hiF) | hiS
  · exact hfree k.val i hiE hik
  · exact hk (mem_filter.mpr ⟨mem_univ _, not_disjoint_iff.mpr ⟨i, hik, hiF⟩⟩)
  · obtain ⟨l, hl, hil⟩ := mem_biUnion.mp hiS
    have hkl : k.val ≠ l := fun h => hk (h ▸ hl)
    exact disjoint_left.mp (D.disjoint hkl) hik hil

variable [AddCommGroup A] (θ : ι → A ≃+ A)

/-- Zero shifts on the enlarged pins restore every deleted parity equation. -/
theorem deleted_kernel_le (z : ι → A)
    (hz : (D.deleteTouching F).weightedEncode θ z = 0)
    (hp : Set.EqOn z 0 (D.deletionPins F E)) : D.weightedEncode θ z = 0 := by
  funext k
  by_cases hk : k ∈ D.touchingBlocks F
  · change ∑ i ∈ D.support k, θ i (z i) = 0
    apply sum_eq_zero
    intro i hi
    have hzi := hp (Or.inr (mem_biUnion.mpr ⟨k, hk, hi⟩))
    simp only [Pi.zero_apply] at hzi
    simp [hzi]
  · exact congrFun hz ⟨k, mem_compl.mpr hk⟩

end
end LeanMachine.DisjointSums
