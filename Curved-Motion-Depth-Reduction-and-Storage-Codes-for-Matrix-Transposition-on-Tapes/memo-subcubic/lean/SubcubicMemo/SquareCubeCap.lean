import SubcubicMemo.SquareTripleCap

/-! The cube with one vertex deleted is another instance of the same
three-boundary-vertex closure lemma. -/

namespace SubcubicMemo.Squares

open Finset MotionDepthCodes
open scoped Classical

def cubeCap : SimpleGraph (Fin 7) := SimpleGraph.fromRel fun i j =>
  (i, j) ∈ ([(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (2, 5), (3, 5),
    (3, 6), (1, 6)] : List (Fin 7 × Fin 7))

instance : DecidableRel cubeCap.Adj := by unfold cubeCap; infer_instance

def capLeft : Finset (Fin 7) := {0, 4, 5, 6}
def capRight : Finset (Fin 7) := {1, 2, 3}
def capBoundary : Finset (Fin 7) := {4, 5, 6}

theorem cap_boundary_subset : capBoundary ⊆ capLeft := by decide
theorem cap_boundary_card : capBoundary.card = 3 := by decide
theorem cap_disjoint : Disjoint capLeft capRight := by decide

theorem cap_pair : ∀ a ∈ capBoundary, ∃ q ∈ capRight, ∃ r ∈ capRight,
    q ≠ r ∧ cubeCap.Adj a q ∧ cubeCap.Adj a r := by decide

theorem cap_left_common : ∀ a ∈ capLeft, ∀ b ∈ capLeft, a ≠ b →
    ∃ q, cubeCap.Adj q a ∧ cubeCap.Adj q b := by decide

theorem cap_right_neighbors : ∀ q ∈ capRight,
    (cubeCap.neighborFinset q).card = 3 ∧ cubeCap.neighborFinset q ⊆ capLeft := by decide

theorem cap_center_neighbors : cubeCap.neighborFinset 0 = capRight := by decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] (h : Hyp G)

include h in
theorem injected_full_neighbors (f : cubeCap →g G) (hf : Function.Injective f)
    {q : Fin 7} (hq : (cubeCap.neighborFinset q).card = 3) {x : V}
    (hqx : G.Adj (f q) x) : x ∈ (cubeCap.neighborFinset q).image f := by
  apply neighbor_mem_of_three h ((cubeCap.neighborFinset q).image f)
    (by rw [card_image_of_injective _ hf, hq]) _ hqx
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
  exact f.map_adj ((cubeCap.mem_neighborFinset q i).mp hi)

include h in
theorem hom_of_cubeCap (hconn : G.Preconnected) (f : cubeCap →g G)
    (hf : Function.Injective f) : Nonempty (G →g circularClique 8 3) := by
  let L := capLeft.image f
  let Q := capRight.image f
  let P := capBoundary.image f
  have s : BoundarySeed (G := G) L Q P :=
    { boundary := image_subset_image cap_boundary_subset
      card := by rw [card_image_of_injective _ hf, cap_boundary_card]
      disjoint := by
        apply disjoint_left.mpr
        intro a ha hb
        obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
        obtain ⟨j, hj, he⟩ := mem_image.mp hb
        exact disjoint_left.mp cap_disjoint hi (hf he ▸ hj)
      independent := by
        intro a ha b hb hab
        obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
        have hij : i ≠ j := fun he => hab.ne (congrArg f he)
        obtain ⟨q, hqi, hqj⟩ := cap_left_common i hi j hj hij
        exact no_triangle G h.triangle (f.map_adj hqi) (f.map_adj hqj) hab
      right := by
        intro q hq x hqx
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hq
        exact image_subset_image (cap_right_neighbors i hi).2
          (injected_full_neighbors h f hf (cap_right_neighbors i hi).1 hqx)
      internal := by
        intro a ha han x hax
        obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
        have hn : i ∉ capBoundary := fun hi => han (mem_image_of_mem f hi)
        have hi0 : i = 0 := by
          fin_cases i <;> simp_all [capLeft, capBoundary]
        subst i
        have hm := injected_full_neighbors h f hf (by rw [cap_center_neighbors]; decide) hax
        rwa [cap_center_neighbors] at hm
      pair := by
        intro a ha
        obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
        obtain ⟨q, hq, r, hr, hqr, hiq, hir⟩ := cap_pair i hi
        exact ⟨f q, mem_image_of_mem f hq, f r, mem_image_of_mem f hr,
          fun he => hqr (hf he), f.map_adj hiq, f.map_adj hir⟩ }
  exact s.hom h hconn

end SubcubicMemo.Squares
