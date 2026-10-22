import TransposeFollowup.InteractionGraph
import TransposeFollowup.SeparatorCount

/-! Finite connected-component partitions and their exact separator loss. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

open Classical in
noncomputable def graphComponents {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) : Finset (Finset ι) :=
  (Finset.univ \ S).image (componentSet G S)

theorem mem_graphComponents {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S C : Finset ι) :
    C ∈ graphComponents G S ↔ ∃ i, i ∉ S ∧ componentSet G S i = C := by
  classical
  simp only [graphComponents, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]

theorem componentSet_subset_complement {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) (i : ι) :
    componentSet G S i ⊆ Finset.univ \ S := by
  intro j hj
  obtain ⟨_, hjs, _⟩ := (mem_componentSet G S i j).mp hj
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjs⟩

theorem graphComponents_nonempty {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S C : Finset ι) (hC : C ∈ graphComponents G S) : C.Nonempty := by
  obtain ⟨i, hi, rfl⟩ := (mem_graphComponents G S C).mp hC
  exact ⟨i, componentSet_self_mem G S i hi⟩

theorem graphComponents_pairwise_disjoint {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) :
    (graphComponents G S : Set (Finset ι)).PairwiseDisjoint id := by
  classical
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro k hkC hkD
  obtain ⟨i, hi, rfl⟩ := (mem_graphComponents G S C).mp hC
  obtain ⟨j, hj, rfl⟩ := (mem_graphComponents G S D).mp hD
  have hik := (mem_componentSet G S i k).mp hkC
  have hjk := (mem_componentSet G S j k).mp hkD
  exact hne ((componentSet_eq_of_outsideConnected G S hik).trans
    (componentSet_eq_of_outsideConnected G S hjk).symm)

theorem graphComponents_cover {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (S : Finset ι) :
    (graphComponents G S).biUnion id = Finset.univ \ S := by
  classical
  ext i
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, hC, hi⟩
    obtain ⟨j, hj, rfl⟩ := (mem_graphComponents G S C).mp hC
    exact ((mem_componentSet G S j i).mp hi).choose_spec.choose
  · intro hi
    exact ⟨componentSet G S i, (mem_graphComponents G S _).mpr ⟨i, hi, rfl⟩,
      componentSet_self_mem G S i hi⟩

theorem componentRows_eq_componentSet {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (i : Fin n) :
    componentRows S (componentSet G S) (componentSet G S i) = componentSet G S i := by
  classical
  ext j
  simp only [componentRows, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hj, heq⟩
    rw [← heq]
    exact componentSet_self_mem G S j hj
  · intro hj
    have hconn := (mem_componentSet G S i j).mp hj
    exact ⟨hconn.choose_spec.choose, (componentSet_eq_of_outsideConnected G S hconn).symm⟩

theorem componentRows_eq_of_mem_graphComponents {n : ℕ} (G : SimpleGraph (Fin n))
    (S C : Finset (Fin n)) (hC : C ∈ graphComponents G S) :
    componentRows S (componentSet G S) C = C := by
  obtain ⟨i, hi, rfl⟩ := (mem_graphComponents G S C).mp hC
  exact componentRows_eq_componentSet G S i

theorem componentRows_empty_of_not_mem_graphComponents {n : ℕ} (G : SimpleGraph (Fin n))
    (S C : Finset (Fin n)) (hC : C ∉ graphComponents G S) :
    componentRows S (componentSet G S) C = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  exact hC ((mem_graphComponents G S C).mpr ⟨i, h.1, h.2⟩)

theorem sum_componentRows_sq {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (∑ C : Finset (Fin n), (componentRows S (componentSet G S) C).card ^ 2) =
      ∑ C ∈ graphComponents G S, C.card ^ 2 := by
  classical
  calc
    _ = ∑ C ∈ graphComponents G S, (componentRows S (componentSet G S) C).card ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro C _ hC
      rw [componentRows_empty_of_not_mem_graphComponents G S C hC]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [componentRows_eq_of_mem_graphComponents G S C hC]

theorem card_internalFreeBits_components {n b : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    (internalFreeBits (b := b) S (componentSet G S)).card =
      b * ∑ C ∈ graphComponents G S, C.card ^ 2 := by
  classical
  rw [card_internalFreeBits, sum_componentRows_sq]

end TransposeFollowup
