import TransposeFollowup.CoordinatePackets
import TransposeFollowup.DisjointFamilyCount
import TransposeFollowup.ComponentDistance
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Packet occurrences versus connected components. This count uses only
declared supports, not linearity or independence of packet values. -/

namespace TransposeFollowup

open Classical
open scoped BigOperators
set_option autoImplicit false
universe u

namespace CoordinateSystem

variable {V : Type u} [Fintype V] {B : ℕ} (C : CoordinateSystem V B)

theorem component_connected {S : Finset V} (hS : S ∈ C.components) :
    (C.graph.induce (S : Set V)).Connected := by
  obtain ⟨v, _, rfl⟩ := (mem_graphComponents C.graph ∅ S).mp hS
  have hs : (↑(componentSet C.graph ∅ v) : Set V) =
      (C.graph.connectedComponentMk v).supp := by
    ext w
    simp only [Finset.mem_coe, mem_componentSet_empty,
      SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hs]
  exact (C.graph.connectedComponentMk v).connected_toSimpleGraph

theorem edge_support {e : Sym2 V} (he : e ∈ C.graph.edgeFinset) :
    ∃ k, (C.packet k).support = e.toFinset := by
  induction e using Sym2.inductionOn with
  | hf v w =>
    obtain ⟨hne, k, hv, hw⟩ := SimpleGraph.mem_edgeFinset.mp he
    refine ⟨k, ?_⟩
    rw [Sym2.toFinset_mk_eq]
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hv, hw⟩
    · simpa [Finset.card_pair hne] using (C.packet k).support_card_le

theorem component_edges_le_packets (S : Finset V) :
    (C.graph.induce (S : Set V)).edgeFinset.card ≤ (C.packetIndices S).card := by
  let E := C.graph.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  have hinj : Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
    intro a b h
    apply Sym2.ext
    intro v
    simp only [← Sym2.mem_toFinset, h]
  have hsub : E.image Sym2.toFinset ⊆ (C.packetIndices S).image (fun k => (C.packet k).support) := by
    intro s hs
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨heg, hes⟩ := Finset.mem_filter.mp he
    obtain ⟨k, hk⟩ := C.edge_support heg
    apply Finset.mem_image.mpr
    refine ⟨k, (C.mem_packetIndices S k).mpr ?_, hk⟩
    rw [hk]
    exact ⟨Finset.nonempty_iff_ne_empty.mpr e.toFinset_ne_empty, hes⟩
  calc
    _ = E.card := (C.graph.card_filter_edgeFinset_toFinset_subset S).symm
    _ = (E.image Sym2.toFinset).card := (Finset.card_image_of_injective E hinj).symm
    _ ≤ ((C.packetIndices S).image (fun k => (C.packet k).support)).card := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le

theorem component_card_le_packets_add_one {S : Finset V} (hS : S ∈ C.components) :
    S.card ≤ (C.packetIndices S).card + 1 := by
  have h := (C.component_connected hS).card_vert_le_card_edgeSet_add_one
  have h' : S.card ≤ (C.graph.induce (S : Set V)).edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Finset.coe_sort_coe, Fintype.card_coe,
      ← SimpleGraph.edgeFinset_card] using h
  exact h'.trans (Nat.add_le_add_right (C.component_edges_le_packets S) 1)

theorem sum_component_cards : ∑ S ∈ C.components, S.card = Fintype.card V := by
  have h := Finset.card_biUnion C.components_disjoint
  simp only [id_eq] at h
  rw [← h, C.components_cover, Finset.card_univ]

theorem sum_component_packets_le : ∑ S ∈ C.components, (C.packetIndices S).card ≤ B := by
  rw [← Finset.card_biUnion C.packetIndices_disjoint]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin B)

theorem coordinate_count_le_broadcast_add_deficient :
    Fintype.card V ≤ B + C.deficient.card := by
  have hp : ∀ S ∈ C.components,
      S.card ≤ (C.packetIndices S).card +
        if (C.packetIndices S).card < S.card then 1 else 0 := by
    intro S hS
    split_ifs with h
    · exact C.component_card_le_packets_add_one hS
    · omega
  have hs := Finset.sum_le_sum hp
  rw [C.sum_component_cards, Finset.sum_add_distrib, Finset.sum_boole] at hs
  exact hs.trans (Nat.add_le_add_right C.sum_component_packets_le C.deficient.card)

theorem deficient_nonempty {S : Finset V} (hS : S ∈ C.deficient) : S.Nonempty :=
  C.component_nonempty ((C.mem_deficient S).mp hS).1

theorem deficient_disjoint : (C.deficient : Set (Finset V)).PairwiseDisjoint id := by
  intro S hS T hT hne
  exact C.components_disjoint (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hT).1 hne

theorem deficient_size_bound (ell : ℕ) :
    (ell + 1) * C.deficient.card ≤ Fintype.card V + ell * (C.smallComponents ell).card :=
  disjoint_family_size_bound C.deficient (fun _ h => C.deficient_nonempty h)
    C.deficient_disjoint ell

end CoordinateSystem
end TransposeFollowup
