import TransposeFollowup.WeightedTree
import TransposeFollowup.GraphSeparatorBound

/-! Fragmentation of a graph from a standard tree decomposition. The weighted
leaf argument improves the earlier manuscript's `2hn/L` separator estimate to
the exact integral bound `(L+1)|S| ≤ hn`. This is a supporting graph theorem;
no novelty claim is made for this standard tree-decomposition technique. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u v

/-- A graph with bags of size at most h admits a separator whose removal leaves
components of size at most L, paying `(L+1)|S| ≤ h|V|`. L=0 and empty vertex
sets are included. -/
theorem TreeDecomposition.fragmentation {V : Type u} {J : Type v}
    [Fintype V] [Fintype J] {G : SimpleGraph V} {T : SimpleGraph J}
    (D : TreeDecomposition G T) (h L : ℕ) (hbag : ∀ j, (D.bag j).card ≤ h) :
    ∃ S : Finset V, (L + 1) * S.card ≤ h * Fintype.card V ∧
      ∀ C ∈ graphComponents G S, C.card ≤ L := by
  obtain ⟨U, hU, hfrag⟩ := weighted_tree_fragmentation T D.tree D.ownerWeight L
  rw [D.total_ownerWeight] at hU
  obtain ⟨hS, hC⟩ := D.fragmentation_transfer U h L hbag hfrag
  refine ⟨D.removed U, ?_, hC⟩
  calc
    (L + 1) * (D.removed U).card ≤ (L + 1) * (h * U.card) := Nat.mul_le_mul_left _ hS
    _ = h * ((L + 1) * U.card) := by ring
    _ ≤ h * Fintype.card V := Nat.mul_le_mul_left _ hU

theorem sum_component_cards {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    ∑ C ∈ graphComponents G S, C.card = (Finset.univ \ S).card := by
  rw [← graphComponents_cover G S, Finset.card_biUnion (graphComponents_pairwise_disjoint G S)]
  rfl

theorem sum_component_squares_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (L : ℕ)
    (hL : ∀ C ∈ graphComponents G S, C.card ≤ L) :
    ∑ C ∈ graphComponents G S, C.card ^ 2 ≤ Fintype.card V * L := by
  calc
    _ ≤ ∑ C ∈ graphComponents G S, C.card * L := by
      apply Finset.sum_le_sum
      intro C hC
      simpa only [pow_two] using Nat.mul_le_mul_left C.card (hL C hC)
    _ = (Finset.univ \ S).card * L := by rw [← Finset.sum_mul, sum_component_cards]
    _ ≤ Fintype.card V * L := Nat.mul_le_mul_right _ (Finset.card_le_univ _)

/-- Exact integral loss estimate before selecting an optimal component size. -/
theorem TreeDecomposition.separator_loss {n b : ℕ} {J : Type v} [Fintype J]
    {G : SimpleGraph (Fin n)} {T : SimpleGraph J} (D : TreeDecomposition G T)
    (h L : ℕ) (hbag : ∀ j, (D.bag j).card ≤ h) :
    ∃ S : Finset (Fin n),
      (L + 1) * graphSeparatorLoss b G S ≤ b * n * (h * n + L * (L + 1)) := by
  obtain ⟨S, hS, hC⟩ := D.fragmentation h L hbag
  simp only [Fintype.card_fin] at hS
  have hsq := sum_component_squares_le G S L hC
  simp only [Fintype.card_fin] at hsq
  refine ⟨S, ?_⟩
  calc
    _ = n * b * ((L + 1) * S.card) +
        b * (L + 1) * (∑ C ∈ graphComponents G S, C.card ^ 2) := by
      unfold graphSeparatorLoss
      ring
    _ ≤ n * b * (h * n) + b * (L + 1) * (n * L) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hS) (Nat.mul_le_mul_left _ hsq)
    _ = _ := by ring

end TransposeFollowup
