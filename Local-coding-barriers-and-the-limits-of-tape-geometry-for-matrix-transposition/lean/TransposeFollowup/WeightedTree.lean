import TransposeFollowup.WeightedLeaf

/-! Weighted fragmentation of a finite tree. For integral node weights and
threshold L, at most totalWeight/(L+1) tree nodes suffice. The proof removes
leaves, either charging an overweight leaf or accumulating a light leaf's
weight at its neighbor. No balanced-separator theorem is assumed. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

namespace WeightedFragmentation

noncomputable def together {V : Type u} [Fintype V] (G : SimpleGraph V)
    (w : V → ℕ) (L : ℕ) (h : ∑ x, w x ≤ L) : WeightedFragmentation G w L where
  removed := ∅
  Label := PUnit
  label := fun _ => PUnit.unit
  edge_same := by intros; rfl
  mass_le := by intro a; simpa [labelMass] using h

noncomputable def removeAll {V : Type u} [Fintype V] (G : SimpleGraph V)
    (w : V → ℕ) (L : ℕ) : WeightedFragmentation G w L where
  removed := Finset.univ
  Label := PUnit
  label := fun _ => PUnit.unit
  edge_same := by intros; rfl
  mass_le := by intro a; simp [labelMass]

end WeightedFragmentation

private theorem weighted_tree_fragmentation_aux (N : ℕ) :
    ∀ (V : Type u) [Fintype V], Fintype.card V ≤ N →
      ∀ (G : SimpleGraph V), G.IsTree → ∀ (w : V → ℕ) (L : ℕ),
        ∃ F : WeightedFragmentation G w L, (L + 1) * F.removed.card ≤ ∑ x, w x := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ hN G hG w L
    by_cases hsmall : ∑ x, w x ≤ L
    · exact ⟨.together G w L hsmall, by simp [WeightedFragmentation.together]⟩
    · cases subsingleton_or_nontrivial V with
      | inl hsub =>
        let : Subsingleton V := hsub
        let : Nonempty V := hG.connected.nonempty
        have hcard : Fintype.card V = 1 := Fintype.card_eq_one_iff.mpr
          ⟨Classical.arbitrary V, fun _ => Subsingleton.elim _ _⟩
        refine ⟨.removeAll G w L, ?_⟩
        simp only [WeightedFragmentation.removeAll, Finset.card_univ, hcard, mul_one]
        omega
      | inr hnontriv =>
        let : Nontrivial V := hnontriv
        obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
        obtain ⟨u, hvu, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
        have huv : u ≠ v := hvu.ne.symm
        have hsize : Fintype.card {x // x ≠ v} < N :=
          (Fintype.card_subtype_lt (x := v) (by simp)).trans_le hN
        have htree : (withoutVertex G v).IsTree :=
          ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hv,
            hG.isAcyclic.induce {v}ᶜ⟩
        by_cases hlight : w v ≤ L
        · obtain ⟨F, hF⟩ := ih _ hsize {x // x ≠ v} le_rfl (withoutVertex G v) htree
            (addWeight (fun x => w x.val) ⟨u, huv⟩ (w v)) L
          refine ⟨F.attachLeaf v ⟨u, huv⟩ (fun x hx => hu x hx) hlight, ?_⟩
          rw [WeightedFragmentation.attachLeaf_card]
          rw [sum_addWeight] at hF
          rw [sum_split_vertex w v]
          simpa only [Nat.add_comm] using hF
        · obtain ⟨F, hF⟩ := ih _ hsize {x // x ≠ v} le_rfl (withoutVertex G v) htree
            (fun x => w x.val) L
          refine ⟨F.deleteVertex v, ?_⟩
          rw [WeightedFragmentation.deleteVertex_card, Nat.mul_add, Nat.mul_one,
            sum_split_vertex w v]
          omega

/-- Every finite weighted tree can be fragmented into pieces of weight at most
L by removing at most totalWeight/(L+1) vertices. The integral product bound
avoids division and also covers zero weights and L=0. -/
theorem weighted_tree_fragmentation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsTree) (w : V → ℕ) (L : ℕ) :
    ∃ S : Finset V, (L + 1) * S.card ≤ ∑ x, w x ∧
      ∀ x, ∑ y ∈ componentSet G S x, w y ≤ L := by
  obtain ⟨F, hF⟩ := weighted_tree_fragmentation_aux (Fintype.card V) V le_rfl G hG w L
  exact ⟨F.removed, hF, F.component_mass_le⟩

end TransposeFollowup
