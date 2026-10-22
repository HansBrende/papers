import TransposeFollowup.TreeFragmentation

/-! Natural-valued treewidth using ordinary finite tree decompositions. Finite
decomposition trees are indexed by `Fin m`; no restriction on their shape is
imposed. The empty graph has treewidth zero under this natural convention. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false
universe u

def HasTreewidthAtMost {V : Type u} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ m : ℕ, ∃ T : SimpleGraph (Fin m), ∃ D : TreeDecomposition G T,
    ∀ j, (D.bag j).card ≤ t + 1

/-- The one-bag decomposition, included to establish that the minimum in the
definition of treewidth exists. -/
noncomputable def oneBagDecomposition {V : Type u} [Fintype V] (G : SimpleGraph V) :
    TreeDecomposition G (⊥ : SimpleGraph (Fin 1)) where
  tree := SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  vertex_covered := fun x => ⟨0, Finset.mem_univ x⟩
  edge_covered := fun {_ _} _ => ⟨0, Finset.mem_univ _, Finset.mem_univ _⟩
  running := fun _ => SimpleGraph.Preconnected.of_subsingleton

theorem hasTreewidthAtMost_card_pred {V : Type u} [Fintype V] (G : SimpleGraph V) :
    HasTreewidthAtMost G (Fintype.card V - 1) := by
  refine ⟨1, ⊥, oneBagDecomposition G, ?_⟩
  intro j
  simp only [oneBagDecomposition, Finset.card_univ]
  omega

theorem exists_treewidth_bound {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ t, HasTreewidthAtMost G t := ⟨_, hasTreewidthAtMost_card_pred G⟩

noncomputable def treewidth {V : Type u} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (exists_treewidth_bound G)

theorem hasTreewidthAtMost_treewidth {V : Type u} [Fintype V] (G : SimpleGraph V) :
    HasTreewidthAtMost G (treewidth G) := Nat.find_spec (exists_treewidth_bound G)

theorem treewidth_le_of_hasTreewidthAtMost {V : Type u} [Fintype V]
    (G : SimpleGraph V) {t : ℕ} (ht : HasTreewidthAtMost G t) : treewidth G ≤ t :=
  Nat.find_min' (exists_treewidth_bound G) ht

theorem treewidth_le_card_pred {V : Type u} [Fintype V] (G : SimpleGraph V) :
    treewidth G ≤ Fintype.card V - 1 :=
  treewidth_le_of_hasTreewidthAtMost G (hasTreewidthAtMost_card_pred G)

/-- The fragmentation result now has no decomposition or separator hypothesis:
the only graph parameter is its standard natural-valued treewidth. -/
theorem treewidth_fragmentation {V : Type u} [Fintype V]
    (G : SimpleGraph V) (L : ℕ) :
    ∃ S : Finset V, (L + 1) * S.card ≤ (treewidth G + 1) * Fintype.card V ∧
      ∀ C ∈ graphComponents G S, C.card ≤ L := by
  obtain ⟨m, T, D, hD⟩ := hasTreewidthAtMost_treewidth G
  exact D.fragmentation (treewidth G + 1) L hD

theorem treewidth_separator_loss {n b : ℕ} (G : SimpleGraph (Fin n)) (L : ℕ) :
    ∃ S : Finset (Fin n), (L + 1) * graphSeparatorLoss b G S ≤
      b * n * ((treewidth G + 1) * n + L * (L + 1)) := by
  obtain ⟨m, T, D, hD⟩ := hasTreewidthAtMost_treewidth G
  exact D.separator_loss (treewidth G + 1) L hD

end TransposeFollowup
