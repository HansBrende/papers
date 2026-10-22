import TransposeFollowup.ComponentPartition
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Standard finite tree decompositions and the transfer of separators from
the decomposition tree to the graph. This does not assume a balanced-separator
or fragmentation theorem in the definition of a tree decomposition. -/

namespace TransposeFollowup

open scoped BigOperators
open Classical
set_option autoImplicit false

universe u v

/-- A tree decomposition in its usual bag formulation. The occurrence nodes
of each graph vertex induce a connected subtree: coverage supplies nonemptiness,
so `running` can state preconnectedness without a redundant nonemptiness field. -/
structure TreeDecomposition {V : Type u} {J : Type v}
    (G : SimpleGraph V) (T : SimpleGraph J) where
  tree : T.IsTree
  bag : J → Finset V
  vertex_covered : ∀ x, ∃ j, x ∈ bag j
  edge_covered : ∀ {x y}, G.Adj x y → ∃ j, x ∈ bag j ∧ y ∈ bag j
  running : ∀ x, (T.induce {j | x ∈ bag j}).Preconnected

namespace TreeDecomposition

variable {V : Type u} {J : Type v} {G : SimpleGraph V} {T : SimpleGraph J}
    (D : TreeDecomposition G T)

/-- Assign each graph vertex to one bag containing it. These disjoint ownership
classes, rather than bag cardinalities, are the weights on the tree. -/
noncomputable def owner (x : V) : J := (D.vertex_covered x).choose

theorem mem_owner_bag (x : V) : x ∈ D.bag (D.owner x) :=
  (D.vertex_covered x).choose_spec

noncomputable def removed (U : Finset J) : Finset V := U.biUnion D.bag

theorem mem_removed (U : Finset J) (x : V) :
    x ∈ D.removed U ↔ ∃ j ∈ U, x ∈ D.bag j := by
  simp [removed]

theorem not_mem_selected_of_not_removed (U : Finset J) {x : V}
    (hx : x ∉ D.removed U) {j : J} (hj : x ∈ D.bag j) : j ∉ U := by
  intro hjU
  exact hx ((D.mem_removed U x).mpr ⟨j, hjU, hj⟩)

theorem owner_not_selected (U : Finset J) {x : V} (hx : x ∉ D.removed U) :
    D.owner x ∉ U := D.not_mem_selected_of_not_removed U hx (D.mem_owner_bag x)

/-- Connected occurrences of an undeleted graph vertex give paths avoiding
every selected tree node. -/
theorem occurrences_outside_connected (U : Finset J) {x : V}
    (hx : x ∉ D.removed U) {i j : J} (hi : x ∈ D.bag i) (hj : x ∈ D.bag j) :
    OutsideConnected T U i j := by
  let f : T.induce {k | x ∈ D.bag k} →g T.induce {k | k ∉ U} :=
    { toFun := fun k => ⟨k.val, D.not_mem_selected_of_not_removed U hx k.property⟩
      map_rel' := fun h => h }
  exact ⟨D.not_mem_selected_of_not_removed U hx hi,
    D.not_mem_selected_of_not_removed U hx hj,
    (D.running x ⟨i, hi⟩ ⟨j, hj⟩).map f⟩

theorem adjacent_owners_outside_connected (U : Finset J) {x y : V}
    (hx : x ∉ D.removed U) (hy : y ∉ D.removed U) (hxy : G.Adj x y) :
    OutsideConnected T U (D.owner x) (D.owner y) := by
  obtain ⟨j, hxj, hyj⟩ := D.edge_covered hxy
  obtain ⟨hi, hj, hij⟩ := D.occurrences_outside_connected U hx (D.mem_owner_bag x) hxj
  obtain ⟨_, hk, hjk⟩ := D.occurrences_outside_connected U hy hyj (D.mem_owner_bag y)
  exact ⟨hi, hk, hij.trans hjk⟩

/-- A graph component remaining after deleting selected bags maps wholly into
one remaining tree component. Only the standard decomposition axioms are used. -/
theorem owners_outside_connected (U : Finset J) {x y : V}
    (hxy : OutsideConnected G (D.removed U) x y) :
    OutsideConnected T U (D.owner x) (D.owner y) := by
  obtain ⟨hx, hy, ⟨p⟩⟩ := hxy
  have transfer : ∀ {a b : {x | x ∉ D.removed U}},
      (G.induce {x | x ∉ D.removed U}).Walk a b →
      (T.induce {j | j ∉ U}).Reachable
        ⟨D.owner a.val, D.owner_not_selected U a.property⟩
        ⟨D.owner b.val, D.owner_not_selected U b.property⟩ := by
    intro a b q
    induction q with
    | nil => exact .refl _
    | @cons a c b h _ ih =>
        obtain ⟨_, _, hac⟩ :=
          D.adjacent_owners_outside_connected U a.property c.property h
        exact hac.trans ih
  exact ⟨D.owner_not_selected U hx, D.owner_not_selected U hy, transfer p⟩

variable [Fintype V] [Fintype J]

noncomputable def ownerWeight (j : J) : ℕ :=
  (Finset.univ.filter (fun x => D.owner x = j)).card

omit [Fintype J] in
theorem ownerWeight_sum (K : Finset J) :
    ∑ j ∈ K, D.ownerWeight j =
      (Finset.univ.filter (fun x => D.owner x ∈ K)).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter Finset.univ K D.owner

theorem total_ownerWeight : ∑ j, D.ownerWeight j = Fintype.card V := by
  rw [D.ownerWeight_sum]
  simp

theorem component_card_le_ownerWeight (U : Finset J) (x : V) :
    (componentSet G (D.removed U) x).card ≤
      ∑ j ∈ componentSet T U (D.owner x), D.ownerWeight j := by
  rw [D.ownerWeight_sum]
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (mem_componentSet T U _ _).mpr
      (D.owners_outside_connected U ((mem_componentSet G _ _ _).mp hy))⟩

omit [Fintype V] [Fintype J] in
theorem removed_card_le (U : Finset J) (h : ℕ) (hbag : ∀ j, (D.bag j).card ≤ h) :
    (D.removed U).card ≤ h * U.card := by
  calc
    _ ≤ ∑ j ∈ U, (D.bag j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ U, h := Finset.sum_le_sum fun j _ => hbag j
    _ = _ := by simp [Nat.mul_comm]

/-- Weighted fragmentation of the decomposition tree transfers to unweighted
fragmentation of the original graph, paying at most one bag per selected node.
The weighted tree fragmentation hypothesis is explicit here; its existence is
a separate combinatorial theorem, not part of `TreeDecomposition`. -/
theorem fragmentation_transfer (U : Finset J) (h L : ℕ)
    (hbag : ∀ j, (D.bag j).card ≤ h)
    (hfrag : ∀ j, ∑ k ∈ componentSet T U j, D.ownerWeight k ≤ L) :
    (D.removed U).card ≤ h * U.card ∧
      ∀ C ∈ graphComponents G (D.removed U), C.card ≤ L := by
  refine ⟨D.removed_card_le U h hbag, ?_⟩
  intro C hC
  obtain ⟨x, _, rfl⟩ := (mem_graphComponents G _ C).mp hC
  exact (D.component_card_le_ownerWeight U x).trans (hfrag (D.owner x))

end TreeDecomposition
end TransposeFollowup
