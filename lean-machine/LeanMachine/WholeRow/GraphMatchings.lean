import LeanMachine.WholeRow.InducedMatchings
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Graph induced matchings give whole-row parity codes

Partition the edges of a simple graph into nonempty induced matchings, in
Mathlib's subgraph sense. Taking both orientations of every edge gives a
partition of the nonincident cells for the helper map of non-neighbours
(including the diagonal). The shared parity-code construction then applies.
No graph-existence theorem or restriction on the matching sizes is assumed.
-/

namespace LeanMachine.WholeRow

open Finset
open scoped Classical
noncomputable section

variable {V κ : Type*}

/-- An edge partition into nonempty induced matchings. The unique membership
condition concerns unoriented edges, since each subgraph is symmetric. -/
structure GraphMatchingPartition (G : SimpleGraph V) (κ : Type*) where
  part : κ → G.Subgraph
  matching : ∀ k, (part k).IsMatching
  induced : ∀ k, (part k).IsInduced
  nonempty : ∀ k, ∃ u v, (part k).Adj u v
  covers : ∀ {u v}, G.Adj u v → ∃! k, (part k).Adj u v

variable [Fintype V] (G : SimpleGraph V)

/-- A column reads its own row and all its distinct non-neighbours. -/
def graphHelpers (j : V) : Finset V := univ.filter fun i => ¬ G.Adj i j

@[simp] theorem mem_graphHelpers (i j : V) : i ∈ graphHelpers G j ↔ ¬ G.Adj i j := by
  simp [graphHelpers]

theorem graphHelpers_reflexive (j : V) : j ∈ graphHelpers G j := by
  simp

theorem graphHelpers_symmetric (i j : V) :
    i ∈ graphHelpers G j ↔ j ∈ graphHelpers G i := by
  simp only [mem_graphHelpers, G.adj_comm]

/-- The exact forward window is the number of non-neighbours, with self included. -/
theorem graphHelpers_card_add_degree (j : V) :
    (graphHelpers G j).card + G.degree j = Fintype.card V := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset V))
    (p := fun i => G.Adj j i)
  have he : (univ.filter fun i => G.Adj j i) = G.neighborFinset j := by
    ext i
    simp
  rw [he, G.card_neighborFinset_eq_degree, card_univ] at h
  simpa only [graphHelpers, G.adj_comm, Nat.add_comm] using h

theorem graphHelpers_card_le_iff (j : V) (w : ℕ) :
    (graphHelpers G j).card ≤ w ↔ Fintype.card V ≤ G.degree j + w := by
  have h := graphHelpers_card_add_degree G j
  omega

namespace GraphMatchingPartition

variable {G} (P : GraphMatchingPartition G κ)

/-- Put both orientations of every edge of a matching in one parity block. -/
def toInducedMatchingPartition : InducedMatchingPartition (graphHelpers G) κ where
  support k := univ.filter fun e : V × V => (P.part k).Adj e.1 e.2
  nonempty k := by
    obtain ⟨u, v, huv⟩ := P.nonempty k
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, huv⟩⟩
  disjoint := by
    intro k l hkl
    apply disjoint_left.mpr
    intro e he hf
    have hk := (mem_filter.mp he).2
    have hl := (mem_filter.mp hf).2
    exact hkl ((P.covers hk.adj_sub).unique hk hl)
  nonincident := by
    intro k e he
    simpa only [mem_graphHelpers, not_not] using (mem_filter.mp he).2.adj_sub
  cross := by
    intro k e he f hf hne
    rw [mem_graphHelpers]
    intro hadj
    have he' := (mem_filter.mp he).2
    have hf' := (mem_filter.mp hf).2
    have hcross := P.induced k he'.fst_mem hf'.snd_mem hadj
    exact hne (Prod.ext ((P.matching k).eq_of_adj_right hcross hf')
      ((P.matching k).eq_of_adj_left he' hcross))
  covers := by
    intro e he
    have hadj : G.Adj e.1 e.2 := by simpa only [mem_graphHelpers, not_not] using he
    obtain ⟨k, hk, _⟩ := P.covers hadj
    exact ⟨k, mem_filter.mpr ⟨mem_univ _, hk⟩⟩

@[simp] theorem mem_support (k : κ) (e : V × V) :
    e ∈ P.toInducedMatchingPartition.support k ↔ (P.part k).Adj e.1 e.2 := by
  simp [toInducedMatchingPartition]

/-- Reversing an edge stays in the same parity block. -/
theorem swap_mem_support (k : κ) (e : V × V) :
    e.swap ∈ P.toInducedMatchingPartition.support k ↔
      e ∈ P.toInducedMatchingPartition.support k := by
  simp only [mem_support, Prod.fst_swap, Prod.snd_swap, (P.part k).adj_comm]

variable {F : Type*} [Field F]

/-- Over a field the checks are linear, with one coordinate per matching. -/
def linearChecks : (V × V → F) →ₗ[F] (κ → F) where
  toFun := P.toInducedMatchingPartition.encode
  map_add' := P.toInducedMatchingPartition.encode.map_add
  map_smul' := by
    intro a x
    ext k
    simp [DisjointSums.encode_apply, mul_sum]

/-- The zero-syndrome linear code has codimension exactly the number of
matchings, over any field, including infinite fields. -/
theorem finrank_ker_add [Fintype κ] :
    Module.finrank F (LinearMap.ker (P.linearChecks (F := F))) + Fintype.card κ =
      Fintype.card V * Fintype.card V := by
  have hr : LinearMap.range (P.linearChecks (F := F)) = ⊤ :=
    LinearMap.range_eq_top.mpr P.toInducedMatchingPartition.toDisjointSums.encode_surjective
  have h := (P.linearChecks (F := F)).finrank_range_add_finrank_ker
  rw [hr, finrank_top] at h
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Nat.add_comm] using h

end GraphMatchingPartition
end
end LeanMachine.WholeRow
