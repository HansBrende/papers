import LeanMachine.FlowWalks
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Physical walk volume and ordinary undirected distance. Parallel edges
and repeated traversals keep their loads; graph distance forgets only the
edge identities. Loops are allowed and can only increase walk length. -/

namespace LeanMachine.FiniteFlow.Network

open Finset
open scoped BigOperators Classical
noncomputable section

variable {V E : Type*} (G : Network V E)

def pathLength {s t : V} (p : G.Path s t) : ℕ :=
  @Quiver.Path.length V G.quiver s t p

theorem sum_pathFlow [Fintype E] {s t : V} (p : G.Path s t) :
    ∑ e, G.pathFlow p e = (G.pathLength p : ℝ) := by
  induction p with
  | nil => simp [pathFlow, pathLength]
  | cons p e ih =>
    simp [pathFlow_cons, Pi.add_apply, sum_add_distrib, unit, ih, pathLength]

/-- Both orientations contribute, so physical volume is exactly walk length. -/
theorem sum_walkLoad [Fintype E] {s t : V} (p : G.bidirected.Path s t) :
    ∑ e, G.walkLoad p e = (G.bidirected.pathLength p : ℝ) := by
  simpa only [walkLoad, sum_add_distrib, Fintype.sum_sum_type] using
    G.bidirected.sum_pathFlow p

/-- The underlying undirected simple graph has exactly the original
nonloop adjacencies, in either direction. -/
def graph : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => ∃ e, G.source e = u ∧ G.target e = v

theorem graph_adj {u v : V} : G.graph.Adj u v ↔ u ≠ v ∧
    ((∃ e, G.source e = u ∧ G.target e = v) ∨
      ∃ e, G.source e = v ∧ G.target e = u) := Iff.rfl

theorem edge_edist_le_one (e : E) : G.graph.edist (G.source e) (G.target e) ≤ 1 := by
  apply SimpleGraph.edist_le_one_iff_adj_or_eq.mpr
  by_cases he : G.source e = G.target e
  · exact Or.inr he
  · exact Or.inl ⟨he, Or.inl ⟨e, rfl, rfl⟩⟩

/-- No acyclicity, connectedness or capacity assumption is needed. -/
theorem edist_le_walk_length {s t : V} (p : G.bidirected.Path s t) :
    G.graph.edist s t ≤ (G.bidirected.pathLength p : ℕ∞) := by
  have hstep (e : E ⊕ E) :
      G.graph.edist (G.bidirected.source e) (G.bidirected.target e) ≤ 1 := by
    cases e with
    | inl e => exact G.edge_edist_le_one e
    | inr e =>
      change G.graph.edist (G.target e) (G.source e) ≤ 1
      rw [SimpleGraph.edist_comm]
      exact G.edge_edist_le_one e
  induction p with
  | nil => simp [pathLength]
  | @cons t v p e ih =>
    have he : G.graph.edist t v ≤ 1 := by
      simpa only [e.property.1, e.property.2] using hstep e.val
    calc
      _ ≤ G.graph.edist s t + G.graph.edist t v := SimpleGraph.edist_triangle
      _ ≤ (G.bidirected.pathLength p : ℕ∞) + 1 := add_le_add ih he
      _ = _ := by simp [pathLength]

end
end LeanMachine.FiniteFlow.Network
