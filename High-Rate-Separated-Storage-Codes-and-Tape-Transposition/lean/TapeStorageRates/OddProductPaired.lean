import TapeStorageRates.OddProductGraph
import DirectedRecovery.PathPacking
import AboveHalfRate.Incidence

/-! # From odd product walks to paired-distance separation

A relation supported on a simple graph inherits its odd closed-walk lower
bounds as paired-distance lower bounds. Both incidence degrees inherit the
graph's degree bound. No storage-code or matrix hypothesis is needed here.
-/

namespace TapeStorageRates

open Finset DirectedRecovery

set_option autoImplicit false

variable {V : Type*} {G : SimpleGraph V}

/-- Forgetting the incidence port maps a graph-supported relation to the graph. -/
abbrev pairedProjection (N : V → Finset V) (hN : ∀ q p, p ∈ N q → G.Adj q p) :
    pairedIncidenceGraph N →g G where
  toFun := Sum.elim id id
  map_rel' := by
    intro u v h
    rcases u with u | u <;> rcases v with v | v
    · exact (pairedIncidenceGraph_not_adj_left_left N u v h).elim
    · exact (hN v u h).symm
    · exact hN u v h
    · exact (pairedIncidenceGraph_not_adj_right_right N u v h).elim

@[simp] theorem pairedProjection_inl (N : V → Finset V)
    (hN : ∀ q p, p ∈ N q → G.Adj q p) (x : V) :
    pairedProjection N hN (Sum.inl x) = x := rfl

@[simp] theorem pairedProjection_inr (N : V → Finset V)
    (hN : ∀ q p, p ∈ N q → G.Adj q p) (x : V) :
    pairedProjection N hN (Sum.inr x) = x := rfl

/-- An odd-walk lower bound for the containing graph bounds each prescribed
opposite-port distance of the supported relation. -/
theorem not_paired_edist_le_of_odd_closed {K : ℕ}
    (hG : ∀ v (w : G.Walk v v), Odd w.length → K < w.length)
    (N : V → Finset V) (hN : ∀ q p, p ∈ N q → G.Adj q p) (x : V) :
    ¬ (pairedIncidenceGraph N).edist (Sum.inl x) (Sum.inr x) ≤ K := by
  intro h
  obtain ⟨n, hn, hnK⟩ := ENat.le_natCast_iff.mp h
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hn
  have hodd := paired_walk_length_odd N x x w
  let w' : G.Walk x x := (w.map (pairedProjection N hN)).copy
    (pairedProjection_inl N hN x) (pairedProjection_inr N hN x)
  have hlen : w'.length = w.length :=
    (SimpleGraph.Walk.length_copy _ _ _).trans (SimpleGraph.Walk.length_map _ _)
  have hlt := hG x w'
    (by rwa [hlen])
  rw [hlen, hw] at hlt
  omega

/-- The odd product preserves the same paired-distance lower bound for every
relation supported on its edges. -/
theorem oddProduct_not_paired_edist_le [DecidableEq V]
    {I : Type*} [Fintype I] {K : ℕ}
    (hG : ∀ v (w : G.Walk v v), Odd w.length → K < w.length)
    (N : (I → V) → Finset (I → V))
    (hN : ∀ q p, p ∈ N q → (oddProductGraph G I).Adj q p) (x : I → V) :
    ¬ (pairedIncidenceGraph N).edist (Sum.inl x) (Sum.inr x) ≤ K :=
  not_paired_edist_le_of_odd_closed
    (fun _ w hw => OddProductGraph.odd_closed_length_gt hG w hw) N hN x

section Degree

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Both incidence degrees of a graph-supported relation are bounded by the
same graph degree cap, even if the relation is not symmetric. -/
theorem paired_degree_le_of_graph {D : ℕ} (hD : ∀ v, G.degree v ≤ D)
    (N : V → Finset V) (hN : ∀ q p, p ∈ N q → G.Adj q p)
    (v : V ⊕ V) [Fintype ((pairedIncidenceGraph N).neighborSet v)] :
    (pairedIncidenceGraph N).degree v ≤ D := by
  classical
  apply AboveHalf.degree_le_of_bounds N _ _ v
  · intro q
    apply (card_le_card (show N q ⊆ G.neighborFinset q from ?_)).trans
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hD q)
    intro p hp
    exact (G.mem_neighborFinset q p).mpr (hN q p hp)
  · intro p
    apply (card_le_card (show (univ.filter fun q => p ∈ N q) ⊆ G.neighborFinset p from ?_)).trans
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hD p)
    intro q hq
    exact (G.mem_neighborFinset p q).mpr (hN q p (mem_filter.mp hq).2).symm

end Degree

end TapeStorageRates
