import MergeDepth.Q91

/-!
# Degrees and distances in paired incidence graphs

Facts about the fifth paper's paired incidence graph `pairedIncidenceGraph N`, used for the degree
bounds of `AboveHalfRate.Descent` and `AboveHalfRate.BlowUp`: the degree of the right port `inr q`
is the size of the recovery set `N q`, the degree of the left port `inl p` is the number of
recovery sets containing `p`, and distances do not increase under graph homomorphisms. The degree
statements hold for every `Fintype` instance on the neighbour sets, so they apply to the classical
instances used in the formal statement of Question 9.1.
-/

namespace AboveHalf

open Finset DirectedRecovery

set_option autoImplicit false

section Degrees

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The degree of a right port is the size of its recovery set. -/
theorem degree_inr (N : V → Finset V) (q : V)
    [Fintype ((pairedIncidenceGraph N).neighborSet (Sum.inr q))] :
    (pairedIncidenceGraph N).degree (Sum.inr q) = (N q).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (pairedIncidenceGraph N).neighborFinset (Sum.inr q) =
      (N q).map Function.Embedding.inl := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    rcases w with p | p <;> simp
  rw [this, Finset.card_map]

/-- The degree of a left port is the number of recovery sets containing it. -/
theorem degree_inl (N : V → Finset V) (p : V)
    [Fintype ((pairedIncidenceGraph N).neighborSet (Sum.inl p))] :
    (pairedIncidenceGraph N).degree (Sum.inl p) =
      (Finset.univ.filter (fun q => p ∈ N q)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (pairedIncidenceGraph N).neighborFinset (Sum.inl p) =
      (Finset.univ.filter (fun q => p ∈ N q)).map Function.Embedding.inr := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    rcases w with q | q <;> simp
  rw [this, Finset.card_map]

/-- A degree bound for all ports from bounds on recovery-set sizes and on reuse. -/
theorem degree_le_of_bounds (N : V → Finset V) {Δ : ℕ}
    (hout : ∀ q, (N q).card ≤ Δ) (hin : ∀ p, (Finset.univ.filter (fun q => p ∈ N q)).card ≤ Δ)
    (v : V ⊕ V) [Fintype ((pairedIncidenceGraph N).neighborSet v)] :
    (pairedIncidenceGraph N).degree v ≤ Δ := by
  rcases v with p | q
  · rw [degree_inl]; exact hin p
  · rw [degree_inr]; exact hout q

end Degrees

/-- Distances do not increase under graph homomorphisms. -/
theorem edist_map_le {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} (f : G →g H)
    (u v : α) : H.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe hn.symm
    calc H.edist (f u) (f v) ≤ (p.map f).length := SimpleGraph.edist_le _
      _ = G.edist u v := by rw [SimpleGraph.Walk.length_map, hp, hn]

end AboveHalf
