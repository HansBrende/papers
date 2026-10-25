import SubcubicMemo.HigherRankArcs
import LeanMachine.SubspaceFamilies

/-! Three consecutive high-rank rows force exact tight support. -/

namespace SubcubicMemo.LowRank

open Module Finset LeanMachine.SubspaceRecovery LeanMachine.SubspaceDefect
open scoped BigOperators Classical

variable {V K W : Type*} [Fintype V] [DecidableEq V] [Field K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {G : SimpleGraph V} [DecidableRel G.Adj] {U : V → Submodule K W}
  {r : Recovery U} (c : HighCore G U r)
include c

theorem HighCore.no_high_reverse {v u : V} (h : High r v u) : ¬ High r u v := by
  intro hrev
  obtain ⟨w, hw, hh⟩ := c.high_successor h
  exact hw (c.oneHigh u w v hh hrev)

theorem HighCore.path_two_ne {a b d : V} (hab : High r a b) (hbd : High r b d) : a ≠ d := by
  rintro rfl
  exact c.no_high_reverse hab hbd

theorem HighCore.path_three_ne {a b d e : V}
    (hab : High r a b) (hbd : High r b d) (hde : High r d e) : a ≠ e := by
  rintro rfl
  exact c.triangle {a, b, d} (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨c.high_adj hab, (c.high_adj hde).symm, c.high_adj hbd⟩)

/-- The third neighbor is an actual original graph vertex; no contraction or
support completion is performed. -/
theorem HighCore.third_neighbor {p v u : V} (hpv : High r p v) (hvu : High r v u) :
    ∃ z, z ≠ p ∧ z ≠ u ∧ z ≠ v ∧ G.neighborFinset v = {p, u, z} := by
  have hp : p ∈ G.neighborFinset v := (G.mem_neighborFinset v p).mpr (c.high_adj hpv).symm
  have hu : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr (c.high_adj hvu)
  have hpu := c.path_two_ne hpv hvu
  have hdeg := (c.high_remainder hvu).1
  have hc : (((G.neighborFinset v).erase u).erase p).card = 1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨hpu, hp⟩), card_erase_of_mem hu,
      SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨z, hz⟩ := card_eq_one.mp hc
  have hzmem : z ∈ ((G.neighborFinset v).erase u).erase p := by rw [hz]; simp
  obtain ⟨hzp, hzmem⟩ := mem_erase.mp hzmem
  obtain ⟨hzu, hzN⟩ := mem_erase.mp hzmem
  have hzv := ((G.mem_neighborFinset v z).mp hzN).ne.symm
  refine ⟨z, hzp, hzu, hzv, ?_⟩
  have he : (G.neighborFinset v).erase u = {p, z} := by
    rw [← insert_erase (mem_erase.mpr ⟨hpu, hp⟩), hz]
  rw [← insert_erase hu, he]
  exact Finset.insert_comm u p {z}

theorem HighCore.high_target_le {v u : V} (h : High r v u) (S : Submodule K W)
    (hv : U v ≤ S)
    (hrest : ∀ w, w ≠ u → LinearMap.range (r.component v w) ≤ S) : U u ≤ S := by
  rw [← (c.high_dimensions h).2.2.2]
  exact r.component_range_le_of_rest v u S hv hrest

theorem HighCore.third_image_line {p v u z : V}
    (hpv : High r p v) (hvu : High r v u)
    (hzp : z ≠ p) (hzu : z ≠ u) (hzv : z ≠ v)
    (hN : G.neighborFinset v = {p, u, z}) :
    finrank K (LinearMap.range (r.component v p)) = 1 ∧
      finrank K (LinearMap.range (r.component v z)) = 1 := by
  have hpu := c.path_two_ne hpv hvu
  have hp : p ∈ (G.neighborFinset v).erase u := by simp [hN, hpu]
  have hz : z ∈ (G.neighborFinset v).erase u := by simp [hN, hzu]
  exact ⟨(c.high_remainder hvu).2.2 p hp, (c.high_remainder hvu).2.2 z hz⟩

end SubcubicMemo.LowRank
