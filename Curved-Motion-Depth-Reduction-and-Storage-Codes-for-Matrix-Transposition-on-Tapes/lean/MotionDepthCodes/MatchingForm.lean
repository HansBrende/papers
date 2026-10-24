import MotionDepthCodes.Subcubic
import LeanMachine.TutteBerge.MatchingNumber

/-!
# Theorem S, matching form

The matching form of Theorem S (`thm:S-barrier` in the paper). On a triangle-free graph of maximum
degree at most `3`, every matrix with unit diagonal and off-diagonal support in the edges has
nullity at most `ν(G)`, the matching number, and some such matrix has nullity exactly `ν(G)`. So
the minrank over every field is `|V| − ν(G)`.

The upper bound combines the barrier form `finrank_ker_le_barrier` with the barrier form of the
Tutte–Berge formula, `SimpleGraph.exists_card_add_sum_card_div_two_eq_matchingNumber`, from
lean-machine (`LeanMachine/TutteBerge/`). There the Tutte–Berge formula is a port of
J. P. Traverso Gianini's formalization (github.com/jtraverso/berge-matching), which derives it
from Mathlib's Tutte theorem. The lower bound is the matching code of a maximum matching.
-/

namespace MotionDepthCodes

open Module

variable {V F : Type*} [Fintype V] [DecidableEq V] [Field F]

/-- **The Tutte–Berge formula, barrier form.** The minimum over `U` of `|U| + ∑_B ⌊|B|/2⌋`, with the
components of `G − U` as blocks, is the matching number `ν(G)`. -/
theorem matchingNumber_eq_min_barrier (G : SimpleGraph V) :
    (∀ U : Finset V, G.matchingNumber ≤ U.card + ∑ B ∈ G.componentBlocks U, B.card / 2) ∧
      ∃ U : Finset V, U.card + ∑ B ∈ G.componentBlocks U, B.card / 2 = G.matchingNumber :=
  ⟨G.matchingNumber_le_card_add_sum_card_div_two,
    G.exists_card_add_sum_card_div_two_eq_matchingNumber⟩

/-- **Matching form of the barrier bound.** If every vertex satisfies (★★), the nullity is at most
the matching number. -/
theorem finrank_ker_le_matchingNumber [DecidableEq F] {G : SimpleGraph V} {M : Matrix V V F}
    (hyp : ThmSHyp M) (hpat : ∀ v u, u ∈ recSet M v → G.Adj v u) (hstar : ∀ v, Star M v) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ G.matchingNumber := by
  obtain ⟨U, hU⟩ := G.exists_card_add_sum_card_div_two_eq_matchingNumber
  have h := finrank_ker_le_barrier hyp hpat U (fun v _ => hstar v) (G.componentBlocks U)
    (G.biUnion_componentBlocks U) (G.pairwiseDisjoint_componentBlocks U)
    (G.not_adj_of_mem_componentBlocks U)
  omega

/-- **Theorem S, matching form, upper bound.** On a triangle-free graph of maximum degree at most
`3`, every matrix with unit diagonal and off-diagonal support in the edges has nullity at most
`ν(G)`, over every field. -/
theorem finrank_ker_le_matchingNumber_of_degree_le_three {G : SimpleGraph V} [DecidableRel G.Adj]
    {M : Matrix V V F} (hdiag : ∀ v, M v v = 1)
    (hpat : ∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) (htri : G.CliqueFree 3)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    finrank F (LinearMap.ker M.mulVecLin) ≤ G.matchingNumber := by
  classical
  have hadj : ∀ v u, u ∈ recSet M v → G.Adj v u := by
    intro v u hu
    obtain ⟨hne, hM⟩ := mem_recSet.mp hu
    by_contra h
    exact hM (hpat v u (Ne.symm hne) h)
  exact finrank_ker_le_matchingNumber (thmSHyp_of_cliqueFree hdiag hpat htri) hadj
    (star_of_degree_le_three hpat hdeg)

/-- **The matching code of a maximum matching.** On every graph, over every field, some matrix with
unit diagonal and off-diagonal support in the edges has nullity at least `ν(G)`. -/
theorem exists_pattern_matchingNumber_le_finrank_ker {G : SimpleGraph V} [DecidableRel G.Adj] :
    ∃ M : Matrix V V F, (∀ v, M v v = 1) ∧ (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) ∧
      G.matchingNumber ≤ finrank F (LinearMap.ker M.mulVecLin) := by
  obtain ⟨N, hN, hcard⟩ := G.exists_isMatching_ncard_eq_matchingNumber
  obtain ⟨u, w, hadj, hinj⟩ := hN.exists_fin_enum
  obtain ⟨M, hdiag, hpat, hle⟩ := exists_pattern_finrank_ker_ge_of_matching (F := F) u w
    (fun i => N.adj_sub (hadj i)) hinj
  exact ⟨M, hdiag, hpat, hcard ▸ hle⟩

/-- **Theorem S, matching form.** For a triangle-free graph of maximum degree at most `3`, the
minrank over every field is `|V| − ν(G)`: every matrix with unit diagonal and off-diagonal support
in the edges has rank at least `|V| − ν(G)`, and some such matrix has rank exactly `|V| − ν(G)`. -/
theorem minrank_eq_card_sub_matchingNumber {G : SimpleGraph V} [DecidableRel G.Adj]
    (htri : G.CliqueFree 3) (hdeg : ∀ v, G.degree v ≤ 3) :
    (∀ M : Matrix V V F, (∀ v, M v v = 1) → (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) →
        Fintype.card V - G.matchingNumber ≤ M.rank) ∧
      ∃ M : Matrix V V F, (∀ v, M v v = 1) ∧ (∀ v u, v ≠ u → ¬ G.Adj v u → M v u = 0) ∧
        M.rank = Fintype.card V - G.matchingNumber := by
  have hrank : ∀ M : Matrix V V F,
      M.rank + finrank F (LinearMap.ker M.mulVecLin) = Fintype.card V := by
    intro M
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h
    exact h
  refine ⟨fun M hdiag hpat => ?_, ?_⟩
  · have h1 := finrank_ker_le_matchingNumber_of_degree_le_three hdiag hpat htri hdeg
    have h2 := hrank M
    omega
  · obtain ⟨M, hdiag, hpat, hge⟩ := exists_pattern_matchingNumber_le_finrank_ker (F := F) (G := G)
    have h1 := finrank_ker_le_matchingNumber_of_degree_le_three hdiag hpat htri hdeg
    have h2 := hrank M
    exact ⟨M, hdiag, hpat, by omega⟩

end MotionDepthCodes
