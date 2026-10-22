import TransposeFollowup.HalfGridExpansion
import TransposeFollowup.SymmetricOverlap

/-! Neighbor expansion capped at the real half-size yields the same
epsilon/2 ordinary vertex expansion at every size, including odd sizes.
Continuous expansion provides precisely this stronger capped hypothesis. -/
namespace TransposeFollowup
open Classical MeasureTheory Set
set_option autoImplicit false

theorem two_sided_capped_expansion_count {n : ℕ} (edges : Finset (Fin n × Fin n))
    (eps : ℝ) (heps : 0≤eps)
    (hR : ∀ A : Finset (Fin n),(1+eps)*min (A.card:ℝ) ((n:ℝ)/2)≤(bipartiteRight edges A).card)
    (hL : ∀ B : Finset (Fin n),(1+eps)*min (B.card:ℝ) ((n:ℝ)/2)≤(bipartiteLeft edges B).card)
    (A B : Finset (Fin n)) (hab : A.card+B.card≤n) :
    eps/2*(A.card+B.card:ℕ)≤
      ((bipartiteRight edges A \ B).card:ℝ)+(bipartiteLeft edges B \ A).card := by
  have htotal : (A.card:ℝ)+B.card≤n:=by exact_mod_cast hab
  have hscale:=mul_le_mul_of_nonneg_left htotal heps
  have hX : (0:ℝ)≤(bipartiteRight edges A \ B).card:=Nat.cast_nonneg _
  have hY : (0:ℝ)≤(bipartiteLeft edges B \ A).card:=Nat.cast_nonneg _
  have hdA : ((bipartiteRight edges A).card:ℝ)≤(bipartiteRight edges A \ B).card+(B.card:ℝ) := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card (s:=bipartiteRight edges A) (t:=B)
  have hdB : ((bipartiteLeft edges B).card:ℝ)≤(bipartiteLeft edges B \ A).card+(A.card:ℝ) := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card (s:=bipartiteLeft edges B) (t:=A)
  have hr:=hR A
  have hl:=hL B
  push_cast
  by_cases ha : (A.card:ℝ)≤(n:ℝ)/2
  · by_cases hb : (B.card:ℝ)≤(n:ℝ)/2
    · rw [min_eq_left ha] at hr
      rw [min_eq_left hb] at hl
      have hp : 0≤eps*((A.card:ℝ)+B.card):=mul_nonneg heps (by positivity)
      nlinarith
    · rw [min_eq_right (le_of_not_ge hb)] at hl
      nlinarith
  · rw [min_eq_right (le_of_not_ge ha)] at hr
    have hb : (B.card:ℝ)≤(n:ℝ)/2:=by linarith
    nlinarith

theorem OrderedBipartite.vertex_expansion_capped {n : ℕ} (edges : Finset (Fin n × Fin n))
    (eps : ℝ) (heps : 0≤eps)
    (hR : ∀ A : Finset (Fin n),(1+eps)*min (A.card:ℝ) ((n:ℝ)/2)≤(bipartiteRight edges A).card)
    (hL : ∀ B : Finset (Fin n),(1+eps)*min (B.card:ℝ) ((n:ℝ)/2)≤(bipartiteLeft edges B).card)
    (S : Finset (Fin (2*n))) (hS : 2*S.card≤Fintype.card (Fin (2*n))) :
    eps/2*S.card≤(outsideNeighbors (graph edges) S).card := by
  have hp:=card_parts S
  have hs : (leftPart S).card+(rightPart S).card≤n := by
    simp only [Fintype.card_fin] at hS
    omega
  have he:=two_sided_capped_expansion_count edges eps heps hR hL (leftPart S) (rightPart S) hs
  rw [hp] at he
  exact he.trans (by exact_mod_cast boundary_count_le edges S)

theorem symmetrizedGraph_vertex_expansion_all_sizes {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hn : 0<n) (hmap : ∀ p,MapsTo (F p).map (F p).domain (Icc (0:ℝ) 1))
    (eps : ℝ) (heps : 0≤eps)
    (hforward : ∀ S : Set ℝ,MeasurableSet S → S⊆Icc (0:ℝ) 1 → volume.real S≤1/2 →
      (1+eps)*volume.real S≤volume.real (mapImageUnion F S))
    (S : Finset (Fin (2*n))) (hS : 2*S.card≤Fintype.card (Fin (2*n))) :
    eps/2*S.card≤(outsideNeighbors (overlapGraph (symmetrizedMaps F) n) S).card := by
  apply OrderedBipartite.vertex_expansion_capped _ eps heps ?_ ?_ S hS
  · intro A
    exact (overlap_right_capped F hn hmap eps hforward A).trans (by
      exact_mod_cast Finset.card_le_card (original_neighbors_le_symmetrized F A).1)
  · intro A
    exact (overlap_right_capped F hn hmap eps hforward A).trans (by
      exact_mod_cast Finset.card_le_card (original_neighbors_le_symmetrized F A).2)

end TransposeFollowup
