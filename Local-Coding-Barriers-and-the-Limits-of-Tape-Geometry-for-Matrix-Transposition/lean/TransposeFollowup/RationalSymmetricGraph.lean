import TransposeFollowup.RationalFamilyGraph

/-! The computed rational inverse family produces exactly the symmetrized
graph used in the continuous expansion proof. Existence of an expanding
input family and a native bit-cost bound remain separate obligations. -/

namespace TransposeFollowup

open Classical Set MeasureTheory
set_option autoImplicit false

def rationalSymmetricFamily {c : ℕ} (F : Fin c → RationalMobius) : Fin (c + c) → RationalMobius :=
  Fin.addCases F (fun p => (F p).inverse)

theorem rationalSymmetricEdges_eq {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    rationalFamilyEdges (rationalSymmetricFamily F) n =
      overlapEdges (symmetrizedMaps (rationalFamilyMaps F)) n := by
  rw [rationalFamilyEdges_eq]
  ext e
  obtain ⟨i, j⟩ := e
  rw [mem_symmetrized_overlap, mem_overlapEdges, mem_overlapEdges, mem_overlapEdges]
  simp only [rationalFamilyMaps, BoundedMonotoneMap.widen_overlap]
  dsimp only [BoundedMonotoneMap.Overlap, RationalMobius.bounded]
  constructor
  · rintro ⟨p, hp⟩
    induction p using Fin.addCases with
    | left p =>
      exact Or.inl ⟨p, by simpa only [rationalSymmetricFamily, Fin.addCases_left] using hp⟩
    | right p =>
      have hi := (F p).inverse_overlap_iff i j
      dsimp only [BoundedMonotoneMap.Overlap, RationalMobius.bounded] at hi
      exact Or.inr ⟨p, hi.mp
        (by simpa only [rationalSymmetricFamily, Fin.addCases_right] using hp)⟩
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · exact ⟨Fin.castAdd c p, by simpa only [rationalSymmetricFamily, Fin.addCases_left] using hp⟩
    · have hi := (F p).inverse_overlap_iff i j
      dsimp only [BoundedMonotoneMap.Overlap, RationalMobius.bounded] at hi
      exact ⟨Fin.natAdd c p, by
        simpa only [rationalSymmetricFamily, Fin.addCases_right] using (hi.mpr hp)⟩

theorem rationalSymmetricStream_toFinset {c : ℕ} (F : Fin c → RationalMobius) (n : ℕ) :
    (rationalFamilyEdgeStream (rationalSymmetricFamily F) n).toFinset =
      overlapEdges (symmetrizedMaps (rationalFamilyMaps F)) n := by
  rw [rationalFamilyEdgeStream_toFinset, ← rationalFamilyEdges_eq, rationalSymmetricEdges_eq]

theorem rationalSymmetric_vertex_expansion {c h : ℕ} (F : Fin c → RationalMobius)
    (hh : 0 < h)
    (hmap : ∀ p, MapsTo (rationalFamilyMaps F p).map (rationalFamilyMaps F p).domain (Icc (0 : ℝ) 1))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 →
      (1 + eps) * volume.real S ≤ volume.real (mapImageUnion (rationalFamilyMaps F) S))
    (S : Finset (Fin (2 * (2 * h)))) (hS : 2 * S.card ≤ Fintype.card (Fin (2 * (2 * h)))) :
    eps / 2 * S.card ≤
      (outsideNeighbors (OrderedBipartite.graph
        (rationalFamilyEdges (rationalSymmetricFamily F) (2 * h))) S).card := by
  rw [rationalSymmetricEdges_eq]
  exact symmetrizedGraph_vertex_expansion (rationalFamilyMaps F) hh hmap eps heps hforward S hS

end TransposeFollowup
