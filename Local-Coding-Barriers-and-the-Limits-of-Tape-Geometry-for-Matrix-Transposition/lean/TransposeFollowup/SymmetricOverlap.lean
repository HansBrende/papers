import TransposeFollowup.OverlapExpansion

/-! Adjoining restricted inverses symmetrizes the overlap relation. The same
integer distortion bound works for inverse maps, so the existing residue
coloring and page compiler apply unchanged to the doubled map family. -/

namespace TransposeFollowup

open Classical Set MeasureTheory
set_option autoImplicit false

namespace BoundedMonotoneMap

noncomputable def inverse {B : ℕ} (F : BoundedMonotoneMap B) : BoundedMonotoneMap B where
  domain := F.map '' F.domain
  map := Function.invFunOn F.map F.domain
  strictMono := by
    intro x hx y hy hxy
    have hxm := Function.invFunOn_mem hx
    have hym := Function.invFunOn_mem hy
    have hxe := Function.invFunOn_eq hx
    have hye := Function.invFunOn_eq hy
    by_contra h
    have hm := F.strictMono.monotoneOn hym hxm (le_of_not_gt h)
    rw [hxe, hye] at hm
    exact (not_le_of_gt hxy) hm
  forward := by
    intro x hx y hy
    have h := F.backward _ (Function.invFunOn_mem hx) _ (Function.invFunOn_mem hy)
    rwa [Function.invFunOn_eq hx, Function.invFunOn_eq hy] at h
  backward := by
    intro x hx y hy
    have h := F.forward _ (Function.invFunOn_mem hx) _ (Function.invFunOn_mem hy)
    rwa [Function.invFunOn_eq hx, Function.invFunOn_eq hy] at h

theorem inverse_apply {B : ℕ} (F : BoundedMonotoneMap B) {x : ℝ} (hx : x ∈ F.domain) :
    F.inverse.map (F.map x) = x := F.strictMono.injOn.leftInvOn_invFunOn hx

theorem inverse_overlap {B n : ℕ} (F : BoundedMonotoneMap B) (i j : Fin n) :
    F.inverse.Overlap i j ↔ F.Overlap j i := by
  constructor
  · rintro ⟨y, hy, hyi, hyj⟩
    refine ⟨F.inverse.map y, Function.invFunOn_mem hy, hyj, ?_⟩
    simpa only [inverse, Function.invFunOn_eq hy] using hyi
  · rintro ⟨x, hx, hxj, hxi⟩
    refine ⟨F.map x, ⟨x, hx, rfl⟩, hxi, ?_⟩
    simpa only [F.inverse_apply hx] using hxj

end BoundedMonotoneMap

noncomputable def symmetrizedMaps {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) :
    Fin (c + c) → BoundedMonotoneMap B := Fin.addCases F (fun p => (F p).inverse)

theorem mem_symmetrized_overlap {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (i j : Fin n) :
    (i, j) ∈ overlapEdges (symmetrizedMaps F) n ↔
      (i, j) ∈ overlapEdges F n ∨ (j, i) ∈ overlapEdges F n := by
  simp only [mem_overlapEdges]
  constructor
  · rintro ⟨p, hp⟩
    induction p using Fin.addCases with
    | left p => exact Or.inl ⟨p, by simpa only [symmetrizedMaps, Fin.addCases_left] using hp⟩
    | right p =>
      exact Or.inr ⟨p, ((F p).inverse_overlap i j).mp
        (by simpa only [symmetrizedMaps, Fin.addCases_right] using hp)⟩
  · rintro (⟨p, hp⟩ | ⟨p, hp⟩)
    · exact ⟨Fin.castAdd c p, by simpa only [symmetrizedMaps, Fin.addCases_left] using hp⟩
    · exact ⟨Fin.natAdd c p, by
        simpa only [symmetrizedMaps, Fin.addCases_right] using ((F p).inverse_overlap i j).mpr hp⟩

theorem symmetrized_overlap_symmetric {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (i j : Fin n) :
    (i, j) ∈ overlapEdges (symmetrizedMaps F) n ↔
      (j, i) ∈ overlapEdges (symmetrizedMaps F) n := by
  rw [mem_symmetrized_overlap, mem_symmetrized_overlap, or_comm]

theorem original_neighbors_le_symmetrized {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (A : Finset (Fin n)) :
    bipartiteRight (overlapEdges F n) A ⊆ bipartiteRight (overlapEdges (symmetrizedMaps F) n) A ∧
    bipartiteRight (overlapEdges F n) A ⊆ bipartiteLeft (overlapEdges (symmetrizedMaps F) n) A := by
  constructor
  · intro j hj
    obtain ⟨i, hi, he⟩ := (mem_bipartiteRight _ A j).mp hj
    exact (mem_bipartiteRight _ A j).mpr ⟨i, hi, (mem_symmetrized_overlap F i j).mpr (Or.inl he)⟩
  · intro j hj
    obtain ⟨i, hi, he⟩ := (mem_bipartiteRight _ A j).mp hj
    exact (mem_bipartiteLeft _ A j).mpr ⟨i, hi, (mem_symmetrized_overlap F j i).mpr (Or.inr he)⟩

theorem symmetrizedGraph_vertex_expansion {c B h : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hh : 0 < h) (hmap : ∀ p, MapsTo (F p).map (F p).domain (Icc (0 : ℝ) 1))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 → (1 + eps) * volume.real S ≤ volume.real (mapImageUnion F S))
    (S : Finset (Fin (2 * (2 * h)))) (hS : 2 * S.card ≤ Fintype.card (Fin (2 * (2 * h)))) :
    eps / 2 * S.card ≤ (outsideNeighbors (overlapGraph (symmetrizedMaps F) (2 * h)) S).card := by
  have hr : ∀ A : Finset (Fin (2 * h)), A.card ≤ h →
      (1 + eps) * A.card ≤ (bipartiteRight (overlapEdges F (2 * h)) A).card :=
    fun A hA => overlap_right_expansion F (by omega) hmap eps hforward A (by omega)
  apply OrderedBipartite.vertex_expansion _ eps heps ?_ ?_ S hS
  · intro A hA
    exact (hr A hA).trans (by
      exact_mod_cast (Finset.card_le_card (original_neighbors_le_symmetrized F A).1))
  · intro A hA
    exact (hr A hA).trans (by
      exact_mod_cast (Finset.card_le_card (original_neighbors_le_symmetrized F A).2))

end TransposeFollowup
