import TransposeFollowup.GridCellMeasure
import TransposeFollowup.BipartiteVertexExpansion

/-! Continuous expansion implies expansion of the actual finite overlap graph.
Images and restricted preimages are covered by neighbor cells plus the finite
grid boundary. Only the tested source cell unions need be measurable. -/

namespace TransposeFollowup

open Classical MeasureTheory Set
set_option autoImplicit false

def mapImageUnion {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (S : Set ℝ) : Set ℝ :=
  ⋃ p, (F p).map '' ((F p).domain ∩ S)

def mapPreimageUnion {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (S : Set ℝ) : Set ℝ :=
  ⋃ p, (F p).domain ∩ (F p).map ⁻¹' S

theorem mapImageUnion_grid_cover {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hn : 0 < n) (hmap : ∀ p, MapsTo (F p).map (F p).domain (Icc (0 : ℝ) 1))
    (A : Finset (Fin n)) :
    mapImageUnion F (gridCells A) ⊆
      gridCells (bipartiteRight (overlapEdges F n) A) ∪ gridBoundary n := by
  intro y hy
  obtain ⟨p, x, ⟨hxd, hxA⟩, rfl⟩ := Set.mem_iUnion.mp hy
  by_cases hb : (F p).map x ∈ gridBoundary n
  · exact Or.inr hb
  obtain ⟨j, hj⟩ := exists_gridCell_of_not_boundary hn (hmap p hxd) hb
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxA
  obtain ⟨hiA, hxi⟩ := Set.mem_iUnion.mp hi
  have he : (i, j) ∈ overlapEdges F n :=
    (mem_overlapEdges F (i, j)).mpr ⟨p, x, hxd, hxi, hj⟩
  have hjN := (mem_bipartiteRight (overlapEdges F n) A j).mpr ⟨i, hiA, he⟩
  exact Or.inl (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjN, hj⟩⟩)

theorem mapPreimageUnion_grid_cover {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hn : 0 < n) (hdom : ∀ p, (F p).domain ⊆ Icc (0 : ℝ) 1)
    (A : Finset (Fin n)) :
    mapPreimageUnion F (gridCells A) ⊆
      gridCells (bipartiteLeft (overlapEdges F n) A) ∪ gridBoundary n := by
  intro x hx
  obtain ⟨p, hxd, hxA⟩ := Set.mem_iUnion.mp hx
  by_cases hb : x ∈ gridBoundary n
  · exact Or.inr hb
  obtain ⟨i, hi⟩ := exists_gridCell_of_not_boundary hn (hdom p hxd) hb
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxA
  obtain ⟨hjA, hxj⟩ := Set.mem_iUnion.mp hj
  have he : (i, j) ∈ overlapEdges F n :=
    (mem_overlapEdges F (i, j)).mpr ⟨p, x, hxd, hi, hxj⟩
  have hiN := (mem_bipartiteLeft (overlapEdges F n) A i).mpr ⟨j, hjA, he⟩
  exact Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiN, hi⟩⟩)

theorem volume_real_le_cells_of_cover {n : ℕ} (A : Finset (Fin n)) {S : Set ℝ}
    (hS : S ⊆ gridCells A ∪ gridBoundary n) : volume.real S ≤ (A.card : ℝ) / n := by
  have hv : volume S ≤ volume (gridCells A) := calc
    _ ≤ volume (gridCells A ∪ gridBoundary n) := measure_mono hS
    _ ≤ volume (gridCells A) + volume (gridBoundary n) := measure_union_le _ _
    _ = volume (gridCells A) := by rw [gridBoundary_volume, add_zero]
  have hr := ENNReal.toReal_mono (gridCells_volume_ne_top A) hv
  exact hr.trans_eq (gridCells_volume_real A)

theorem gridCells_volume_le_half {n : ℕ} (hn : 0 < n) (A : Finset (Fin n))
    (hA : 2 * A.card ≤ n) : volume.real (gridCells A) ≤ 1 / 2 := by
  rw [gridCells_volume_real]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 2 * (A.card : ℝ) ≤ n := by exact_mod_cast hA
  apply (div_le_iff₀ hn').mpr
  linarith

theorem overlap_right_expansion {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hn : 0 < n) (hmap : ∀ p, MapsTo (F p).map (F p).domain (Icc (0 : ℝ) 1))
    (eps : ℝ)
    (hexp : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 → (1 + eps) * volume.real S ≤ volume.real (mapImageUnion F S))
    (A : Finset (Fin n)) (hA : 2 * A.card ≤ n) :
    (1 + eps) * A.card ≤ (bipartiteRight (overlapEdges F n) A).card := by
  have he := hexp (gridCells A) (gridCells_measurable A) (gridCells_subset_unit A)
    (gridCells_volume_le_half hn A hA)
  have hv := volume_real_le_cells_of_cover _ (mapImageUnion_grid_cover F hn hmap A)
  have hbound := he.trans hv
  rw [gridCells_volume_real, ← mul_div_assoc] at hbound
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0 : ℝ) < n)).mp hbound

theorem overlap_left_expansion {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hn : 0 < n) (hdom : ∀ p, (F p).domain ⊆ Icc (0 : ℝ) 1)
    (eps : ℝ)
    (hexp : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 → (1 + eps) * volume.real S ≤ volume.real (mapPreimageUnion F S))
    (A : Finset (Fin n)) (hA : 2 * A.card ≤ n) :
    (1 + eps) * A.card ≤ (bipartiteLeft (overlapEdges F n) A).card := by
  have he := hexp (gridCells A) (gridCells_measurable A) (gridCells_subset_unit A)
    (gridCells_volume_le_half hn A hA)
  have hv := volume_real_le_cells_of_cover _ (mapPreimageUnion_grid_cover F hn hdom A)
  have hbound := he.trans hv
  rw [gridCells_volume_real, ← mul_div_assoc] at hbound
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast hn : (0 : ℝ) < n)).mp hbound

theorem overlapGraph_vertex_expansion {c B h : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (hh : 0 < h) (hdom : ∀ p, (F p).domain ⊆ Icc (0 : ℝ) 1)
    (hmap : ∀ p, MapsTo (F p).map (F p).domain (Icc (0 : ℝ) 1))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hforward : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 → (1 + eps) * volume.real S ≤ volume.real (mapImageUnion F S))
    (hbackward : ∀ S : Set ℝ, MeasurableSet S → S ⊆ Icc (0 : ℝ) 1 →
      volume.real S ≤ 1 / 2 → (1 + eps) * volume.real S ≤ volume.real (mapPreimageUnion F S))
    (S : Finset (Fin (2 * (2 * h)))) (hS : 2 * S.card ≤ Fintype.card (Fin (2 * (2 * h)))) :
    eps / 2 * S.card ≤ (outsideNeighbors (overlapGraph F (2 * h)) S).card := by
  apply OrderedBipartite.vertex_expansion (overlapEdges F (2 * h)) eps heps
    (fun A hA => overlap_right_expansion F (by omega) hmap eps hforward A (by omega))
    (fun A hA => overlap_left_expansion F (by omega) hdom eps hbackward A (by omega)) S hS

end TransposeFollowup
