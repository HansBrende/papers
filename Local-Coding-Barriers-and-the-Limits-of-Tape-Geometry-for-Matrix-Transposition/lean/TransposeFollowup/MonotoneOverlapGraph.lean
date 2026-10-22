import TransposeFollowup.MonotoneCellOverlap
import TransposeFollowup.MatchingPageDegree

/-! A finite family of bounded monotone maps defines a simple overlap graph.
Duplicate edges are retained once and assigned the least witnessing map tag.
The graph has a fixed number of nested matching pages, independent of size.
The real overlap predicate is not yet a rational decision algorithm. -/

namespace TransposeFollowup

open Classical
set_option autoImplicit false

noncomputable def overlapEdges {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (n : ℕ) :
    Finset (Fin n × Fin n) := Finset.univ.filter (fun e => ∃ p, (F p).Overlap e.1 e.2)

theorem mem_overlapEdges {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B) (e : Fin n × Fin n) :
    e ∈ overlapEdges F n ↔ ∃ p, (F p).Overlap e.1 e.2 := by simp [overlapEdges]

noncomputable def overlapTags {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (e : Fin n × Fin n) : Finset (Fin c) := Finset.univ.filter (fun p => (F p).Overlap e.1 e.2)

theorem overlapTags_nonempty {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (e : overlapEdges F n) : (overlapTags F e.val).Nonempty := by
  obtain ⟨p, hp⟩ := (mem_overlapEdges F e.val).mp e.property
  exact ⟨p, by simpa [overlapTags] using hp⟩

noncomputable def overlapTag {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (e : overlapEdges F n) : Fin c := (overlapTags F e.val).min' (overlapTags_nonempty F e)

theorem overlapTag_spec {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (e : overlapEdges F n) : (F (overlapTag F e)).Overlap e.val.1 e.val.2 := by
  have hm := Finset.min'_mem (overlapTags F e.val) (overlapTags_nonempty F e)
  exact (Finset.mem_filter.mp hm).2

theorem overlapTag_le {c B n : ℕ} (F : Fin c → BoundedMonotoneMap B)
    (e : overlapEdges F n) (p : Fin c) (hp : (F p).Overlap e.val.1 e.val.2) : overlapTag F e ≤ p := by
  exact Finset.min'_le _ _ (by simpa [overlapTags] using hp)

noncomputable def overlapColoring {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (n : ℕ) :
    ResidueMatchingInput (overlapEdges F n) c (B + 1) where
  modulus_pos := Nat.zero_lt_succ B
  tag := overlapTag F
  ordered e f hp horder := by
    have hf := overlapTag_spec F f
    rw [← hp] at hf
    exact (F (overlapTag F e)).overlap_order (overlapTag_spec F e) hf horder
  row_span e f hp he := by
    have hf := overlapTag_spec F f
    rw [← hp, ← he] at hf
    exact (F (overlapTag F e)).overlap_row_span (overlapTag_spec F e) hf
  column_span e f hp he := by
    have hf := overlapTag_spec F f
    rw [← hp, ← he] at hf
    exact (F (overlapTag F e)).overlap_column_span (overlapTag_spec F e) hf

noncomputable def overlapGraph {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (n : ℕ) :
    SimpleGraph (Fin (2 * n)) := OrderedBipartite.graph (overlapEdges F n)

noncomputable def overlapPages {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (n : ℕ) :
    NestedMatchingPages (overlapGraph F n) (c * ((B + 1) * (B + 1))) :=
  (overlapColoring F n).nestedPages

theorem overlapGraph_degree_le {c B : ℕ} (F : Fin c → BoundedMonotoneMap B) (n : ℕ)
    (u : Fin (2 * n)) : (overlapGraph F n).degree u ≤ c * ((B + 1) * (B + 1)) :=
  (overlapPages F n).degree_le_pages u

end TransposeFollowup
