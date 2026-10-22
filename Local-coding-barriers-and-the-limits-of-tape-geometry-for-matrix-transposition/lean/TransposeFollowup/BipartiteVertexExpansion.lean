import TransposeFollowup.BipartiteExpansionCount

/-! Transfer two-sided neighbor expansion to the actual ordered simple graph.
The two copies of the vertex class are disjoint, so their outside boundaries
can be counted together without losing or identifying vertices. -/

namespace TransposeFollowup
namespace OrderedBipartite

open Classical
set_option autoImplicit false

theorem left_or_right {n : ℕ} (u : Fin (2 * n)) :
    (∃ i : Fin n, left i = u) ∨ ∃ j : Fin n, right j = u := by
  by_cases hu : u.val < n
  · exact Or.inl ⟨⟨u.val, hu⟩, Fin.ext rfl⟩
  · have huv := u.isLt
    refine Or.inr ⟨⟨2 * n - 1 - u.val, by omega⟩, ?_⟩
    apply Fin.ext
    dsimp [right]
    omega

noncomputable def leftPart {n : ℕ} (S : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => left i ∈ S)

noncomputable def rightPart {n : ℕ} (S : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter (fun j => right j ∈ S)

theorem mem_leftPart {n : ℕ} (S : Finset (Fin (2 * n))) (i : Fin n) :
    i ∈ leftPart S ↔ left i ∈ S := by simp [leftPart]

theorem mem_rightPart {n : ℕ} (S : Finset (Fin (2 * n))) (j : Fin n) :
    j ∈ rightPart S ↔ right j ∈ S := by simp [rightPart]

theorem images_disjoint {n : ℕ} (A B : Finset (Fin n)) :
    Disjoint (A.image left) (B.image right) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
  exact left_ne_right i j hj.symm

theorem parts_cover {n : ℕ} (S : Finset (Fin (2 * n))) :
    (leftPart S).image left ∪ (rightPart S).image right = S := by
  ext u
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (mem_leftPart S i).mp hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
      exact (mem_rightPart S j).mp hj
  · intro hu
    rcases left_or_right u with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨i, (mem_leftPart S i).mpr hu, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, (mem_rightPart S j).mpr hu, rfl⟩)

theorem card_parts {n : ℕ} (S : Finset (Fin (2 * n))) :
    (leftPart S).card + (rightPart S).card = S.card := by
  calc
    _ = ((leftPart S).image left ∪ (rightPart S).image right).card := by
      rw [Finset.card_union_of_disjoint (images_disjoint _ _),
        Finset.card_image_of_injective _ left_injective,
        Finset.card_image_of_injective _ right_injective]
    _ = _ := congrArg Finset.card (parts_cover S)

theorem adj_left_right {n : ℕ} (edges : Finset (Fin n × Fin n)) (i j : Fin n) :
    (graph edges).Adj (left i) (right j) ↔ (i, j) ∈ edges := by
  change (SimpleGraph.fromEdgeSet _).Adj _ _ ↔ _
  rw [SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e, he⟩, _⟩
    have heq : e.val = (i, j) := address_injective he
    exact heq ▸ e.property
  · intro he
    exact ⟨⟨⟨(i, j), he⟩, rfl⟩, left_ne_right i j⟩

theorem boundary_count_le {n : ℕ} (edges : Finset (Fin n × Fin n))
    (S : Finset (Fin (2 * n))) :
    (bipartiteRight edges (leftPart S) \ rightPart S).card +
      (bipartiteLeft edges (rightPart S) \ leftPart S).card ≤
      (outsideNeighbors (graph edges) S).card := by
  let X := bipartiteRight edges (leftPart S) \ rightPart S
  let Y := bipartiteLeft edges (rightPart S) \ leftPart S
  have hx : X.image right ⊆ outsideNeighbors (graph edges) S := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hj, hjS⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨i, hi, he⟩ := (mem_bipartiteRight edges (leftPart S) j).mp hj
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨left i, (mem_leftPart S i).mp hi, ?_⟩, ?_⟩
    · exact ((graph edges).mem_neighborFinset _ _).mpr ((adj_left_right edges i j).mpr he)
    · exact fun h => hjS ((mem_rightPart S j).mpr h)
  have hy : Y.image left ⊆ outsideNeighbors (graph edges) S := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hi, hiS⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨j, hj, he⟩ := (mem_bipartiteLeft edges (rightPart S) i).mp hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨right j, (mem_rightPart S j).mp hj, ?_⟩, ?_⟩
    · exact ((graph edges).mem_neighborFinset _ _).mpr
        ((adj_left_right edges i j).mpr he).symm
    · exact fun h => hiS ((mem_leftPart S i).mpr h)
  have hc := Finset.card_le_card (Finset.union_subset hy hx)
  rw [Finset.card_union_of_disjoint (images_disjoint Y X),
    Finset.card_image_of_injective _ left_injective,
    Finset.card_image_of_injective _ right_injective] at hc
  exact (Nat.add_comm _ _).trans_le hc

theorem vertex_expansion {h : ℕ} (edges : Finset (Fin (2 * h) × Fin (2 * h)))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hR : ∀ A : Finset (Fin (2 * h)), A.card ≤ h →
      (1 + eps) * A.card ≤ (bipartiteRight edges A).card)
    (hL : ∀ B : Finset (Fin (2 * h)), B.card ≤ h →
      (1 + eps) * B.card ≤ (bipartiteLeft edges B).card)
    (S : Finset (Fin (2 * (2 * h)))) (hS : 2 * S.card ≤ Fintype.card (Fin (2 * (2 * h)))) :
    eps / 2 * S.card ≤ (outsideNeighbors (graph edges) S).card := by
  have hparts := card_parts S
  have hsmall : (leftPart S).card + (rightPart S).card ≤ 2 * h := by
    simp only [Fintype.card_fin] at hS
    omega
  have he := two_sided_expansion_count edges eps heps hR hL (leftPart S) (rightPart S) hsmall
  rw [hparts] at he
  exact he.trans (by exact_mod_cast boundary_count_le edges S)

end OrderedBipartite
end TransposeFollowup
