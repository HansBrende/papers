import TransposeFollowup.PageOpcode

/-! Event descriptions in the original bipartite edge coordinates, derived
through the existing edge equivalence into the ordered simple graph. -/

namespace TransposeFollowup
namespace ResidueMatchingInput

open Classical
set_option autoImplicit false

variable {n c M : ℕ} {edges : Finset (Fin n × Fin n)} (D : ResidueMatchingInput edges c M)

theorem sourceEvent_left (i : Fin n) (p : Fin (c * (M * M))) :
    D.nestedPages.SourceEvent (OrderedBipartite.left i) p ↔
      ∃ e : edges, e.val.1 = i ∧ D.color e = p := by
  change (∃ z, OrderedBipartite.left ((OrderedBipartite.edgeEquiv edges).symm z).val.1 =
    OrderedBipartite.left i ∧ D.color ((OrderedBipartite.edgeEquiv edges).symm z) = p) ↔ _
  constructor
  · rintro ⟨z, hs, hp⟩
    exact ⟨(OrderedBipartite.edgeEquiv edges).symm z, OrderedBipartite.left_injective hs, hp⟩
  · rintro ⟨e, hs, hp⟩
    refine ⟨OrderedBipartite.edgeEquiv edges e, ?_⟩
    rw [Equiv.symm_apply_apply, hs]
    exact ⟨rfl, hp⟩

theorem targetEvent_right (j : Fin n) (p : Fin (c * (M * M))) :
    D.nestedPages.TargetEvent (OrderedBipartite.right j) p ↔
      ∃ e : edges, e.val.2 = j ∧ D.color e = p := by
  change (∃ z, OrderedBipartite.right ((OrderedBipartite.edgeEquiv edges).symm z).val.2 =
    OrderedBipartite.right j ∧ D.color ((OrderedBipartite.edgeEquiv edges).symm z) = p) ↔ _
  constructor
  · rintro ⟨z, hs, hp⟩
    exact ⟨(OrderedBipartite.edgeEquiv edges).symm z, OrderedBipartite.right_injective hs, hp⟩
  · rintro ⟨e, hs, hp⟩
    refine ⟨OrderedBipartite.edgeEquiv edges e, ?_⟩
    rw [Equiv.symm_apply_apply, hs]
    exact ⟨rfl, hp⟩

theorem not_sourceEvent_right (j : Fin n) (p : Fin (c * (M * M))) :
    ¬D.nestedPages.SourceEvent (OrderedBipartite.right j) p := by
  rintro ⟨z, hs, _⟩
  exact OrderedBipartite.left_ne_right _ j hs

theorem not_targetEvent_left (i : Fin n) (p : Fin (c * (M * M))) :
    ¬D.nestedPages.TargetEvent (OrderedBipartite.left i) p := by
  rintro ⟨z, hs, _⟩
  exact OrderedBipartite.left_ne_right i _ hs.symm

end ResidueMatchingInput
end TransposeFollowup
