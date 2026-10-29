import SourceCovers.SerialCoreGraph

set_option autoImplicit false

/-! Identify original nonleaves before any periodic deletion. The bridge
and the isolated early family are retained as original leaves. -/

namespace SourceCovers.SerialGeometry.Parameters

open Finset BoundedNesting
noncomputable section

variable (P : Parameters)

theorem bankCore_neighbors (c : Fin 2) (j : Fin P.bankCount) (F : CoreFamily P.coreFamilies) :
    (coreModel P.coreFamilies).graph.Adj (P.bankCore c j) F ↔
      (∃ i : Fin P.bankCount, F = P.bankCore c i ∧
        (j.val + 1 = i.val ∨ i.val + 1 = j.val)) ∨
      (c.val = 0 ∧ j.val + 1 = P.bankCount ∧ F = P.bridgeCore) := by
  constructor
  · intro h
    rcases P.core_cases F with ⟨c', i, rfl⟩ | rfl | rfl
    · obtain ⟨rfl, hi⟩ := (P.bankCore_adj_iff c c' j i).mp h
      exact Or.inl ⟨i, rfl, hi⟩
    · exact False.elim (P.earlyCore_not_adj _ h.symm)
    · have hb := (P.bankCore_bridge_adj_iff c j).mp h
      exact Or.inr ⟨hb.1, hb.2, rfl⟩
  · rintro (⟨i, rfl, hi⟩ | ⟨hc, hj, rfl⟩)
    · exact (P.bankCore_adj_iff c c j i).mpr ⟨rfl, hi⟩
    · exact (P.bankCore_bridge_adj_iff c j).mpr ⟨hc, hj⟩

theorem bridgeCore_neighbors (F : CoreFamily P.coreFamilies) :
    (coreModel P.coreFamilies).graph.Adj P.bridgeCore F ↔
      ∃ c : Fin 2, ∃ j : Fin P.bankCount,
        F = P.bankCore c j ∧ c.val = 0 ∧ j.val + 1 = P.bankCount := by
  constructor
  · intro h
    rcases P.core_cases F with ⟨c, j, rfl⟩ | rfl | rfl
    · have hb := (P.bankCore_bridge_adj_iff c j).mp h.symm
      exact ⟨c, j, rfl, hb⟩
    · exact False.elim (P.earlyCore_not_adj _ h.symm)
    · exact False.elim (h.ne rfl)
  · rintro ⟨c, j, rfl, hb⟩
    exact ((P.bankCore_bridge_adj_iff c j).mpr hb).symm

theorem earlyCore_not_nonleaf : ¬ (coreModel P.coreFamilies).Nonleaf P.earlyCore := by
  rintro ⟨F, _, hF, _⟩
  exact P.earlyCore_not_adj F hF

theorem bridgeCore_not_nonleaf : ¬ (coreModel P.coreFamilies).Nonleaf P.bridgeCore := by
  rintro ⟨F, G, hF, hG, hne⟩
  obtain ⟨c, j, rfl, hc, hj⟩ := (P.bridgeCore_neighbors F).mp hF
  obtain ⟨c', j', rfl, hc', hj'⟩ := (P.bridgeCore_neighbors G).mp hG
  have hec : c = c' := Fin.ext (hc.trans hc'.symm)
  have hej : j = j' := Fin.ext (by omega)
  exact hne (by rw [hec, hej])

/-- The last early bank is a nonleaf because of its bridge neighbor;
the last late bank is an original leaf. -/
theorem bankCore_nonleaf_iff (c : Fin 2) (j : Fin P.bankCount) :
    (coreModel P.coreFamilies).Nonleaf (P.bankCore c j) ↔
      0 < j.val ∧ (j.val + 1 < P.bankCount ∨ c.val = 0) := by
  have hn := P.bankCount_ge
  constructor
  · rintro ⟨F, G, hF, hG, hne⟩
    rw [P.bankCore_neighbors] at hF hG
    rcases hF with ⟨i, rfl, hi⟩ | ⟨hc, hj, rfl⟩ <;>
      rcases hG with ⟨i', rfl, hi'⟩ | ⟨hc', hj', rfl⟩
    · have he : i.val ≠ i'.val := by
        intro he
        exact hne (congrArg (P.bankCore c) (Fin.ext he))
      have hbi := i.isLt
      have hbi' := i'.isLt
      exact ⟨by omega, Or.inl (by omega)⟩
    · exact ⟨by omega, Or.inr hc'⟩
    · exact ⟨by omega, Or.inr hc⟩
    · exact False.elim (hne rfl)
  · rintro ⟨hj, hlast⟩
    let i : Fin P.bankCount := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hi : (coreModel P.coreFamilies).graph.Adj (P.bankCore c j) (P.bankCore c i) :=
      (P.bankCore_adj_iff c c j i).mpr ⟨rfl, Or.inr (by dsimp only [i]; omega)⟩
    by_cases hnext : j.val + 1 < P.bankCount
    · let i' : Fin P.bankCount := ⟨j.val + 1, hnext⟩
      refine ⟨P.bankCore c i, P.bankCore c i', hi,
        (P.bankCore_adj_iff c c j i').mpr ⟨rfl, Or.inl rfl⟩, ?_⟩
      intro he
      have hh := @bankCore_injective P (c, i) (c, i') he
      have hv := congrArg (fun q : Fin 2 × Fin P.bankCount => q.2.val) hh
      dsimp only [i, i'] at hv
      omega
    · have hc := hlast.resolve_left hnext
      have hlast' : j.val + 1 = P.bankCount := by have := j.isLt; omega
      exact ⟨P.bankCore c i, P.bridgeCore, hi,
        (P.bankCore_bridge_adj_iff c j).mpr ⟨hc, hlast'⟩, P.bankCore_ne_bridge c i⟩

theorem core_nonleaf_cases {F : CoreFamily P.coreFamilies}
    (hF : (coreModel P.coreFamilies).Nonleaf F) :
    ∃ c : Fin 2, ∃ j : Fin P.bankCount,
      F = P.bankCore c j ∧ 0 < j.val ∧ (j.val + 1 < P.bankCount ∨ c.val = 0) := by
  rcases P.core_cases F with ⟨c, j, rfl⟩ | rfl | rfl
  · exact ⟨c, j, rfl, (P.bankCore_nonleaf_iff c j).mp hF⟩
  · exact False.elim (P.earlyCore_not_nonleaf hF)
  · exact False.elim (P.bridgeCore_not_nonleaf hF)

end
end SourceCovers.SerialGeometry.Parameters
