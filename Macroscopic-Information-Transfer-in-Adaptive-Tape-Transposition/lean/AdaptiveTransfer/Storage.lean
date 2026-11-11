import AdaptiveTransfer.CurrentVersion
import Mathlib.Data.Finset.Card

/-! Native support changes and actual persistent cells. These results do not
claim independence, future use, or a dynamic-carrier compiler. -/

namespace AdaptiveTransfer

open Transpose Finset

def nonblankWithin {M : TM} (c : Config M) (h : Fin M.k) (window : Finset ℤ) : Finset ℤ :=
  window.filter fun z => c.work h z ≠ 0

theorem native_support_subset {M : TM} {w : List Bool} {c c' : Config M}
    (hs : step M w c = some c') (h : Fin M.k) (window : Finset ℤ) :
    nonblankWithin c' h window ⊆ insert (c.workPos h) (nonblankWithin c h window) := by
  intro z hz
  obtain ⟨hzw, hnon⟩ := mem_filter.mp hz
  by_cases heq : z = c.workPos h
  · exact mem_insert.mpr (Or.inl heq)
  · exact mem_insert_of_mem (mem_filter.mpr ⟨hzw, by
      simpa [step_preserves_unscanned hs h z heq] using hnon⟩)

theorem native_support_growth_le_one {M : TM} {w : List Bool} {c c' : Config M}
    (hs : step M w c = some c') (h : Fin M.k) (window : Finset ℤ) :
    (nonblankWithin c' h window).card ≤ (nonblankWithin c h window).card + 1 :=
  (card_le_card (native_support_subset hs h window)).trans (card_insert_le _ _)

theorem native_support_shrink_le_one {M : TM} {w : List Bool} {c c' : Config M}
    (hs : step M w c = some c') (h : Fin M.k) (window : Finset ℤ) :
    (nonblankWithin c h window).card ≤ (nonblankWithin c' h window).card + 1 := by
  have hsub : nonblankWithin c h window ⊆
      insert (c.workPos h) (nonblankWithin c' h window) := by
    intro z hz
    obtain ⟨hzw, hnon⟩ := mem_filter.mp hz
    by_cases heq : z = c.workPos h
    · exact mem_insert.mpr (Or.inl heq)
    · exact mem_insert_of_mem (mem_filter.mpr ⟨hzw, by
        simpa [step_preserves_unscanned hs h z heq] using hnon⟩)
  exact (card_le_card hsub).trans (card_insert_le _ _)

namespace ExecutionPrefix

variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

/-- A cell not scanned during an interval keeps its actual symbol. -/
theorem untouched_cell_constant (h : Fin M.k) {u v : ℕ} (huv : u ≤ v) (hvT : v ≤ T)
    (z : ℤ) (hgap : ∀ t, u ≤ t → t < v → z ≠ (E.config t).workPos h) :
    (E.config v).work h z = (E.config u).work h z := by
  rw [E.work_eq_memoryAfter h hvT, E.work_eq_memoryAfter h (huv.trans hvT)]
  exact memoryAfter_no_write _ _ _ _ huv (fun t hut htv _ => hgap t hut htv)

/-- At most the duration many terminal nonblank cells can have been written in
the interval. The remaining cells are unchanged throughout the interval. -/
theorem persistent_cells (h : Fin M.k) (window : Finset ℤ)
    {u v : ℕ} (_huv : u ≤ v) (hvT : v ≤ T) :
    ∃ S : Finset ℤ,
      S ⊆ nonblankWithin (E.config v) h window ∧
      (nonblankWithin (E.config v) h window).card ≤ S.card + (v - u) ∧
      ∀ z ∈ S, ∀ t, u ≤ t → t ≤ v →
        (E.config t).work h z = (E.config v).work h z := by
  let touched := (Ico u v).image fun t => (E.config t).workPos h
  let S := nonblankWithin (E.config v) h window \ touched
  refine ⟨S, sdiff_subset, ?_, ?_⟩
  · have hcard := card_sdiff_add_card_inter (nonblankWithin (E.config v) h window) touched
    have hbound : (nonblankWithin (E.config v) h window ∩ touched).card ≤ v - u := by
      calc _ ≤ touched.card := card_le_card inter_subset_right
        _ ≤ (Ico u v).card := card_image_le
        _ = v - u := Nat.card_Ico u v
    dsimp [S]
    omega
  · intro z hz t hut htv
    have hznot := (mem_sdiff.mp hz).2
    symm
    apply E.untouched_cell_constant h htv hvT z
    intro r htr hrv hzr
    apply hznot
    exact mem_image.mpr ⟨r, mem_Ico.mpr ⟨hut.trans htr, hrv⟩, hzr.symm⟩

end ExecutionPrefix
end AdaptiveTransfer
