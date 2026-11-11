import NativeRelations.OneFreeHeadSmallExcursion

/-! State-spine closure bounds the number of actual retained intervals. The
local version allows paid entry snapshots at the starts of the selected chunk. -/

namespace AdaptiveTransfer

open Finset NativeRelations

def StateClosedExcept (K B : Finset ℕ) : Prop :=
  ∀ t ∈ K, 0 < t → t - 1 ∉ B → t - 1 ∈ K

theorem starts_subset_cut_successors {K B : Finset ℕ} (h : StateClosedExcept K B) :
    runStarts K ⊆ insert 0 (B.image (fun t => t + 1)) := by
  intro t ht
  obtain ⟨htK, hstart⟩ := mem_filter.mp ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · have hprev : t - 1 ∉ K := hstart.resolve_left ht0
    have hcut : t - 1 ∈ B := by
      by_contra hn
      exact hprev (h t htK (by omega) hn)
    exact mem_insert_of_mem (mem_image.mpr ⟨t - 1, hcut, by omega⟩)

theorem fragment_count_le {K B : Finset ℕ} (h : StateClosedExcept K B) :
    (runStarts K).card ≤ B.card + 1 := by
  calc (runStarts K).card ≤ (insert 0 (B.image (fun t => t + 1))).card :=
      card_le_card (starts_subset_cut_successors h)
    _ ≤ (B.image (fun t => t + 1)).card + 1 := card_insert_le _ _
    _ ≤ B.card + 1 := Nat.add_le_add_right card_image_le 1

/-- A retained fragment is closed under state predecessors inside its selected
chunk, except at recorded cut steps. No global trace is supplied. -/
def LocallyStateClosedExcept (C K B : Finset ℕ) : Prop :=
  K ⊆ C ∧ ∀ t ∈ K, 0 < t → t - 1 ∈ C → t - 1 ∉ B → t - 1 ∈ K

theorem local_starts_subset {C K B : Finset ℕ} (h : LocallyStateClosedExcept C K B) :
    runStarts K ⊆ runStarts C ∪ B.image (fun t => t + 1) := by
  intro t ht
  obtain ⟨htK, hstart⟩ := mem_filter.mp ht
  by_cases htC : t ∈ runStarts C
  · exact mem_union_left _ htC
  · have ht0 : t ≠ 0 := by
      intro heq
      exact htC (mem_filter.mpr ⟨h.1 htK, Or.inl heq⟩)
    have hpC : t - 1 ∈ C := by
      by_contra hn
      exact htC (mem_filter.mpr ⟨h.1 htK, Or.inr hn⟩)
    have hpK : t - 1 ∉ K := hstart.resolve_left ht0
    have hpB : t - 1 ∈ B := by
      by_contra hn
      exact hpK (h.2 t htK (by omega) hpC hn)
    exact mem_union_right _ (mem_image.mpr ⟨t - 1, hpB, by omega⟩)

theorem localized_fragment_count_le {C K B : Finset ℕ}
    (h : LocallyStateClosedExcept C K B) :
    (runStarts K).card ≤ (runStarts C).card + B.card := by
  calc (runStarts K).card ≤ (runStarts C ∪ B.image (fun t => t + 1)).card :=
      card_le_card (local_starts_subset h)
    _ ≤ (runStarts C).card + (B.image (fun t => t + 1)).card := card_union_le _ _
    _ ≤ (runStarts C).card + B.card := Nat.add_le_add_left card_image_le _

end AdaptiveTransfer
