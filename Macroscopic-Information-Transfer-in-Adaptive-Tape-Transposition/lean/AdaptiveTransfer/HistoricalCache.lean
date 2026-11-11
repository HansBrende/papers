import AdaptiveTransfer.Storage
import Mathlib.Tactic

/-! Actual distinct changed addresses control error support about a frozen
word. Restores count, repeated changes share one address, identity writes do
not count. This is not the historical-carrier compiler. -/

namespace AdaptiveTransfer

open Transpose Finset

namespace ExecutionPrefix

variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

def changedCells (h : Fin M.k) (u v : ℕ) : Finset ℤ :=
  ((Ico u v).filter fun t =>
    (E.config (t + 1)).work h ((E.config t).workPos h) ≠
      (E.config t).work h ((E.config t).workPos h)).image
    (fun t => (E.config t).workPos h)

theorem changedCells_mono (h : Fin M.k) {u v u' v' : ℕ}
    (hu : u ≤ u') (hv : v' ≤ v) : E.changedCells h u' v' ⊆ E.changedCells h u v := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
  obtain ⟨ht, hc⟩ := mem_filter.mp ht
  obtain ⟨hut, htv⟩ := mem_Ico.mp ht
  exact mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_Ico.mpr ⟨hu.trans hut, htv.trans_le hv⟩, hc⟩, rfl⟩

theorem unchanged_outside_changedCells (h : Fin M.k) {u v : ℕ}
    (huv : u ≤ v) (hvT : v ≤ T) (z : ℤ) (hz : z ∉ E.changedCells h u v) :
    (E.config v).work h z = (E.config u).work h z := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hprev : z ∉ E.changedCells h u v := fun hm =>
      hz (E.changedCells_mono h le_rfl (by omega) hm)
    have hs : (E.config (v + 1)).work h z = (E.config v).work h z := by
      by_cases heq : z = (E.config v).workPos h
      · by_contra hc
        apply hz
        exact mem_image.mpr ⟨v, mem_filter.mpr
          ⟨mem_Ico.mpr ⟨huv, by omega⟩, by simpa only [← heq] using hc⟩, heq.symm⟩
      · exact step_preserves_unscanned (E.successful v (by omega)) h z heq
    exact hs.trans (ih (by omega) hprev)

def residualWithin (h : Fin M.k) (t : ℕ) (base : ℤ → Fin (M.g + 1))
    (window : Finset ℤ) : Finset ℤ :=
  window.filter fun z => (E.config t).work h z ≠ base z

theorem residual_subset_changed (h : Fin M.k) {u v : ℕ} (huv : u ≤ v)
    (hvT : v ≤ T) (base : ℤ → Fin (M.g + 1)) (window : Finset ℤ) :
    E.residualWithin h v base window ⊆
      E.residualWithin h u base window ∪ E.changedCells h u v := by
  intro z hz
  obtain ⟨hzw, hne⟩ := mem_filter.mp hz
  by_cases hc : z ∈ E.changedCells h u v
  · exact mem_union_right _ hc
  · apply mem_union_left
    apply mem_filter.mpr
    exact ⟨hzw, by simpa only [E.unchanged_outside_changedCells h huv hvT z hc] using hne⟩

theorem residual_card_le (h : Fin M.k) {u v : ℕ} (huv : u ≤ v)
    (hvT : v ≤ T) (base : ℤ → Fin (M.g + 1)) (window : Finset ℤ) :
    (E.residualWithin h v base window).card ≤
      (E.residualWithin h u base window).card + (E.changedCells h u v).card :=
  (card_le_card (E.residual_subset_changed h huv hvT base window)).trans (card_union_le _ _)

theorem changedCells_split_first (h : Fin M.k) (u v : ℕ) :
    E.changedCells h u v ⊆
      insert ((E.config u).workPos h) (E.changedCells h (u + 1) v) := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
  obtain ⟨ht, hc⟩ := mem_filter.mp ht
  obtain ⟨hut, htv⟩ := mem_Ico.mp ht
  by_cases htu : t = u
  · subst t
    exact mem_insert_self _ _
  · apply mem_insert_of_mem
    exact mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, htv⟩, hc⟩, rfl⟩

/-- The single entering write costs one address; the later episode pays
only its distinct actually changed addresses. -/
theorem residual_card_le_entering_add_episode (h : Fin M.k) {u v s m : ℕ}
    (huv : u ≤ v) (hvT : v ≤ T) (base : ℤ → Fin (M.g + 1)) (window : Finset ℤ)
    (hstart : (E.residualWithin h u base window).card ≤ s)
    (hepisode : (E.changedCells h (u + 1) v).card ≤ m) :
    (E.residualWithin h v base window).card ≤ s + m + 1 := by
  have hc := (card_le_card (E.changedCells_split_first h u v)).trans (card_insert_le _ _)
  have hr := E.residual_card_le h huv hvT base window
  omega

theorem changedCells_card_le_duration (h : Fin M.k) (u v : ℕ) :
    (E.changedCells h u v).card ≤ v - u := by
  calc
    _ ≤ ((Ico u v).filter fun t =>
      (E.config (t + 1)).work h ((E.config t).workPos h) ≠
        (E.config t).work h ((E.config t).workPos h)).card := card_image_le
    _ ≤ (Ico u v).card := card_filter_le _ _
    _ = v - u := Nat.card_Ico u v

end ExecutionPrefix
end AdaptiveTransfer
