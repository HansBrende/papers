import AdaptiveTransfer.HistoricalCache

/-! Distinct actual changed addresses require both successful duration and
physical head span. These consequences do not assume or construct a cache
compiler or the canonical episode policy. -/

namespace AdaptiveTransfer.ExecutionPrefix
open Transpose Finset

variable {M : TM} {w : List Bool} {T : ℕ} (E : ExecutionPrefix M w T)

def episodeVisited (h : Fin M.k) (u v : ℕ) : Finset ℤ :=
  (Ico u v).image fun t => (E.config t).workPos h

noncomputable def episodeSpan (h : Fin M.k) (u v : ℕ) : ℕ :=
  if hn : (E.episodeVisited h u v).Nonempty then
    ((E.episodeVisited h u v).max' hn - (E.episodeVisited h u v).min' hn).toNat
  else 0

theorem changedCells_subset_episodeVisited (h : Fin M.k) (u v : ℕ) :
    E.changedCells h u v ⊆ E.episodeVisited h u v := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
  exact mem_image.mpr ⟨t, (mem_filter.mp ht).1, rfl⟩

theorem changedCells_card_le_span_add_one (h : Fin M.k) (u v : ℕ) :
    (E.changedCells h u v).card ≤ E.episodeSpan h u v + 1 := by
  let V := E.episodeVisited h u v
  by_cases hn : V.Nonempty
  · have hbounds : V ⊆ Icc (V.min' hn) (V.max' hn) := by
      intro z hz
      exact mem_Icc.mpr ⟨min'_le _ z hz, le_max' _ z hz⟩
    have hminmax : V.min' hn ≤ V.max' hn := min'_le _ _ (max'_mem _ hn)
    have hc := (card_le_card (E.changedCells_subset_episodeVisited h u v)).trans (card_le_card hbounds)
    rw [Int.card_Icc] at hc
    have he : E.episodeSpan h u v = (V.max' hn - V.min' hn).toNat := by
      simp only [episodeSpan, V, dite_eq_left hn]
    rw [he]
    omega
  · have he : V = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hc := card_le_card (E.changedCells_subset_episodeVisited h u v)
    change (E.changedCells h u v).card ≤ V.card at hc
    rw [he, card_empty] at hc
    omega

/-- If an episode violates the floor-density bound, its distinct changes,
successful step count and actual visited-head span meet the stated thresholds.
The endpoint assumption ensures all counted episode steps are successful. -/
theorem many_changes_duration_span (h : Fin M.k) {u v P : ℕ} {δ : ℝ}
    (hv : v ≤ T) (hδ : 0 ≤ δ)
    (hmany : ⌊δ * P⌋₊ < (E.changedCells h u v).card) :
    ⌊δ * P⌋₊ + 1 ≤ (E.changedCells h u v).card ∧
      δ * P < ((v - u : ℕ) : ℝ) ∧ ⌊δ * P⌋₊ ≤ E.episodeSpan h u v ∧
      ∀ t ∈ Ico u v, ∃ c', step M w (E.config t) = some c' := by
  have hduration := E.changedCells_card_le_duration h u v
  have hspan := E.changedCells_card_le_span_add_one h u v
  refine ⟨by omega, ?_, by omega, ?_⟩
  · have hfloor : ⌊δ * P⌋₊ < v - u := hmany.trans_le hduration
    exact (Nat.floor_lt (by positivity)).mp hfloor
  · intro t ht
    exact ⟨E.config (t + 1), E.successful t ((mem_Ico.mp ht).2.trans_le hv)⟩

/-- The reached-configuration episode may include halt. Its changed addresses
stop at the successful horizon, while its physical span includes the whole
declared episode. The halting configuration contributes no fictitious write. -/
theorem many_episode_changes_duration_span (h : Fin M.k) {u v P : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hmany : ⌊δ * P⌋₊ < (E.changedCells h u (min v T)).card) :
    ⌊δ * P⌋₊ + 1 ≤ (E.changedCells h u (min v T)).card ∧
      δ * P < ((min v T - u : ℕ) : ℝ) ∧ ⌊δ * P⌋₊ ≤ E.episodeSpan h u v ∧
      ∀ t ∈ Ico u (min v T), ∃ c', step M w (E.config t) = some c' := by
  obtain ⟨hc, hd, _, hs⟩ := E.many_changes_duration_span h (min_le_right v T) hδ hmany
  refine ⟨hc, hd, ?_, hs⟩
  have hsub := card_le_card (E.changedCells_mono h (u := u) (v := v) le_rfl (min_le_left v T))
  have hb := E.changedCells_card_le_span_add_one h u v
  omega

end AdaptiveTransfer.ExecutionPrefix
