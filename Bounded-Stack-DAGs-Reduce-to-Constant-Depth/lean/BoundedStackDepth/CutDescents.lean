import BoundedStackDepth.Exposure
import BoundedStackDepth.LadderBands
import BoundedStackDepth.EventWeight

/-!
# The cut state edges

A descent of the label at `t` (a cut state edge `t → t − 1`) changes the shown set or wraps a digit
(`shown_ne_or_wrap`).

* **The shown set moves only at events** (`shown_eq_of_not_eventTime`): the shown set changes at `t` only if some head has a rise or a
  last-stint end at `t` of group `≥ 1`. This is view invariance at `d = 0`, where every candidate is
  displayed by (Z).
* `card_descents_le`: the descents number at most the event times plus the wrap times.
* `card_eventTimes_le`: the event times number at most the rises and last-stint ends of all heads.
* `sum_card_wrapTimes_le`: over the digit offsets, the wrap times total at most
  `P K^{P−1} Σ_w (#turning points + #segment starts)`: at most `P` groups have a digit, and a counter
  increases at `t` only by the events at `t`.
-/

namespace BoundedStackDepth

open BoundedNesting Finset FrameSystem

variable {k : ℕ} {xs : Fin k → ℕ → ℤ} (T : ℕ) (hx : ∀ i, IsWalk (xs i)) {h₀ : ℕ}

theorem headFrames_T (v : Fin (k * 2)) : (headFrames T hx v).T = T := upperFrames_T _

theorem isWalk_headFrames (v : Fin (k * 2)) : IsWalk (headFrames T hx v).x := by
  rw [headFrames, upperFrames_x]; exact isWalk_headWalk hx v

/-- Lemma W2 for the heads' frames. -/
private theorem popsAtZero_head (v : Fin (k * 2)) : (headFrames T hx v).PopsAtZero := by
  intro F hF hne h12
  have hF' : F ∈ suspendFrames (headWalk xs v) T := by
    rcases mem_insert.mp hF with h | h
    · exact absurd h hne
    · exact h
  exact beta_last_eq_zero (isWalk_headWalk hx v) hF' h12

open Classical in
/-- The times at which some head has a rise or a last-stint end of group `≥ 1` (at offset `r`). -/
noncomputable def eventTimes (r : ℕ) : Finset ℕ :=
  (Ico 1 T).filter fun t => ∃ w, ∃ g ∈ range T, 1 ≤ g ∧
    ((headFrames T hx w).RiseAt h₀ r t g ∨ (headFrames T hx w).LastStintAt h₀ r t g)

variable {Q : ℕ} [NeZero Q]

/-- **The shown set moves only at events.** Outside the event times the shown set does not change. -/
theorem shown_eq_of_not_eventTime {r : ℕ} (hr : r < h₀) (ξ : EntryIdx (headFrames T hx) → Fin Q)
    {t : ℕ} (ht : t ∈ Ico 1 T) (hnot : t ∉ eventTimes T hx (h₀ := h₀) r) :
    shown T hx h₀ r ξ (t - 1) = shown T hx h₀ r ξ t := by
  classical
  obtain ⟨ht1, htT⟩ := mem_Ico.mp ht
  have htT' : ∀ w, t < (headFrames T hx w).T := fun w => by rw [headFrames_T]; exact htT
  have hviews : ∀ w, (headFrames T hx w).headAbove h₀ r 0 (t - 1) =
      (headFrames T hx w).headAbove h₀ r 0 t ∧
      (headFrames T hx w).headVisible h₀ r 0 (t - 1) = (headFrames T hx w).headVisible h₀ r 0 t := by
    intro w
    refine view_step hr (popsAtZero_head T hx w) (htT' w) 0 fun g hg => ⟨fun h => ?_, fun h => ?_⟩
    · have hg' := lt_of_rise (isWalk_headFrames T hx w) hr (htT' w) h
      rw [headFrames_T] at hg'
      refine hnot ?_
      simp only [eventTimes, mem_filter]
      exact ⟨ht, w, g, mem_range.mpr hg', by omega, Or.inl h⟩
    · have hg' := lt_of_lastStint (isWalk_headFrames T hx w) hr (htT' w) h
      rw [headFrames_T] at hg'
      refine hnot ?_
      simp only [eventTimes, mem_filter]
      exact ⟨ht, w, g, mem_range.mpr hg', by omega, Or.inr h⟩
  obtain ⟨hX, hV⟩ := views_eq (headFrames T hx) h₀ r (fun e => ξ e ≠ 0) hviews
  have hz : ∀ s, ∀ e, dispBot (headFrames T hx) h₀ r s e ≤ 0 → 0 < dispTop (headFrames T hx) h₀ r e →
      Disp (dispBot (headFrames T hx) h₀ r s) (dispTop (headFrames T hx) h₀ r) (fun e => ξ e ≠ 0)
        (seeds (headFrames T hx) h₀ r s) e := fun s e h1 _ => Disp.zero (by omega)
  have habove := shown_above_eq (hz (t - 1)) (hz t) hX hV
  ext y
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · exact ⟨fun _ => zero_mem_shown hx r ξ t, fun _ => zero_mem_shown hx r ξ (t - 1)⟩
  · have := congrArg (y ∈ ·) habove
    simp only [mem_filter, hy, and_true, eq_iff_iff] at this
    exact this

open Classical in
/-- The times at which some digit wraps (at offset `r`, digits `ω`, bits `ξ`). -/
noncomputable def wrapTimes (K P r : ℕ) (ω : Fin P → ℕ) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    Finset ℕ :=
  (Ico 1 T).filter fun t => ∃ g ∈ shown T hx h₀ r ξ (t - 1), ∃ i : Fin P,
    topRank (shown T hx h₀ r ξ (t - 1)) g = i ∧
      (globalCount T hx (flr h₀ r g) (t - 1) + ω i) / K ≠ (globalCount T hx (flr h₀ r g) t + ω i) / K

/-- **The cut state edges.** The descents of the label number at most the event times plus the wrap
times. -/
theorem card_descents_le {K P r : ℕ} (hr : r < h₀) (ω : Fin P → ℕ)
    (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    (descentsOf (labelOf T hx h₀ K P r ω ξ) T).card ≤
      (eventTimes T hx (h₀ := h₀) r).card + (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card := by
  classical
  refine (card_le_card fun t ht => ?_).trans (card_union_le _ _)
  obtain ⟨hI, hcut⟩ := mem_filter.mp ht
  have hle : t - 1 ≤ t := Nat.sub_le t 1
  rcases shown_ne_or_wrap (fun g _ => globalCount_mono T hx hle) hcut with hne | hw
  · refine mem_union_left _ ?_
    by_contra hnot
    exact hne (shown_eq_of_not_eventTime T hx hr ξ hI hnot)
  · refine mem_union_right _ ?_
    simp only [wrapTimes, mem_filter]
    exact ⟨hI, hw⟩

/-- The event times number at most the rises and last-stint ends of all heads. -/
theorem card_eventTimes_le (r : ℕ) :
    (eventTimes T hx (h₀ := h₀) r).card ≤ ∑ w, ((rises (headFrames T hx w) h₀ r T).card +
      (lastStints (headFrames T hx w) h₀ r T).card) := by
  classical
  calc (eventTimes T hx (h₀ := h₀) r).card
      ≤ (univ.biUnion fun w => ((rises (headFrames T hx w) h₀ r T) ∪
          (lastStints (headFrames T hx w) h₀ r T)).image Prod.fst).card := by
        refine card_le_card fun t ht => ?_
        simp only [eventTimes, mem_filter] at ht
        obtain ⟨hI, w, g, hg, hg1, h⟩ := ht
        obtain ⟨ht1, htT⟩ := mem_Ico.mp hI
        refine mem_biUnion.mpr ⟨w, mem_univ _, mem_image.mpr ⟨(t, g), ?_, rfl⟩⟩
        rcases h with h | h
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr htT, hg⟩, h⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr htT, hg⟩, ht1, h⟩)
    _ ≤ ∑ w, (((rises (headFrames T hx w) h₀ r T) ∪
          (lastStints (headFrames T hx w) h₀ r T)).image Prod.fst).card := card_biUnion_le
    _ ≤ _ := sum_le_sum fun w _ => card_image_le.trans (card_union_le _ _)

/-- Over a set of values, the fibers of a finite set number at most its size. -/
theorem sum_card_fiber_le {α : Type*} (A : Finset α) (f : α → ℕ) (S : Finset ℕ) :
    ∑ t ∈ S, (A.filter (f · = t)).card ≤ A.card := by
  rw [sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

/-- A counter increases at `t` by at most the number of events at `t`. -/
theorem globalCount_sub_le (θ : ℕ) {t : ℕ} :
    globalCount T hx θ t - globalCount T hx θ (t - 1) ≤
      ∑ w, (((turnsOf (headFrames T hx w)).filter (· = t)).card +
        ((segStarts (headFrames T hx w)).filter (·.2 = t)).card) := by
  classical
  have hle : t - 1 ≤ t := Nat.sub_le t 1
  have hw : ∀ w, eventCount (headFrames T hx w) θ t ≤ eventCount (headFrames T hx w) θ (t - 1) +
      (((turnsOf (headFrames T hx w)).filter (· = t)).card +
        ((segStarts (headFrames T hx w)).filter (·.2 = t)).card) := fun w => by
    have h1 := turnCount_sub (S := headFrames T hx w) (θ := θ) hle
    have h2 := segEventCount_sub (S := headFrames T hx w) (θ := θ) hle
    have h3 : ((turnsOf (headFrames T hx w)).filter fun s => t - 1 < s ∧ s ≤ t ∧
        θ ≤ band (prom (headFrames T hx w).x (headFrames T hx w).T s)).card ≤
        ((turnsOf (headFrames T hx w)).filter (· = t)).card :=
      card_le_card (monotone_filter_right _ fun s _ hs => by omega)
    have h4 : ((segStarts (headFrames T hx w)).filter fun Fs => t - 1 < Fs.2 ∧ Fs.2 ≤ t ∧
        θ ≤ segScale (headFrames T hx w) Fs.1 Fs.2).card ≤
        ((segStarts (headFrames T hx w)).filter (·.2 = t)).card :=
      card_le_card (monotone_filter_right _ fun Fs _ hs => by omega)
    unfold eventCount
    omega
  unfold globalCount
  have := sum_le_sum fun w (_ : w ∈ univ) => hw w
  rw [sum_add_distrib] at this
  omega

/-- **The wrap times, over the digit offsets.** They total at most `P K^{P−1}` times the number of
events of all heads. -/
theorem sum_card_wrapTimes_le {K P r : ℕ} (hK : 0 < K) (ξ : EntryIdx (headFrames T hx) → Fin Q) :
    ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K), (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card ≤
      P * K ^ (P - 1) * ∑ w, ((turnsOf (headFrames T hx w)).card +
        (segStarts (headFrames T hx w)).card) := by
  classical
  let E : ℕ → ℕ := fun t => ∑ w, (((turnsOf (headFrames T hx w)).filter (· = t)).card +
    ((segStarts (headFrames T hx w)).filter (·.2 = t)).card)
  have hper : ∀ t ∈ Ico 1 T, ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
      ∃ g ∈ shown T hx h₀ r ξ (t - 1), ∃ i : Fin P, topRank (shown T hx h₀ r ξ (t - 1)) g = i ∧
        (globalCount T hx (flr h₀ r g) (t - 1) + ω i) / K ≠
          (globalCount T hx (flr h₀ r g) t + ω i) / K).card ≤ P * K ^ (P - 1) * E t := by
    intro t ht
    have ht1 := (mem_Ico.mp ht).1
    have hB : ((shown T hx h₀ r ξ (t - 1)).filter (topRank (shown T hx h₀ r ξ (t - 1)) · < P)).card
        ≤ P := by
      refine (card_le_card_of_injOn (topRank (shown T hx h₀ r ξ (t - 1))) (fun g hg => ?_)
        fun a ha b hb h => topRank_injOn _ (mem_filter.mp (mem_coe.mp ha)).1
          (mem_filter.mp (mem_coe.mp hb)).1 h).trans (card_range P).le
      exact mem_coe.mpr (mem_range.mpr (mem_filter.mp hg).2)
    have hwrap := card_wrap_le_sum (P := P) hK (shown T hx h₀ r ξ (t - 1))
      ((shown T hx h₀ r ξ (t - 1)).filter (topRank (shown T hx h₀ r ξ (t - 1)) · < P))
      (fun g => globalCount T hx (flr h₀ r g) (t - 1)) (fun g => globalCount T hx (flr h₀ r g) t)
      fun g _ => globalCount_mono T hx (Nat.sub_le t 1)
    refine le_trans (card_le_card fun ω hω => ?_) (hwrap.trans ?_)
    · simp only [mem_filter] at hω ⊢
      obtain ⟨hmem, g, hg, i, hi, hw⟩ := hω
      exact ⟨hmem, g, ⟨hg, hi ▸ i.isLt⟩, i, hi, hw⟩
    · calc ∑ g ∈ (shown T hx h₀ r ξ (t - 1)).filter (topRank (shown T hx h₀ r ξ (t - 1)) · < P),
            (globalCount T hx (flr h₀ r g) t - globalCount T hx (flr h₀ r g) (t - 1)) * K ^ (P - 1)
          ≤ ∑ _g ∈ (shown T hx h₀ r ξ (t - 1)).filter (topRank (shown T hx h₀ r ξ (t - 1)) · < P),
            E t * K ^ (P - 1) :=
            sum_le_sum fun g _ => Nat.mul_le_mul_right _ (globalCount_sub_le T hx _)
        _ = ((shown T hx h₀ r ξ (t - 1)).filter (topRank (shown T hx h₀ r ξ (t - 1)) · < P)).card *
            (E t * K ^ (P - 1)) := by rw [sum_const, smul_eq_mul]
        _ ≤ P * (E t * K ^ (P - 1)) := Nat.mul_le_mul_right _ hB
        _ = P * K ^ (P - 1) * E t := by ring
  have hexch : ∑ ω ∈ Fintype.piFinset (fun _ : Fin P => range K),
      (wrapTimes T hx (h₀ := h₀) K P r ω ξ).card =
      ∑ t ∈ Ico 1 T, ((Fintype.piFinset fun _ : Fin P => range K).filter fun ω : Fin P → ℕ =>
        ∃ g ∈ shown T hx h₀ r ξ (t - 1), ∃ i : Fin P, topRank (shown T hx h₀ r ξ (t - 1)) g = i ∧
          (globalCount T hx (flr h₀ r g) (t - 1) + ω i) / K ≠
            (globalCount T hx (flr h₀ r g) t + ω i) / K).card := by
    simp only [wrapTimes, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
  rw [hexch]
  calc _ ≤ ∑ t ∈ Ico 1 T, P * K ^ (P - 1) * E t := sum_le_sum hper
    _ = P * K ^ (P - 1) * ∑ t ∈ Ico 1 T, E t := by rw [mul_sum]
    _ ≤ _ := by
        refine Nat.mul_le_mul_left _ ?_
        show ∑ t ∈ Ico 1 T, ∑ w, (((turnsOf (headFrames T hx w)).filter (· = t)).card +
          ((segStarts (headFrames T hx w)).filter (·.2 = t)).card) ≤ _
        rw [sum_comm]
        refine sum_le_sum fun w _ => ?_
        rw [sum_add_distrib]
        exact Nat.add_le_add (sum_card_fiber_le _ id _)
          (sum_card_fiber_le _ (fun Fs : (ℕ × ℕ) × ℕ => Fs.2) _)

end BoundedStackDepth
