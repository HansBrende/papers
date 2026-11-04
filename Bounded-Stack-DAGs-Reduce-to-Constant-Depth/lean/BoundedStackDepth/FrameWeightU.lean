import BoundedStackDepth.LadderBands
import BoundedStackDepth.FrameWeight

/-!
# Frame weight of class U (Lemma W1, concrete part)

Let `x` be a walk (pauses allowed) and `S = upperFrames x T hx` the frame system of class U. For a
segment `σ = (F, s)` with own times `A = segTimes σ`, the staircase (`sup_add_one_le_card`) bounds
`segMax σ = max_A |x − x s|` by `|A| − 1`. Its two hypotheses are the two halves of Lemma W1:

* **Outermost subframes** (`exists_outer_subframe`): a time of a frame `F` that is not an own time
  of `F` lies in a hanging or descent frame `G` of a top `τ` whose excursion lies directly in `F`
  (`inner τ = F`): the longest frame strictly inside `F` containing it. Own times of `F` lie in
  no such `G` (`free_of_own`), and the end of a nonempty `G` is an own time of `F` if it lies before
  the end of `F` (`own_frame_end`).
* **Steps** (`own_step`): consecutive own times of a frame are at most one level apart. They are
  consecutive times, or the times between them form a frame `G` as above, and they are its ladder
  ends `L (w − 1), L w` or `D w, D (w − 1)` (`x_frame_ends`).
* **Start**: the first own time of a segment is at its home. It is the segment start, unless the
  start `F.1` of `F` is not an own time of `F`; then the outermost subframe at `F.1` is a hanging
  frame `[L (w − 1) + 1, L w)` (a descent frame never starts at `F.1`), the walk is at `w` at both
  of its ends (`x_hangFrame_fst`), and its end is the first own time.

`segMax_add_one_le` is **Lemma W1**; with `sum_segWeight_le` the segment weights of class U sum to at
most `T` (`sum_segWeight_upperFrames_le`). `card_suspendFrames_le`: a top of height `H` has `H − 1`
levels (`card_levels`), hence at most `2 (H − 1)` frames, and there are at most `2T` suspend frames.
-/

namespace BoundedStackDepth

open BoundedNesting Finset

namespace FrameSystem

variable {S : FrameSystem}

/-- The own times of the segment `(F, s)` are the own times of `F` whose segment starts at `s`. -/
theorem mem_segTimes {F : ℕ × ℕ} {s t : ℕ} :
    t ∈ S.segTimes (F, s) ↔ S.Own F t ∧ S.segStart F t = s := by
  unfold segTimes segOf
  rw [mem_filter, mem_range]
  constructor
  · rintro ⟨ht, he⟩
    have h1 : S.inner t = F := congrArg Prod.fst he
    have h2 : S.segStart (S.inner t) t = s := congrArg Prod.snd he
    rw [h1] at h2
    exact ⟨h1 ▸ own_inner ht, h2⟩
  · rintro ⟨hown, hs⟩
    refine ⟨lt_of_lt_of_le hown.2.1.2 (S.bounds F hown.1), ?_⟩
    rw [inner_eq hown, hs]

end FrameSystem

open FrameSystem

variable {x : ℕ → ℤ} {T τ : ℕ} {w : ℤ} {G : ℕ × ℕ}

/-! ### The ends of a frame of level `w` -/

/-- Around a frame of level `w` the walk is at `w − 1` and `w`: just before its start and at its end
are `L (w − 1), L w` (hanging frame) or `D w, D (w − 1)` (descent frame). -/
theorem x_frame_ends (hx : IsWalk x) (hw : w ∈ levels x T τ)
    (hG : G = hangFrame x T τ w ∨ G = descFrame x T τ w) :
    (x (G.1 - 1) = w - 1 ∧ x G.2 = w) ∨ (x (G.1 - 1) = w ∧ x G.2 = w - 1) := by
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  have hc1 : base x T τ ≤ w - 1 := by omega
  have hc2 : w - 1 < x τ := by omega
  rcases hG with rfl | rfl
  · left
    show x (ladL x T τ (w - 1) + 1 - 1) = w - 1 ∧ x (ladL x T τ w) = w
    rw [Nat.add_sub_cancel]
    exact ⟨x_ladL hx hc1 hc2, x_ladL hx hw1.le hw2⟩
  · right
    show x (ladD x T τ w + 1 - 1) = w ∧ x (ladD x T τ (w - 1)) = w - 1
    rw [Nat.add_sub_cancel]
    exact ⟨x_ladD hx hw1.le hw2, x_ladD hx hc1 hc2⟩

/-- A hanging frame of level `w` starts at level `w`: right after `L (w − 1)` the walk steps up. -/
theorem x_hangFrame_fst (hx : IsWalk x) (hw : w ∈ levels x T τ) :
    x (hangFrame x T τ w).1 = w := by
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  have hc1 : base x T τ ≤ w - 1 := by omega
  have hc2 : w - 1 < x τ := by omega
  have hl := (isUpperHop_ladL hx hc1 hc2).long
  have h1 := ladL_above hx hc1 hc2 (t := ladL x T τ (w - 1) + 1) (by omega) (by omega)
  have h2 := (hx.step (ladL x T τ (w - 1))).1
  rw [x_ladL hx hc1 hc2] at h2
  show x (ladL x T τ (w - 1) + 1) = w
  omega

/-! ### Outermost subframes -/

/-- **Outermost subframes.** A time `u` of a frame `F` that is not an own time of `F` lies in a
hanging or descent frame of a top `τ` whose excursion lies directly in `F` (`inner τ = F`). Take the
longest frame `G` strictly inside `F` containing `u`, a frame of some top `τ`: `F` contains the
interior of the excursion of `τ` (else `G` would not be strictly inside `F`), and `inner τ` contains
`G` strictly, so it is not strictly inside `F`. -/
theorem exists_outer_subframe (hx : IsWalk x) {F : ℕ × ℕ} (hF : F ∈ (upperFrames x T hx).frames)
    {u : ℕ} (hu : Contains F u) (hnot : ¬ (upperFrames x T hx).Own F u) :
    ∃ τ ∈ tops x T, (upperFrames x T hx).inner τ = F ∧ ∃ w ∈ levels x T τ, ∃ G : ℕ × ℕ,
      (G = hangFrame x T τ w ∨ G = descFrame x T τ w) ∧ G.1 ≤ u ∧ u < G.2 := by
  classical
  have huT : u < T := lt_of_lt_of_le hu.2 ((upperFrames x T hx).bounds F hF)
  have hin := own_inner (S := upperFrames x T hx) huT
  obtain ⟨G, hGC, hmax⟩ := ((upperFrames x T hx).frames.filter
    (fun G => Contains G u ∧ Within G F ∧ G ≠ F)).exists_max_image (fun G => G.2 - G.1)
    ⟨_, mem_filter.mpr ⟨hin.1, hin.2.1, hin.2.2 F hF hu, fun h => hnot (h ▸ hin)⟩⟩
  obtain ⟨hGf, hGu, hGF, hGne⟩ := mem_filter.mp hGC
  rcases mem_insert.mp hGf with rfl | hGs
  · exact absurd (within_antisymm hGF ⟨Nat.zero_le _, (upperFrames x T hx).bounds F hF⟩) hGne
  obtain ⟨τ, hτ, hGτ⟩ := mem_suspendFrames.mp hGs
  obtain ⟨w, hw, hGw⟩ := mem_framesOf.mp hGτ
  refine ⟨τ, hτ, ?_, w, hw, G, hGw.imp Eq.symm Eq.symm, hGu.1, hGu.2⟩
  have hGb := framesOf_bounds hx hτ hGτ
  have hτG := ladder_time_not_mem_framesOf hx hτ hτ le_rfl le_rfl (Or.inl rfl) hGτ
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  have hu1 := hGu.1
  have hu2 := hGu.2
  have hF1 := hu.1
  have hF2 := hu.2
  -- `F` contains the interior of the excursion of `τ`
  have hFint : F.1 ≤ (exc x T τ).1 + 1 ∧ (exc x T τ).2 ≤ F.2 := by
    rcases frame_cases hx hτ hF with h | h | h | ⟨τ', hτ', h1, h2, hFτ'⟩
    · exact h
    · omega
    · omega
    · exfalso
      by_cases hne : τ = τ'
      · subst hne
        rcases framesOf_disjoint hx hFτ' hGτ with he | he | he
        · exact hGne he.symm
        · omega
        · omega
      · obtain ⟨H, hH, hH1, hH2⟩ := exists_framesOf_nested hx hτ hτ' hne h1 h2
        have hFb := framesOf_bounds hx hτ' hFτ'
        rcases framesOf_disjoint hx hH hGτ with he | he | he
        · subst he
          exact hGne (within_antisymm hGF ⟨by omega, by omega⟩)
        · omega
        · omega
  have hown := own_inner_top hx hτ
  have hIb := inner_top_bounds hx hτ
  have hW : Within ((upperFrames x T hx).inner τ) F := hown.2.2 F hF ⟨by omega, by omega⟩
  by_contra hneq
  have hlen := hmax _ (mem_filter.mpr ⟨hown.1, ⟨by omega, by omega⟩, hW, hneq⟩)
  omega

/-- **Ends of subframes.** The end of a nonempty frame `G` of `τ` is an own time of the frame of the
excursion of `τ` if it lies before the end of that frame. It is a free ladder time `L w` or
`D (w − 1)` strictly inside the excursion, or the end `b` of the excursion; the walk steps down into
`b`, so no frame starts at `b` and the innermost frame at `b` is that of the excursion
(`inner_exc_snd`). -/
theorem own_frame_end (hx : IsWalk x) (hτ : τ ∈ tops x T) (hw : w ∈ levels x T τ)
    (hG : G = hangFrame x T τ w ∨ G = descFrame x T τ w) (hne : G.1 < G.2)
    (hlt : G.2 < ((upperFrames x T hx).inner τ).2) :
    (upperFrames x T hx).Own ((upperFrames x T hx).inner τ) G.2 := by
  obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
  have hc1 : base x T τ ≤ w - 1 := by omega
  have hc2 : w - 1 < x τ := by omega
  have ha := exc_fst_lt hx hτ
  have hb := lt_exc_snd hx hτ
  rcases hG with rfl | rfl
  · -- the hanging frame ends at the free ladder time `L w`
    have h1 := (ladL_lt_ladL hx le_rfl hw1 hw2).1
    have h2 := ladL_lt hx hw1.le hw2
    show (upperFrames x T hx).Own _ (ladL x T τ w)
    exact own_of_free hx hτ h1 (by omega) (free_ladL hx hτ hw1.le hw2)
  · change ladD x T τ w + 1 < ladD x T τ (w - 1) at hne
    change ladD x T τ (w - 1) < _ at hlt
    show (upperFrames x T hx).Own _ (ladD x T τ (w - 1))
    have h1 := lt_ladD hx hc1 hc2
    rcases eq_or_lt_of_le hc1 with he | he
    · -- the descent frame at the lowest level ends at the end `b` of the excursion
      rw [← he] at hne hlt ⊢
      rw [← exc_snd] at hne hlt ⊢
      have hbT := exc_snd_lt hx hτ
      rcases inner_exc_snd hx hτ hlt with h | h
      · rw [← h]
        exact own_inner hbT
      · exfalso
        have hin := own_inner (S := upperFrames x T hx) hbT
        have hDw := lt_ladD hx hw1.le hw2
        have hxb : x (exc x T τ).2 = base x T τ := x_ladD hx le_rfl (base_lt hτ)
        have hdown := base_lt_of_mem hx hτ (t := (exc x T τ).2 - 1) (by omega) (by omega)
        rcases mem_insert.mp hin.1 with hroot | hHs
        · rw [hroot] at h
          simp only at h
          omega
        obtain ⟨τ'', -, hHτ''⟩ := mem_suspendFrames.mp hHs
        obtain ⟨w'', hw'', hHw''⟩ := mem_framesOf.mp hHτ''
        obtain ⟨hlev, -, hpred, -⟩ := frameAt_walk hx hw'' (hHw''.imp Eq.symm Eq.symm)
        have e1 := hlev (exc x T τ).2 h.le hin.2.1.2
        rw [h] at hpred
        omega
    · -- the descent frame ends at the free ladder time `D (w − 1)` inside the excursion
      exact own_of_free hx hτ (by omega) (ladL_lt_ladL hx le_rfl he hc2).2
        (free_ladD hx hτ hc1 hc2)

/-! ### Steps along own times -/

/-- **Steps along own times.** Consecutive own times `t' < t` of a frame `F` are at most one level
apart: `t = t' + 1`, or the times in between form a frame `[t' + 1, t)` of a top whose excursion
lies directly in `F`, and `t', t` are the ladder times `L (w − 1), L w` or `D w, D (w − 1)` around
it. -/
theorem own_step (hx : IsWalk x) {F : ℕ × ℕ} {t' t : ℕ} (h't : (upperFrames x T hx).Own F t')
    (ht : (upperFrames x T hx).Own F t) (hlt : t' < t)
    (hgap : ∀ u, t' < u → u < t → ¬ (upperFrames x T hx).Own F u) :
    x t ≤ x t' + 1 ∧ x t' ≤ x t + 1 := by
  rcases Nat.lt_or_ge (t' + 1) t with h | h
  · have hF1 := h't.2.1.1
    have hF2 := ht.2.1.2
    obtain ⟨τ, hτ, hFτ, w, hw, G, hG, hG1, hG2⟩ :=
      exists_outer_subframe hx h't.1 ⟨by omega, by omega⟩ (hgap _ (by omega) h)
    subst hFτ
    have hGτ := frameAt_mem hw hG
    have hf' := free_of_own hx hτ h't τ hτ le_rfl le_rfl G hGτ
    have hf := free_of_own hx hτ ht τ hτ le_rfl le_rfl G hGτ
    have hG1' : G.1 = t' + 1 := by
      by_contra hne
      exact hf' ⟨by omega, by omega⟩
    have hG2' : G.2 ≤ t := by
      by_contra hne
      exact hf ⟨by omega, by omega⟩
    have hend := own_frame_end hx hτ hw hG (by omega) (by omega)
    have hGt : G.2 = t := by
      by_contra hne
      exact hgap _ (by omega) (by omega) hend
    have hends := x_frame_ends hx hw hG
    rw [hG1', Nat.add_sub_cancel, hGt] at hends
    omega
  · obtain rfl : t = t' + 1 := by omega
    exact hx.step t'

/-! ### Lemma W1 -/

/-- **Lemma W1 (frame weight), concrete part.** The maximum of every segment of class U is less than
its number of own times: the first own time is at the home, and each later one is at most one level
from the previous one (the staircase). -/
theorem segMax_add_one_le (hx : IsWalk x) :
    ∀ σ ∈ (upperFrames x T hx).segments,
      (upperFrames x T hx).segMax σ + 1 ≤ ((upperFrames x T hx).segTimes σ).card := by
  rintro ⟨F, s⟩ hσ
  have hA : ((upperFrames x T hx).segTimes (F, s)).Nonempty := by
    obtain ⟨t, ht, he⟩ := mem_image.mp hσ
    exact ⟨t, mem_filter.mpr ⟨ht, he⟩⟩
  refine sup_add_one_le_card (fun t => (x t - x s).natAbs) hA ?_ ?_
  · -- the first own time is at the home
    have hmem := min'_mem _ hA
    have hmin : ∀ t, (upperFrames x T hx).Own F t → (upperFrames x T hx).segStart F t = s →
        ((upperFrames x T hx).segTimes (F, s)).min' hA ≤ t :=
      fun t h1 h2 => min'_le _ _ (mem_segTimes.mpr ⟨h1, h2⟩)
    generalize ((upperFrames x T hx).segTimes (F, s)).min' hA = t₀ at hmem hmin ⊢
    obtain ⟨hown₀, hs₀⟩ := mem_segTimes.mp hmem
    suffices h : x t₀ = x s by
      show (x t₀ - x s).natAbs = 0
      rw [h, sub_self, Int.natAbs_zero]
    have h2 := hown₀.2.1.1
    have h3 := hown₀.2.1.2
    rcases segStart_mem (S := upperFrames x T hx) F t₀ with h | h <;> rw [hs₀] at h
    · -- the segment starts at the start of `F`
      subst h
      by_cases hF1 : (upperFrames x T hx).Own F F.1
      · have := hmin F.1 hF1 (segStart_start _ F)
        rw [show t₀ = F.1 by omega]
      -- `F.1` lies in a hanging frame `G` of a top of `F`, and the first own time is its end
      obtain ⟨τ, hτ, hFτ, w, hw, G, hG, hG1, hG2⟩ :=
        exists_outer_subframe hx hown₀.1 ⟨le_rfl, by omega⟩ hF1
      subst hFτ
      have hGτ := frameAt_mem hw hG
      have hGb := framesOf_bounds hx hτ hGτ
      have hIb := inner_top_bounds hx hτ
      have hG1' : G.1 = ((upperFrames x T hx).inner τ).1 := by omega
      have hf := free_of_own hx hτ hown₀ τ hτ le_rfl le_rfl G hGτ
      have hG2' : G.2 ≤ t₀ := by
        by_contra hne
        exact hf ⟨by omega, by omega⟩
      have hend := own_frame_end hx hτ hw hG (by omega) (by omega)
      have hseg : (upperFrames x T hx).segStart ((upperFrames x T hx).inner τ) G.2 =
          ((upperFrames x T hx).inner τ).1 :=
        le_antisymm ((segStart_mono hG2').trans hs₀.le) (start_le_segStart _ _)
      have hle := hmin G.2 hend hseg
      obtain ⟨hw1, hw2⟩ := mem_levels.mp hw
      rcases hG with rfl | rfl
      · rw [show t₀ = (hangFrame x T τ w).2 by omega, ← hG1', x_hangFrame_fst hx hw]
        exact x_ladL hx hw1.le hw2
      · -- a descent frame cannot start at `F.1`: `D w` lies strictly inside the excursion
        exfalso
        have := lt_ladD hx hw1.le hw2
        have := exc_fst_lt hx hτ
        change ladD x T τ w + 1 = _ at hG1'
        omega
    · -- the segment starts at a restart of `F`, an own time
      have := hmin s h.2.2.2 (segStart_of_restart ⟨h.1, h.2.1, h.2.2.2⟩)
      rw [show t₀ = s by omega]
  · -- each later own time is at most one level from the previous one
    intro t ht hne
    obtain ⟨hown, hst⟩ := mem_segTimes.mp ht
    obtain ⟨t', ht'B, hmax⟩ :=
      (((upperFrames x T hx).segTimes (F, s)).filter (· < t)).exists_max_image id
        ⟨_, mem_filter.mpr ⟨min'_mem _ hA, lt_of_le_of_ne (min'_le _ _ ht) (Ne.symm hne)⟩⟩
    obtain ⟨ht'A, ht't⟩ := mem_filter.mp ht'B
    obtain ⟨hown', hst'⟩ := mem_segTimes.mp ht'A
    refine ⟨t', ht'A, ht't, ?_⟩
    have hgap : ∀ u, t' < u → u < t → ¬ (upperFrames x T hx).Own F u := by
      intro u h1 h2 hu
      have hsu : (upperFrames x T hx).segStart F u = s :=
        le_antisymm ((segStart_mono h2.le).trans hst.le) (hst'.symm.le.trans (segStart_mono h1.le))
      have := hmax u (mem_filter.mpr ⟨mem_segTimes.mpr ⟨hu, hsu⟩, h2⟩)
      simp only [id] at this
      omega
    have := own_step hx hown' hown ht't hgap
    show (x t - x s).natAbs ≤ (x t' - x s).natAbs + 1
    omega

/-- **Lemma W1, segments.** The weights `2 ^ band segMax` of the segments of class U sum to at most
`T`. -/
theorem sum_segWeight_upperFrames_le (hx : IsWalk x) :
    ∑ σ ∈ (upperFrames x T hx).segments, 2 ^ band ((upperFrames x T hx).segMax σ) ≤ T :=
  (upperFrames x T hx).sum_segWeight_le (segMax_add_one_le hx)

/-- A top of height `H` has `H − 1` levels. -/
theorem card_levels (x : ℕ → ℤ) (T τ : ℕ) : (levels x T τ).card = height x T τ - 1 := by
  rw [levels, Int.card_Ioo, base]
  omega

/-- A top of height `H` has at most `2 (H − 1)` frames. -/
theorem card_framesOf_le (x : ℕ → ℤ) (T τ : ℕ) : (framesOf x T τ).card ≤ 2 * (height x T τ - 1) :=
  calc (framesOf x T τ).card
      ≤ ((levels x T τ).image (hangFrame x T τ)).card +
          ((levels x T τ).image (descFrame x T τ)).card := card_union_le _ _
    _ ≤ (levels x T τ).card + (levels x T τ).card := add_le_add card_image_le card_image_le
    _ = 2 * (height x T τ - 1) := by rw [card_levels]; ring

/-- **Lemma W1, suspend frames.** There are at most `2T` suspend frames: a top of height `H` has at
most `2 (H − 1)` of them, and the heights add up to the number of upper hops, at most `T`. -/
theorem card_suspendFrames_le (hx : IsWalk x) : (suspendFrames x T).card ≤ 2 * T :=
  calc (suspendFrames x T).card
      ≤ ∑ τ ∈ tops x T, (framesOf x T τ).card := by
        rw [suspendFrames_eq_biUnion]
        exact card_biUnion_le
    _ ≤ ∑ τ ∈ tops x T, 2 * height x T τ :=
        sum_le_sum fun τ _ => (card_framesOf_le x T τ).trans (by omega)
    _ = 2 * (upperHops x T).card := by rw [← mul_sum, sum_height_eq]
    _ ≤ 2 * T := by
        have := card_upperHops_add_card_tops_le hx T
        omega

end BoundedStackDepth
